import logging
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from typing import Any

import httpx
from datasets import load_dataset, load_dataset_builder  # type: ignore
from tenacity import (
    RetryError,
    before_sleep_log,
    retry,
    stop_after_attempt,
    wait_exponential,
)
from tqdm import tqdm

from .base import BaseKimina
from .models import CheckRequest, CheckResponse, Infotree, ReplResponse, Snippet
from .utils import build_log, find_code_column, find_id_column

logger = logging.getLogger("kimina-client")


class KiminaClient(BaseKimina):
    def __init__(
        self,
        api_url: str | None = None,
        api_key: str | None = None,
        headers: dict[str, str] | None = None,
        http_timeout: int = 600,
        n_retries: int = 3,
    ):
        super().__init__(
            api_url=api_url,
            api_key=api_key,
            headers=headers,
            http_timeout=http_timeout,
            n_retries=n_retries,
        )

    def check(
        self,
        snips: str | list[str] | Snippet | list[Snippet],
        timeout: int = 60,
        debug: bool = False,
        reuse: bool = True,
        infotree: Infotree | None = None,
        batch_size: int = 8,
        max_workers: int = 5,
        show_progress: bool = True,
    ) -> CheckResponse:
        if isinstance(snips, str):
            snips = [snips]
        elif isinstance(snips, Snippet):
            snips = [snips]

        snippets = [Snippet.from_snip(snip) for snip in snips]
        batches = [
            snippets[i : i + batch_size] for i in range(0, len(snippets), batch_size)
        ]
        results: list[CheckResponse] = []
        with ThreadPoolExecutor(max_workers=max_workers) as executor:
            # TODO: not thread-safe because reusing the same httpx.Client..., create a new one for each call to api_check
            futures = {
                executor.submit(
                    self.api_check, batch, timeout, debug, reuse, infotree, True
                ): batch
                for batch in batches
            }
            iterator = (
                tqdm(
                    as_completed(futures),
                    total=len(futures),
                    desc="Batches",
                    bar_format="{desc}: {percentage:3.0f}%|{bar}| {n_fmt}/{total_fmt} [elapsed: {elapsed}, remaining: {remaining}]",
                )
                if show_progress
                else as_completed(futures)
            )
            for future in iterator:
                results.append(future.result())
        return CheckResponse.merge(results)

    def api_check(
        self,
        snippets: list[Snippet],
        timeout: int = 30,
        debug: bool = False,
        reuse: bool = True,
        infotree: Infotree | None = None,
        safe: bool = False,
    ) -> CheckResponse:
        """
        Makes a POST request to /api/check with provided arguments.

        Returns a `CheckResponse`.
        """
        try:
            url = self.build_url("/api/check")

            payload = CheckRequest(
                snippets=snippets,
                timeout=timeout,
                debug=debug,
                reuse=reuse,
                infotree=infotree,
            ).model_dump()

            resp = self._query(url, payload)
            return self.handle(resp, CheckResponse)
        except Exception as e:
            if safe:
                return CheckResponse(
                    results=[
                        ReplResponse(id=snip.id, error=str(e)) for snip in snippets
                    ],
                )
            raise e

    def _query(
        self, url: str, payload: dict[str, Any] | None = None, method: str = "POST"
    ) -> Any:
        """
        Sends a `method` request to `url` with `payload` as body/params.
        A new `httpx.Client` is created for each request for thread-safety.
        Use AsyncClient for more efficient concurrent requests (TCP connection reuse/pooling).
        """

        @retry(
            stop=stop_after_attempt(self.n_retries),
            wait=wait_exponential(multiplier=1, min=1, max=10),
            before_sleep=before_sleep_log(logger, logging.ERROR),
        )
        def run_method() -> Any:
            try:
                with httpx.Client(
                    headers=self.headers, timeout=self.http_timeout
                ) as client:
                    if method.upper() == "POST":
                        response = client.post(url, json=payload)
                    elif method.upper() == "GET":
                        response = client.get(url, params=payload)
                    else:
                        raise ValueError(f"Unsupported method: {method}")
                    response.raise_for_status()  # Ensure 2xx, otherwise retry
            except httpx.HTTPError as e:
                logger.error(f"Error posting to {url}: {e}")
                raise e

            try:
                return response.json()  # Ensure JSON, otherwise retry
            except ValueError:
                logger.error(f"Server returned non-JSON: {response.text}")
                raise ValueError("Invalid response from server: not a valid JSON")

        try:
            return run_method()
        except RetryError:
            raise RuntimeError(f"Request failed after {self.n_retries} retries")

    def health(self) -> Any:
        """
        Checks server's healthy.
        """
        url = self.build_url("/health")
        resp = self._query(url, method="GET")
        return resp  # TODO: create status object to cast automatically

    def test(self) -> None:
        """
        Tests with `#check Nat`.
        """
        logger.info("Testing with `#check Nat`...")
        response = self.check("#check Nat", show_progress=False).results[0].response
        assert response is not None, "Response should not be None"
        assert response.get("messages", None) == [
            {
                "severity": "info",
                "pos": {"line": 1, "column": 0},
                "endPos": {"line": 1, "column": 6},
                "data": "Nat : Type",
            }
        ]
        logger.info("Test passed!")

    def run_benchmark(
        self,
        dataset_name: str = "Goedel-LM/Lean-workbook-proofs",
        split: str = "train",
        n: int = 100,
        batch_size: int = 8,
        max_workers: int = 5,
        timeout: int = 60,
        reuse: bool = True,
        show_progress: bool = True,
    ) -> None:
        """
        Runs benchmark on Hugging Face dataset.
        Displays results in the console.
        """
        # TODO: add option output dir with file hierarchy based on metadata like uuid in the run_benchmark method
        # TODO: add count heartbeats option

        if n <= 0:
            logger.error("Please specify n > 0")
            return

        if batch_size <= 0:
            logger.warning("Cannot use batch size = %d, defaulting to 8", batch_size)
            batch_size = 8

        logger.info(build_log(dataset_name, n, batch_size))

        builder = load_dataset_builder(dataset_name)
        if not builder.info.features:
            logger.error("Dataset has no features, cannot run benchmark")
            return

        columns: list[str] = list(builder.info.features)

        id_column_name: str | tuple[str, str] = "id"
        code_column_name: str = "code"
        if dataset_name == "Goedel-LM/Lean-workbook-proofs":
            id_column_name = "problem_id"
            code_column_name = "full_proof"
        elif dataset_name == "AI-MO/math-test-inference-results":
            id_column_name = ("uuid", "proof_id")
            code_column_name = "proof"
        else:
            id_column_name = find_id_column(columns)
            code_column_name = find_code_column(columns)

        dataset = load_dataset(dataset_name, split=split + f"[:{n}]")

        def get_id(sample: Any, id_column_name: str | tuple[str, str]) -> str:
            if isinstance(id_column_name, tuple):
                a, b = id_column_name
                return str(sample[a]) + "_" + str(sample[b])
            return str(sample[id_column_name])

        snips = [
            Snippet(
                id=str(get_id(sample, id_column_name)),
                code=sample[code_column_name],  # type: ignore
            )
            for sample in dataset  # type: ignore
        ]

        start_time = time.time()
        check_response = self.check(
            snips=snips,
            timeout=timeout,
            reuse=reuse,
            batch_size=batch_size,
            max_workers=max_workers,
            show_progress=show_progress,
        )
        elapsed_time = time.time() - start_time

        check_response.analyze(elapsed_time)
