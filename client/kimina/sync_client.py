import logging
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from difflib import get_close_matches
from typing import Any

import httpx
from colorama import Style
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

logger = logging.getLogger("kimina")


def b(text: str) -> str:
    return f"{Style.BRIGHT}{text}{Style.RESET_ALL}"


class Kimina(BaseKimina):
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
        self.session = httpx.Client(headers=self.headers, timeout=self.http_timeout)

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
                    desc=f"Batches",
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
        @retry(
            stop=stop_after_attempt(self.n_retries),
            wait=wait_exponential(multiplier=1, min=1, max=10),
            before_sleep=before_sleep_log(logger, logging.ERROR),
        )
        def run_method():
            try:
                if method.upper() == "POST":
                    response = self.session.post(url, json=payload)
                elif method.upper() == "GET":
                    response = self.session.get(url, params=payload)
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

    def health(self) -> None:
        url = self.build_url("/health")
        resp = self._query(url, method="GET")
        return resp  # TODO: create status object to cast automaticalllly

    def test(self):
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

    def find_id_column(self, columns: list[str]) -> str | tuple[str, str]:
        if "id" in columns:
            return "id"

        preferred_names = ["uuid", "proof_id", "problem_id"]

        match = get_close_matches("id", columns, n=1, cutoff=0.6)
        if not match:
            for name in preferred_names:
                match = get_close_matches(name, columns, n=1, cutoff=0.6)
                if match:
                    break
        selected_column = match[0] if match else None
        logger.info("Available columns:")
        for i, col in enumerate(columns):
            logger.info(f"{i}: {col}")

        user_input = input("Select column index/name or type 'concat': ").strip()
        if user_input.lower() == "concat":
            idxs = input("Enter two column indices to concatenate (e.g. 0 1): ")
            idx1, idx2 = map(int, idxs.split())
            return (columns[idx1], columns[idx2])
        if not user_input and selected_column:
            return selected_column
        if user_input.isdigit() and 0 <= int(user_input) < len(columns):
            return columns[int(user_input)]
        if user_input not in columns:
            raise ValueError(f"Invalid column: {user_input}")

        return user_input

    def find_code_column(self, columns: list[str]) -> str:
        if "code" in columns:
            return "code"

        preferred_names = ["code", "proof", "full_proof"]

        match = get_close_matches("code", columns, n=1, cutoff=0.6)
        if not match:
            for name in preferred_names:
                match = get_close_matches(name, columns, n=1, cutoff=0.6)
                if match:
                    break
        selected_column = match[0] if match else None
        logger.info("Available columns:")
        for i, col in enumerate(columns):
            logger.info(f"{i}: {col}")

        user_input = input("Select column index/name: ").strip()
        if not user_input and selected_column:
            return selected_column
        if user_input.isdigit() and 0 <= int(user_input) < len(columns):
            return columns[int(user_input)]
        if user_input not in columns:
            raise ValueError(f"Invalid column: {user_input}")

        return user_input

    def build_log(self, dataset_name: str, n: int, batch_size: int) -> str:
        final_log = f"Running benchmark on {Style.BRIGHT}{dataset_name}{Style.RESET_ALL}: # Snippets = {b(str(n))} | Batches = "

        n_full_batches = n // batch_size

        if n_full_batches == 0:
            final_log += f"[{b(str(n))}]"
        else:
            if n_full_batches == 1:
                final_log += f"[{b(str(batch_size))}]"
            else:
                final_log += f"{b(str(n_full_batches))} x [{b(str(batch_size))}]"
            if n % batch_size > 0:
                final_log += f" + [{b(str(n % batch_size))}]"
        return final_log

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
        # TODO: add option for uuid as metadata in the check call + output dir.
        # TODO: add option output dir with file hierarchy based on metadata like uuid in the run_benchmark method
        # TODO: add count heartbeats option

        if n <= 0:
            logger.error("Please specify n > 0")
            return

        if batch_size <= 0:
            logger.warning("Cannot use batch size = %d, defaulting to 8", batch_size)
            batch_size = 8

        logger.info(self.build_log(dataset_name, n, batch_size))

        builder = load_dataset_builder(dataset_name)
        if not builder.info.features:
            logger.error("Dataset has no features, cannot run benchmark")
            return

        columns: list[str] = list(builder.info.features)

        if dataset_name == "Goedel-LM/Lean-workbook-proofs":
            id_column_name = "problem_id"
            code_column_name = "full_proof"
        elif dataset_name == "AI-MO/math-test-inference-results":
            id_column_name = ("uuid", "proof_id")
            code_column_name = "proof"
        else:
            id_column_name = self.find_id_column(columns)
            code_column_name = self.find_code_column(columns)

        dataset = load_dataset(dataset_name, split=split + f"[:{n}]")

        def get_id(sample: Any, id_column_name: str | tuple[str, str]):
            if isinstance(id_column_name, tuple):
                a, b = id_column_name
                return str(sample[a]) + "_" + str(sample[b])
            return str(sample[id_column_name])

        snips = [
            Snippet(
                id=str(get_id(sample, id_column_name)), code=sample[code_column_name]
            )
            for sample in dataset
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

    def close(self):
        self.session.close()
