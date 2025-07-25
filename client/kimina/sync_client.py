import logging
from concurrent.futures import ThreadPoolExecutor, as_completed
from typing import Any

import httpx
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

logger = logging.getLogger(__name__)


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
                tqdm(as_completed(futures), total=len(futures))
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

    def close(self):
        self.session.close()
