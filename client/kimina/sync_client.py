import logging
from typing import Any

import httpx
from httpx import Response
from tenacity import before_sleep_log, retry, stop_after_attempt, wait_exponential

from .base import BaseKimina
from .models import CheckRequest, CheckResponse, Infotree, Snippet

logger = logging.getLogger(__name__)


class KiminaClient(BaseKimina):
    def __init__(
        self,
        api_url: str | None = None,
        api_key: str | None = None,
        headers: dict[str, str] | None = None,
        http_timeout: int = 60,
    ):
        super().__init__(
            api_url=api_url,
            api_key=api_key,
            headers=headers,
            http_timeout=http_timeout,
        )
        self.session = httpx.Client(headers=self.headers, timeout=self.http_timeout)

    def check(
        self,
        snips: str | list[str] | Snippet | list[Snippet],
        timeout: int = 60,
        debug: bool = False,
        reuse: bool = True,
        infotree: Infotree | None = None,
    ) -> CheckResponse:
        if isinstance(snips, str):
            snips = [snips]
        elif isinstance(snips, Snippet):
            snips = [snips]

        snippets = [Snippet.from_snip(snip) for snip in snips]

        return self.api_check(snippets, timeout, debug, reuse, infotree)

    def api_check(
        self,
        snippets: list[Snippet],
        timeout: int = 30,
        debug: bool = False,
        reuse: bool = True,
        infotree: Infotree | None = None,
    ) -> CheckResponse:
        url = self.build_url("/api/check")

        payload = CheckRequest(
            snippets=snippets,
            timeout=timeout,
            debug=debug,
            reuse=reuse,
            infotree=infotree,
        ).model_dump()

        resp = self.query(url, payload)
        return self.handle(resp, CheckResponse)

    def query(self, url: str, payload: dict[str, Any]) -> Response:
        @retry(
            stop=stop_after_attempt(self.n_retries),
            wait=wait_exponential(multiplier=1, min=1, max=10),
            before_sleep=before_sleep_log(logger, logging.ERROR),
        )
        def post():
            return self.session.post(url, json=payload)

        return post()

    def close(self):
        self.session.close()
