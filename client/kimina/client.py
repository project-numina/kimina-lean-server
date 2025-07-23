import logging
import os
import sys
from typing import Any
from urllib.parse import urljoin, urlparse, urlunparse
from uuid import uuid4

import aiohttp
import requests
from loguru import logger
from tenacity import retry  # RetryError,
from tenacity import before_sleep_log, stop_after_attempt, wait_exponential

from .models import CheckRequest, CheckResponse, Code, Infotree, Snippet, VerifyResponse

logger.remove()
logger.add(sys.stderr, level="INFO", colorize=True, format="<level>{message}</level>")

loggsies = logging.Logger("kimina.client")


class Kimina:

    def __init__(
        self,
        api_url: str = "https://lean.projectnumina.ai",
        api_key: str | None = None,
        reuse: bool = True,
    ):
        self.api_url = api_url.rstrip("/")
        self.api_key = api_key
        self.reuse = reuse

    def check(
        self,
        snippet: Snippet | str,
        *,
        timeout: int = 20,
        debug: bool = False,
        reuse: bool | None = None,
        infotree: Infotree | None = None,
    ) -> CheckResponse:
        if isinstance(snippet, str):
            snippet = Snippet(id=uuid4().hex, code=snippet)

        req = CheckRequest(
            snippet=snippet,
            timeout=timeout,
            debug=debug,
            reuse=(
                reuse if reuse is not None else self.reuse
            ),  # Use request reuse param, otherwise use client reuse param
            infotree=infotree,
        )
        headers = {"Content-Type": "application/json"}
        if self.api_key:
            headers["Authorization"] = f"Bearer {self.api_key}"
        resp = requests.post(
            f"{self.api_url}/api/check", json=req.model_dump(), headers=headers
        )
        resp.raise_for_status()
        return CheckResponse.model_validate(resp.json())

    def _test_connection(self):
        headers = {"Content-Type": "application/json"}
        if self.api_key:
            headers["Authorization"] = f"Bearer {self.api_key}"

        resp = requests.get(f"{self.api_url}/health", headers=headers)

        resp.raise_for_status()

        resp = resp.json()
        if resp["status"] != "ok":
            raise Exception(
                f"The lean server {self.api_url} cannot be available: {resp}"
            )

        logger.info(f"Connected to Lean server at {self.api_url}")


class Lean4Client(Kimina):
    """
    DEPRECATED: use `Kimina` instead.
    """

    def __init__(
        self,
        base_url: str = "https://lean.projectnumina.ai",
        api_key: str | None = None,
        disable_cache: bool = False,
    ):
        logger.warning("Lean4Client is deprecated; please use Kimina instead")
        if api_key is None:
            api_key = os.getenv("LEAN_SERVER_API_KEY") or os.getenv(
                "LEANSERVER_API_KEY"
            )

        super().__init__(base_url, api_key, reuse=(not disable_cache))

        self.url = base_url

        self._old_test_connection()

    def _old_test_connection(self):
        headers = {"Content-Type": "application/json"}
        if self.api_key:
            headers["Authorization"] = f"Bearer {self.api_key}"

        resp = requests.get(f"{self.url}", headers=headers)

        resp.raise_for_status()

        resp = resp.json()
        if resp["status"] != "ok":
            raise Exception(f"The lean server {self.url} cannot be available: {resp}")

        logger.info(f"Connected to Lean server at {self.url}")

    # async def async_version(self, param: str) -> str:
    #     return await make_async(self.sync_version)(param)

    def verify(
        self,
        codes: list[Code],
        timeout: int,
        infotree_type: Infotree | None = None,
    ) -> VerifyResponse:
        payload = {
            "codes": codes,
            "timeout": timeout,
            "infotree_type": infotree_type,
            "disable_cache": not self.reuse,
        }
        resp = self._sync_query("post", "/verify", json=payload)
        return VerifyResponse.model_validate(resp.json())

    @retry(
        stop=stop_after_attempt(3),
        wait=wait_exponential(multiplier=1, min=1, max=10),
        before_sleep=before_sleep_log(loggsies, logging.ERROR),
    )
    def _sync_query(
        self, method: str, endpoint: str, **request_kwargs: Any
    ) -> requests.Response:
        headers = {
            "Content-Type": "application/json",
            "Accept": "application/json",
            "Authorization": f"Bearer {self.api_key}",
        }
        url = f"{self.api_url}{endpoint}"
        with requests.Session() as session:
            session.trust_env = True
            response = session.request(
                method, url, headers=headers, timeout=3600, **request_kwargs
            )
        response.raise_for_status()
        return response

    async def async_verify(
        self, codes: list[Code], timeout: int, infotree_type: Infotree | None = None
    ) -> VerifyResponse:
        json_data: Any = {
            "codes": codes,
            "timeout": timeout,
            "infotree_type": infotree_type,
            "disable_cache": not self.reuse,
        }
        response = await self._query("post", "/verify", json_data)
        return VerifyResponse.model_validate(response)

    async def _query(
        self,
        method: str,
        endpoint: str,
        json_data: Any | None = None,
        n_retries: int = 3,
    ) -> Any:

        @retry(
            stop=stop_after_attempt(n_retries),
            wait=wait_exponential(multiplier=1, min=1, max=10),
            before_sleep=before_sleep_log(loggsies, logging.ERROR),
        )
        async def query_with_retries(
            method: str, endpoint: str, json_data: Any | None = None
        ) -> Any:
            headers = {
                "Content-Type": "application/json",
                "Accept": "application/json",
                "Authorization": f"Bearer {self.api_key}",
            }

            # trust_env=True to use HTTP_PROXY and HTTPS_PROXY
            async with aiohttp.ClientSession(
                trust_env=True, timeout=aiohttp.ClientTimeout(total=3600)
            ) as session:
                value = str(urljoin(self.api_url, endpoint))
                print(value)
                async with session.request(
                    method,
                    value,
                    headers=headers,
                    json=json_data,
                ) as response:
                    res = await response.json()

            return res

        return await query_with_retries(method, endpoint, json_data)

    def _ensure_url_has_scheme(self, default_scheme: str = "https"):
        parsed = urlparse(self.api_url)
        if not parsed.scheme:
            parsed = urlparse(f"{default_scheme}://{self.api_url}")
        return urlunparse(parsed)
