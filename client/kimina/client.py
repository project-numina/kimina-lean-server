import os
import sys
from typing import Optional
from uuid import uuid4

import requests
from loguru import logger

from .models import CheckRequest, CheckResponse, Infotree, Snippet

logger.remove()
logger.add(sys.stderr, level="INFO", colorize=True, format="<level>{message}</level>")


class Kimina:

    def __init__(
        self,
        api_url: str = "https://lean.projectnumina.ai",
        api_key: Optional[str] = None,
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

        self._test_connection()

    def _test_connection(self):
        headers = {"Content-Type": "application/json"}
        if self.api_key:
            headers["Authorization"] = f"Bearer {self.api_key}"

        resp = requests.get(f"{self.url}/health", headers=headers)

        resp.raise_for_status()

        resp = resp.json()
        if resp["status"] != "ok":
            raise Exception(f"The lean server {self.url} cannot be available: {resp}")

        logger.info(f"Connected to Lean server at {self.url}")
