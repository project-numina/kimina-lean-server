from __future__ import annotations

import asyncio
import json
from pprint import pformat
from statistics import mean
from typing import cast

import pytest
from asgi_lifespan import LifespanManager
from datasets import load_dataset
from httpx import ASGITransport, AsyncClient
from kimina_client import CheckRequest, ReplResponse, Snippet
from loguru import logger

from server.main import app
from server.settings import settings


@pytest.mark.perfs
@pytest.mark.asyncio  # TODO: Parametrize
async def test_goedel(perf_rows: int, perf_shuffle: bool) -> None:
    ds = load_dataset(
        "Goedel-LM/Lean-workbook-proofs", split="train"
    )  # Goedel is on v4.9.0, some proofs aren't valid in later versions.
    if perf_shuffle:
        ds = ds.shuffle(seed=0)
    if perf_rows:
        ds = ds.select(range(perf_rows))

    logger.info(f"Checking {len(ds)} proofs")
    times: list[float] = []

    # TODO: Create real perf tests not using ASGI transport (with actual network)
    # limits = Limits(max_connections=settings.MAX_REPLS, max_keepalive_connections=5)
    async with LifespanManager(app, startup_timeout=60):
        async with AsyncClient(
            transport=ASGITransport(app=app),
            base_url="http://testserver/api",
            # limits=limits,
        ) as client:
            logger.debug(
                f"MAX_REPLS: {settings.max_repls}\nMAX_REPL_USES: {settings.max_repl_uses}"
            )
            semaphore = asyncio.Semaphore(
                settings.max_repls
            )  # limit concurrent requests don't use this semaphore just llilmit in async client

            async def run_item(item: dict[str, str]) -> ReplResponse:
                async with semaphore:
                    proof = item["full_proof"]
                    payload = CheckRequest(
                        snippets=[Snippet(id=item["problem_id"], code=proof)],
                        timeout=30,
                    ).model_dump()
                    resp = await client.post("check", json=payload)
                    assert resp.status_code == 200
                    data = resp.json()["results"][0]
                    logger.info(json.dumps(data, indent=2))
                    assert "time" in data
                    times.append(float(data["time"]))
                    return cast(ReplResponse, data)

            tasks = [
                asyncio.create_task(run_item(item))
                for item in ds
                if item["problem_id"]
                not in [
                    "lean_workbook_10036",
                    "lean_workbook_10012",  # Unknown identifier: div_le_div_iff (disappeared in v4.26.0)
                ]  # skip this one, it's too long
            ]

            all_results = await asyncio.gather(*tasks)
            for idx, result in enumerate(all_results):
                assert "response" in result, f"response #{idx} missing 'response' key"
                if settings.lean_version == "v4.26.0":
                    assert "messages" not in result["response"] or not any(
                        msg["severity"] == "error"
                        for msg in result["response"]["messages"]
                    ), (
                        f"Proof #{idx} contains errors : {pformat(result['response']['messages'])}"
                    )
                else:
                    assert "messages" in result["response"]
                    assert any(
                        msg["data"] == "Goals accomplished!"
                        for msg in result["response"]["messages"]
                    ), (
                        f"Proof #{idx} did not accomplish goals: {pformat(result['response']['messages'])}"
                    )
    logger.info(
        f"min: {min(times):.2f} s, max: {max(times):.2f} s and mean: {mean(times):.2f} s"
    )
    assert mean(times) < 10, (
        "Mean time for proofs should be less than 10 seconds"
    )  # max repls = 5
