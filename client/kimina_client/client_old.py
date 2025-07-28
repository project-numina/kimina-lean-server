# # import asyncio
# # import logging
# # import os
# # from urllib.parse import urljoin, urlparse, urlunparse
# # from typing import List

# # import aiohttp
# # from loguru import logger


# # from tqdm.asyncio import tqdm_asyncio


# async def process_batch(batch, client: Lean4Client, timeout, infotree_type, semaphore):
#     async with semaphore:
#         response = await client.async_verify(
#             batch, timeout=timeout, infotree_type=infotree_type
#         )
#         return response


# async def process_batches(
#     client,
#     batches: List[List[dict]],
#     timeout=60,
#     num_proc=os.cpu_count(),
#     infotree_type=None,
# ):
#     semaphore = asyncio.Semaphore(num_proc)

#     results = []

#     coros = [
#         process_batch(batche, client, timeout, infotree_type, semaphore)
#         for batche in batches
#     ]

#     for fut in tqdm_asyncio.as_completed(
#         coros, total=len(batches), desc="Verifying proofs"
#     ):
#         result = await fut
#         results.extend(result["results"])

#     return results


# def batch_verify_proof(
#     client,
#     samples: List[dict],
#     timeout=60,
#     num_proc=os.cpu_count(),
#     batch_size=8,
#     infotree_type=None,
# ):
#     custom_ids = [sample["custom_id"] for sample in samples]
#     assert len(custom_ids) == len(set(custom_ids)), "Custom id must be unique"

#     logger.info(
#         f"Processing {len(samples)} samples in {len(samples)/batch_size} batches of size {batch_size}"
#     )

#     batches = [samples[i : i + batch_size] for i in range(0, len(samples), batch_size)]

#     results = asyncio.run(
#         process_batches(
#             client,
#             batches,
#             timeout=timeout,
#             num_proc=num_proc,
#             infotree_type=infotree_type,
#         )
#     )

#     return results
