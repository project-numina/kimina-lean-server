# import asyncio
# import logging
# import os
# from urllib.parse import urljoin, urlparse, urlunparse
# from typing import List

# import aiohttp
# from loguru import logger


# from tqdm.asyncio import tqdm_asyncio


# async def process_batch(batch, client: Lean4Client, timeout, infotree_type, semaphore):
#     """Process a single batch of proofs with the Lean4 client.

#     Args:
#         batch (List[dict]): A batch of proof samples to verify.
#         client (Lean4Client): The Lean4 client instance.
#         timeout (int): Timeout in seconds for verification.
#         infotree_type (str, optional): Type of info tree to use.
#         semaphore (asyncio.Semaphore): Semaphore to limit concurrent executions.

#     Returns:
#         dict: The verification response from the Lean4 client.
#     """
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
#     """Process multiple batches of proofs concurrently.

#     Args:
#         client (Lean4Client): The Lean4 client instance.
#         batches (List[List[dict]]): List of batches, where each batch is a list of samples.
#         timeout (int, optional): Timeout in seconds for each batch. Defaults to 60.
#         num_proc (int, optional): Maximum number of concurrent processes. Defaults to CPU count.
#         infotree_type (str, optional): Type of info tree to use. Defaults to None.

#     Returns:
#         List[dict]: Combined results from all batches.
#     """
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
#     """Verify multiple proofs in batches using the Lean4 server.

#     Args:
#         client (Lean4Client): The Lean4 client instance to use for verification.
#         samples (List[dict]): List of samples to verify. Each sample must be a dictionary
#             containing at least:
#             - custom_id (str): A unique identifier for the sample.
#             - proof (str): The Lean4 proof code to verify.
#         timeout (int, optional): Timeout in seconds for each batch. Defaults to 60.
#         num_proc (int, optional): Number of concurrent processes. Defaults to CPU count.
#         batch_size (int, optional): Number of samples in each batch. Defaults to 8.
#         infotree_type (str, optional): Type of info tree to use. Defaults to None.

#     Returns:
#         List[dict]: List of verification results. Each result contains:
#             - custom_id: The custom ID of the sample.
#             - error: Error message if verification failed, None otherwise.
#             - response: The response from the Lean server.

#     Raises:
#         AssertionError: If custom_id values are not unique across all samples.

#     Note:
#         Each sample in the input list must have both 'custom_id' and 'proof' keys.
#         The 'custom_id' values must be unique across all samples.
#     """
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
