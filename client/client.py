import asyncio
import logging
import os
from urllib.parse import urljoin, urlparse, urlunparse
from typing import List

import aiohttp
from loguru import logger
from tenacity import (
    RetryError,
    before_sleep_log,
    retry,
    stop_after_attempt,
    wait_exponential,
)

from tqdm.asyncio import tqdm_asyncio


class Lean4Client(object):
    """Client for interacting with the Lean 4 verification server.

    This client handles communication with a Lean 4 server for verifying proofs
    and retrieving results. It handles authentication, connection testing,
    and provides methods for synchronous and asynchronous verification.
    """

    def __init__(self, base_url, api_key=None, disable_cache=False) -> None:
        """Initialize the Lean4Client.

        Args:
            base_url (str): Base URL of the Lean 4 server.
            api_key (str, optional): API key for authentication. If None, will try
                to load from LEANSERVER_API_KEY environment variable. Defaults to None.
            disable_cache (bool, optional): Whether to disable result and header caching. Defaults to False.

        Raises:
            Exception: If the Lean server cannot be connected to or is unavailable.
        """
        self.url = base_url
        if api_key is None:
            api_key = os.getenv("LEANSERVER_API_KEY")

        self.api_key = api_key
        self.disable_cache = disable_cache

        self._test_connection()

    def verify(self, codes, timeout, infotree_type=None):
        """Synchronous wrapper for verifying proof codes.

        This is a convenience method that wraps the async_verify method
        in an asyncio event loop for synchronous usage.

        Args:
            codes (list): The list of Lean 4 code to verify.
                Each code is a dict containing:
                    - code: The Lean 4 code to verify.
                    - custom_id: The custom id of the proof.
            timeout (int): The timeout in seconds.
            infotree_type (str, optional): Type of info tree to use. Defaults to None.

        Returns:
            dict: The response from the server with verification results.
        """
        return asyncio.run(self.async_verify(codes, timeout, infotree_type))

    async def async_verify(self, codes, timeout, infotree_type=None):
        """verify the proof code and get result

        Args:
            codes (list): The list of lena 4 code to verify.
                Each code is a dict of:
                    - code: The lena 4 code to verify.
                    - custom_id: The custom id of the proof.
            timeout (int): The timeout in seconds.

        Returns:
            response (dict): The response from the server.
                It contains a  key results, which is a list of dictionaries.
                Each dictionary contains the following keys:
                    - code: The custom id of the proof.
                    - error: A string with the error message from the lean server.
                    - response: A dictionary with the response from the LEAN REPL.

        Example:
            >>> client.one_pass_verify("import Mathlib\n\nexample : 2 = 2 := rfl", timeout=60)
            {'results': [{'code': 'test_connection', 'error': None, 'response': {'env': 0}}]}
        """
        json_data = {
            "codes": codes,
            "timeout": timeout,
            "infotree_type": infotree_type,
            "disable_cache": self.disable_cache,
        }
        response = await self._query("post", "/verify", json_data)
        return response

    async def _query(
        self,
        method: str,
        endpoint: str,
        json_data: dict | None = None,
        n_retries: int = 3,
    ) -> dict:
        """
        One single method for sending all requests, with retry behavior controlled by the caller.

        Args:
            method: The HTTP method to use (e.g., "get", "post").
            endpoint: The endpoint to call.
            json_data: The data to send in the request.
            n_retries: Number of retry attempts.

        Returns:
            response: The response from the server.
        """

        # Create retry decorator with dynamic n_retries
        @retry(
            stop=stop_after_attempt(
                n_retries
            ),  # Dynamic retries based on the caller's argument
            wait=wait_exponential(multiplier=1, min=1, max=10),  # Exponential backoff
            before_sleep=before_sleep_log(
                logger, logging.ERROR
            ),  # Optional logging of each retry
        )
        async def query_with_retries(url):
            headers = {
                "Content-Type": "application/json",
                "Accept": "application/json",
                "Authorization": f"Bearer {self.api_key}",
            }

            # Create a session with trust_env set to True
            async with aiohttp.ClientSession(
                trust_env=True, timeout=aiohttp.ClientTimeout(total=3600)
            ) as session:
                async with session.request(
                    method,
                    self._ensure_url_has_scheme(str(urljoin(url, endpoint))),
                    headers=headers,
                    json=json_data,  # Directly send the JSON data
                ) as response:
                    # Get the response body asynchronously and parse it as JSON
                    res = await response.json()

            return res

        # Call the query function with retries
        return await query_with_retries(self.url)

    def _ensure_url_has_scheme(self, url, default_scheme="http"):
        """Ensure URL has a scheme (http/https) prefix.

        Args:
            url (str): The URL to check and potentially modify.
            default_scheme (str, optional): The scheme to add if none exists. Defaults to "http".

        Returns:
            str: URL with a scheme.
        """
        parsed = urlparse(url)
        if not parsed.scheme:
            parsed = urlparse(f"{default_scheme}://{url}")
        return urlunparse(parsed)

    def _test_connection(self):
        """Test the connection to the Lean server.

        Sends a simple GET request to the root endpoint to verify
        that the server is available and responsive.

        Raises:
            Exception: If the server cannot be connected to or returns a non-ok status.

        Returns:
            bool: True if connection test passed.
        """
        try:
            response = asyncio.run(self._query("get", "/"))
        except RetryError:
            raise Exception(f"The lean server {self.url} cannot be connected.")

        if response.get("status") != "ok":
            raise Exception(
                f"The lean server {self.url} cannot be available. {response}"
            )


async def process_batch(batch, client: Lean4Client, timeout, infotree_type, semaphore):
    """Process a single batch of proofs with the Lean4 client.

    Args:
        batch (List[dict]): A batch of proof samples to verify.
        client (Lean4Client): The Lean4 client instance.
        timeout (int): Timeout in seconds for verification.
        infotree_type (str, optional): Type of info tree to use.
        semaphore (asyncio.Semaphore): Semaphore to limit concurrent executions.

    Returns:
        dict: The verification response from the Lean4 client.
    """
    async with semaphore:
        response = await client.async_verify(
            batch, timeout=timeout, infotree_type=infotree_type
        )
        return response


async def process_batches(
    client,
    batches: List[List[dict]],
    timeout=60,
    num_proc=os.cpu_count(),
    infotree_type=None,
):
    """Process multiple batches of proofs concurrently.

    Args:
        client (Lean4Client): The Lean4 client instance.
        batches (List[List[dict]]): List of batches, where each batch is a list of samples.
        timeout (int, optional): Timeout in seconds for each batch. Defaults to 60.
        num_proc (int, optional): Maximum number of concurrent processes. Defaults to CPU count.
        infotree_type (str, optional): Type of info tree to use. Defaults to None.

    Returns:
        List[dict]: Combined results from all batches.
    """
    semaphore = asyncio.Semaphore(num_proc)

    results = []

    coros = [
        process_batch(batche, client, timeout, infotree_type, semaphore)
        for batche in batches
    ]

    for fut in tqdm_asyncio.as_completed(
        coros, total=len(batches), desc="Verifying proofs"
    ):
        result = await fut
        results.extend(result["results"])

    return results


def batch_verify_proof(
    client,
    samples: List[dict],
    timeout=60,
    num_proc=os.cpu_count(),
    batch_size=8,
    infotree_type=None,
):
    """Verify multiple proofs in batches using the Lean4 server.

    Args:
        client (Lean4Client): The Lean4 client instance to use for verification.
        samples (List[dict]): List of samples to verify. Each sample must be a dictionary
            containing at least:
            - custom_id (str): A unique identifier for the sample.
            - proof (str): The Lean4 proof code to verify.
        timeout (int, optional): Timeout in seconds for each batch. Defaults to 60.
        num_proc (int, optional): Number of concurrent processes. Defaults to CPU count.
        batch_size (int, optional): Number of samples in each batch. Defaults to 8.
        infotree_type (str, optional): Type of info tree to use. Defaults to None.

    Returns:
        List[dict]: List of verification results. Each result contains:
            - custom_id: The custom ID of the sample.
            - error: Error message if verification failed, None otherwise.
            - response: The response from the Lean server.

    Raises:
        AssertionError: If custom_id values are not unique across all samples.

    Note:
        Each sample in the input list must have both 'custom_id' and 'proof' keys.
        The 'custom_id' values must be unique across all samples.
    """
    custom_ids = [sample["custom_id"] for sample in samples]
    assert len(custom_ids) == len(set(custom_ids)), "Custom id must be unique"

    logger.info(
        f"Processing {len(samples)} samples in {len(samples)/batch_size} batches of size {batch_size}"
    )

    batches = [samples[i : i + batch_size] for i in range(0, len(samples), batch_size)]

    results = asyncio.run(
        process_batches(
            client,
            batches,
            timeout=timeout,
            num_proc=num_proc,
            infotree_type=infotree_type,
        )
    )

    return results
