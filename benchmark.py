import os

from loguru import logger
from datasets import load_dataset

from client.client import Lean4Client, batch_verify_proof
from utils.proof_utils import analyze


def benchmark_api(client, n: int, timeout: int, batch_size: int, num_proc: int):
    """Benchmark the Lean4 verification API by testing it on a dataset of proofs.

    This function loads proof samples from the Goedel-LM/Lean-workbook-proofs dataset,
    verifies them using the Lean4 client, and analyzes the results.

    Args:
        client (Lean4Client): The client instance used to connect to the Lean4 server.
        n (int): Number of samples to test from the dataset.
        timeout (int): Maximum time in seconds allowed for each verification.
        batch_size (int): Number of samples to process in each batch.
        num_proc (int): Number of concurrent processes to use for verification.

    Returns:
        None: Results are printed to stdout by the analyze function.
    """
    dataset = load_dataset("AI-MO/math-test-inference-results", split="train")
    # dataset = dataset.select(range(n))

    samples = [
        {"custom_id": str(sample["problem_id"]) + "_" + str(i), "proof": sample["proof"]}
        for i, sample in enumerate(dataset)
    ]

    result = batch_verify_proof(
        samples=samples,
        client=client,
        timeout=timeout,
        num_proc=num_proc,
        batch_size=batch_size,
    )

    analyze(result)


if __name__ == "__main__":
    n = 100
    timeout = 240
    batch_size = 8
    num_proc = 64
    url = "your_url"

    logger.info("Testing cached mode")

    # Test cached mode
    client = Lean4Client(base_url=url, disable_cache=False)

    benchmark_api(client, n, timeout, batch_size, num_proc)

    logger.info("Testing non-cached mode")

    # Test non-cached mode
    client = Lean4Client(base_url=url, disable_cache=True)

    benchmark_api(client, n, timeout, batch_size, num_proc)
