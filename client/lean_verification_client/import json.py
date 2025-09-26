import json
import multiprocessing as mp
import time
import pandas as pd
from datasets import load_dataset
from loguru import logger
from tqdm import tqdm

from autoformalizer.eval_utils import lean_feedback


async def verify_one_batch(client, timeout, working_dir, infotree_type, samples):
    """
        - samples (list): A list of samples to verify in one batch
            samples must contain the following keys:
                - proof: The proof code to verify
                - proof_id: The proof id
                - uuid: The uuid of the problem
        - timeout (int): The timeout in seconds for the entire batch
        - working_dir (Path): Working directory for saving verification results

    Returns:
        - list: List of processed samples with verification results
    """
    # Prepare batch input format
    batch_codes = []
    for sample in samples:
        batch_codes.append(
            {"code": sample["proof"], "custom_id": str(sample["proof_id"])}
        )
    id_to_sample = {str(sample["proof_id"]): sample for sample in samples}

    # Perform batch verification
    start_time = time.time()
    if working_dir:
        # Create directory structure for results
        for sample in samples:
            uuid_dir = working_dir / sample["uuid"]
            uuid_dir.mkdir(parents=True, exist_ok=True)

        # check if all file path exist
        all_file_path = [
            working_dir / sample["uuid"] / f"{sample['proof_id']}.json"
            for sample in samples
        ]
    if working_dir and all([file_path.exists() for file_path in all_file_path]):
        # all files exist, load reponse
        response = []
        for file_path in all_file_path:
            with open(file_path, "r") as f:
                try:
                    data = json.load(f)
                except json.JSONDecodeError:
                    data = {"error": "JSONDecodeError"}
                if "code" not in data:
                    data["code"] = file_path.stem
                response.append(data)
    else:
        response = await client.async_one_pass_verify_batch(
            batch_codes, timeout=timeout, infotree_type=infotree_type
        )
        response = response.get("results", [])
    elapsed_time = time.time() - start_time

    # Process results
    if len(response) != len(samples):
        logger.error(
            f"""Time: {elapsed_time:.2f}s, Batch verification failed:
            Expected {len(samples)} results, got {len(response)}"""
        )
        # return samples with default values
        results = []
        for sample in samples:
            new_sample = sample.copy()
            new_sample.update(
                {
                    "lean_feedback": json.dumps(
                        {"error": "Missing response from server"}
                    ),
                    "has_error": True,
                    "is_valid_no_sorry": False,
                    "is_valid_with_sorry": False,
                }
            )
            results.append(new_sample)
        return results

    results = []
    for individual_response in response:
        if individual_response.get("error") is not None:
            # ignore timeout error
            if "Lean process timed out" not in individual_response["error"]:
                logger.warning(
                    f"Time: {elapsed_time:.2f}s, Sample in batch failed: {individual_response['error']}"
                )
        elif individual_response.get("response") is None:
            logger.warning(
                f"Time: {elapsed_time:.2f}s, Sample in batch failed: No response found"
            )

        proof_id = (
            individual_response["custom_id"]
            if "custom_id" in individual_response
            else individual_response["code"]
        )
        sample = id_to_sample.get(proof_id).copy()
        filepath = (
            working_dir / sample["uuid"] / f"{proof_id}.json" if working_dir else None
        )
        if working_dir and (not filepath.exists()):
            with open(filepath, "w") as f:
                json.dump(individual_response, f)

        output = lean_feedback.parse_client_response(individual_response)
        sample.update(
            {
                "lean_feedback": json.dumps(individual_response),
                "has_error": output["has_error"],
                "is_valid_no_sorry": output["is_valid_no_sorry"],
                "is_valid_with_sorry": output["is_valid_with_sorry"],
            }
        )
        results.append(sample)

    return results


# TODO: no count heartbeats yet
async def thread_worker(
    batch_queue, result_queue, client, timeout, working_dir, infotree_type
):
    results = await verify_one_batch(
        client, timeout, working_dir, infotree_type, batch
    )
    except Exception as e:
        logger.error(
            f"Batch verification failed for batch {str(batch)[:50]} with error: {e}"
        )
        results = []
        for sample in batch:
            new_sample = sample.copy()
            new_sample.update(
                {
                    "lean_feedback": json.dumps({"error": str(e)}),
                    "has_error": True,
                    "is_valid_no_sorry": False,
                    "is_valid_with_sorry": False,
                }
            )
            results.append(new_sample)
    result_queue.put(results)

def batch_verify_proof(
    client,
    samples,
    timeout=60,
    num_threads=20,
    batch_size=8,
    working_dir=None,
    infotree_type=None,
    disable_tqdm=False,
    count_heartbeats=False,
):
    """
        - samples (list): List of samples to verify.
            Must contain the following keys:
                - proof_id: The proof id
                - uuid: The uuid of the problem
                - proof: The formal proof to verify
        - working_dir (Path): Working directory for saving verification results
            if None, no cache is applied

    Returns:
        - list: List of all processed samples with verification results
            Each sample contains the following:
                - proof_id: The proof id
                - uuid: The uuid of the problem
                - proof: The formal proof
                - lean_feedback: A JSON string with the response from the server
                - has_error: A boolean indicating if the proof has an error
                - is_valid_no_sorry: A boolean indicating if the proof is valid
                    without any "sorry" statements.
                    This is the output from lean_feedback.parse_client_response.
                - is_valid_with_sorry: A boolean indicating if the proof is valid
                    with "sorry" statements. Use to check formal_statement.
                    This is the output from lean_feedback.parse_client_response.
                - heartbeats: count of heartbeats for all theorems

    """

    # assert proof id is unique
    proof_ids = [sample["proof_id"] for sample in samples_copy]
    assert len(proof_ids) == len(set(proof_ids)), "Proof id must be unique"

    manager = mp.Manager()
    batch_queue = manager.Queue()
    result_queue = manager.Queue()
    [batch_queue.put(batch) for batch in batches]

    all_results = []
    
    # count heartbeats
    for data in all_results:
        tot_heartbeats = extract_all_heartbeats_lean_output(data)
        data["heartbeats"] = tot_heartbeats

    return all_results



def example_batch(client):
    dataset = load_dataset("AI-MO/math-test-inference-results", split="train")
    working_dir = None
    # select the first 500 uuids
    dataset = dataset.select(range(100 * 64))
    print(dataset)

    # make sure we have proof_id, uuid, and proof
    new_samples = []
    for sample in tqdm(dataset):
        new_samples.append(
            {
                # for this dataset, proof_id is not unique, unfortunately
                "proof_id": sample["uuid"] + "_" + str(sample["proof_id"]),
                "uuid": sample["uuid"],
                "proof": sample["proof"],
            }
        )

    # create batch and use one_pass_verify_batch
    batch_size = 1
    results = batch_verify_proof(
        client=client,
        samples=new_samples,
        timeout=60,
        num_threads=200,
        batch_size=batch_size,
        working_dir=working_dir,
        count_heartbeats=True,
    )
    # print(len(results))
    # print(results[0])

    # calculate valid rate and other stats
    df = []
    for data in results:
        uuid = data["uuid"]
        name = data["proof_id"]
        response = json.loads(data["lean_feedback"])
        error_message = response.get("error", None)
        df.append(
            {
                "uuid": uuid,
                "is_valid_no_sorry": data["is_valid_no_sorry"],
                "name": name,
                "has_connection_error": bool(error_message),
                "heartbeats": data["heartbeats"],
            }
        )
    df = pd.DataFrame(df)
    print(df)

    # calculate valid rate
    valid_rate = df["is_valid_no_sorry"].sum() / len(df)
    print(f"valid rate: {valid_rate}")

    # connection error rate
    connection_error_rate = df["has_connection_error"].sum() / len(df)
    print(f"connection error rate: {connection_error_rate}")

    # calculate valid rate for each uuid using groupby
    uuid_group = df.groupby("uuid")["is_valid_no_sorry"].sum()

    # find all uuids with at least one valid proof
    valid_uuids = uuid_group[uuid_group > 0].index
    print(f"Number of uuids: {len(uuid_group)}")
    print(f"Number of uuids with at least one valid proof: {len(valid_uuids)}")
    if len(valid_uuids) == 52:
        logger.info("Example batch test passed!")
    else:
        logger.error("Example batch test failed!")
        raise ValueError("Example batch test failed!")


# Not used anywhere, let's convert it to a sanity check against the server (test connection++)
def test_single_proof(client):
    """
    Tests a single proof with the Lean4 client.

    Args:
        client (Lean4Client): The client to use for verification.
        proof (str): The proof code to verify.

    Returns:
        dict: The response from the server.
    """
    proof = """import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

set_option maxHeartbeats 0

/-- The volume of a cone is given by the formula $V = \frac{1}{3}Bh$,
where $B$ is the area of the base and $h$ is the height. The area of the base of a cone is 30 square units,
and its height is 6.5 units. What is the number of cubic units in its volume? Show that it is 65.-/
theorem mathd_algebra_478 (b h v : ℝ) (h₀ : 0 < b ∧ 0 < h ∧ 0 < v) (h₁ : v = 1 / 3 * (b * h))
    (h₂ : b = 30) (h₃ : h = 13 / 2) : v = 65 := by
  -- Start with the formula for the volume of the cone
  rw [h₁, h₂, h₃] -- Substitute the values for b and h
  -- Simplify the expression: V = (1/3) * 30 * (13/2)
  norm_num
"""

    code = {
        "uuid": "aaa",
        "proof_id": "aaa_0",
        "proof": proof,
    }
    samples = [code]
    res = batch_verify_proof(
        client, samples=samples, timeout=15, num_threads=3, count_heartbeats=True
    )
    logger.info(f"code sample after verify :\n{samples[0]['proof']}")

    return res


if __name__ == "__main__":
    """
    python -m autoformalizer.clients.lean4_client
    Example batch should display something like

    ==========================Output==========================
        valid rate: 0.32890625
        connection error rate: 0.0
        Number of uuids: 100
        Number of uuids with at least one valid proof: 52
    """
    client = Lean4Client()

    if test_connection(client):
        logger.info("Connection successful!")
    else:
        logger.error("Connection failed!")

    output = test_single_proof(client)
    print(output[0]["lean_feedback"])
    if output[0]["is_valid_no_sorry"]:
        logger.info("Proof is valid!")
        heartbeats = extract_first_heartbeats_lean_output(output[0])
        logger.info(f"heartbeats : {heartbeats}")
    else:
        logger.error("Proof is invalid!")

    # example_batch(client)