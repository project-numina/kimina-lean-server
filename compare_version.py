import json
import os
import datasets

from client.client import Lean4Client, batch_verify_proof


def deep_sort_json_keys(obj):
    if isinstance(obj, dict):
        return {k: deep_sort_json_keys(obj[k]) for k in sorted(obj.keys())}
    elif isinstance(obj, list):
        return [deep_sort_json_keys(elem) for elem in obj]
    else:
        return obj


def increment_line_values(d):
    """
    Recursively check if the key in a dictionary or list is 'line'.
    If it is a 'line' key in the dictionary and its value is an integer, then increase the integer value by 1.
    If it is a list, then recursively process each element in the list.

    Args:
    d (dict or list or any): The dictionary, list or any other type to check.

    Returns:
    dict or list or any: The updated structure.
    """
    if isinstance(d, dict):
        new_dict = {}
        for key, value in d.items():
            if key == "line" and isinstance(value, int):
                new_dict[key] = value + 1
            elif isinstance(value, (dict, list)):
                new_dict[key] = increment_line_values(value)
            else:
                new_dict[key] = value
        return new_dict
    elif isinstance(d, list):
        new_list = []
        for item in d:
            if isinstance(item, (dict, list)):
                new_list.append(increment_line_values(item))
            else:
                new_list.append(item)
        return new_list
    else:
        return d


if __name__ == "__main__":
    ds = datasets.load_dataset("AI-MO/lean-result-test-sample-2k", split="train")

    timeout = 60
    batch_size = 1
    num_proc = os.cpu_count() or 16

    url = "http://127.0.0.1:12332"

    client = Lean4Client(base_url=url, disable_cache=False)

    samples = [
        {"custom_id": sample["custom_id"], "proof": sample["proof"]} for sample in ds
    ]

    result = batch_verify_proof(
        samples=samples,
        client=client,
        timeout=timeout,
        num_proc=num_proc,
        batch_size=batch_size,
    )

    origin_ds_id_map = {row["custom_id"]: row for row in ds}

    not_same_samples = []

    for sample_result in result:
        custom_id = sample_result["custom_id"]

        origin_row = origin_ds_id_map[custom_id]
        origin_result_response = json.loads(origin_row["response"])
        origin_result_messages = (
            origin_result_response.get("messages", None)
            if origin_result_response
            else None
        )

        current_result_response = sample_result["response"]
        current_result_messages = (
            current_result_response.get("messages", None)
            if current_result_response
            else None
        )

        origin_result_messages_str = json.dumps(
            deep_sort_json_keys(origin_result_messages)
        )

        current_result_messages_str = json.dumps(
            deep_sort_json_keys(increment_line_values(current_result_messages))
        )

        if origin_result_messages_str != current_result_messages_str:
            not_same_samples.append(
                {
                    "custom_id": custom_id,
                    "origin_messages": origin_result_messages_str,
                    "current_messages": current_result_messages_str,
                }
            )

    print(
        f"The same total {len(ds) - len(not_same_samples)}, datasets size is {len(ds)}"
    )

    for not_same_sample in not_same_samples:
        print("=================================")
        print(not_same_sample["custom_id"])
        print("---------------------------------")
        print("origin:")
        print(not_same_sample["origin_messages"])
        print("---------------------------------")
        print("current:")
        print(not_same_sample["current_messages"])
        print("---------------------------------")
