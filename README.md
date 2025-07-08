# Kimina Lean Server

This project serves the [Lean REPL](https://github.com/leanprover-community/repl) using FastAPI.
It supports massive parallelization to verify Lean 4 proofs at scale.

📄 Technical report: [Technical Report](./Technical_Report.pdf)

## ✨ Features

- High-throughput Lean4 proof verification
- FastAPI-based async server with configurable concurrency
- REPL pooling and context caching for performance

## 📦 Setup

Clone this repository and change directory:

```sh
git clone git@github.com:project-numina/kimina-lean-server.git
cd kimina-lean-server
```

### Containerized - Docker

You can build the Docker image with (add `--build-arg LEAN_VERSION=v4.18.0` if you don't want the default `v4.15.0` Lean version):

```sh
cp .env.template .env
docker compose up -d
```

Test it works with a request:

```sh
curl --request POST \
  --url http://localhost/verify \
  --header 'Content-Type: application/json' \
  --data '{
    "codes": [
	  {
		"custom_id": "1234",
		"proof": "#check Nat"
	  }
    ],
    "infotree_type": "original"
}' | jq
```

To shut down the container / view logs:

```sh
docker compose down
docker compose logs -f
```

### Direct installation

First, install elan — the Lean version manager: [reference](https://github.com/leanprover/elan).

After installing elan, make sure that `elan --version` works correctly.
(`lake --version` should also work after elan is properly installed.)

Install dependencies:

```sh
pip install -e .
```

Set Up the Lean Environment:

```sh
bash setup.sh
```

This script installs Lean 4 and builds `mathlib4` and `repl` in the current working directory.

Start the FastAPI server:

```sh
cp .env.template .env
python -m server
```

Once running, the server exposes a FastAPI application for LeanREPL interaction.

> [!NOTE]
> Make sure `mathlib4` and `repl` exist in the workspace directory before launching the server.

The server is up! You can test the endpoint with the same cURL request as in the containerized section.

If you change the code, validate your changes by running tests with:

```sh
pytest
```

### Example: Batch Verifying Lean Proofs

You can verify a large number of Lean proofs in parallel using the following example:

```python
import nest_asyncio
from client import Lean4Client

# Enable nested asyncio for Jupyter notebooks
nest_asyncio.apply()

client = Lean4Client(base_url="http://127.0.0.1:12332")
mock_proof = """import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem lean_workbook_10009 (a b c: ℝ) (ha : a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ a + b + c = 1): a^3 + b^3 + c^3 + (15 * a * b * c)/4 ≥ 1/4 := by

nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
sq_nonneg (a + b + c)]"""

response = client.verify([
    {"proof": mock_proof, "custom_id": "1"},
    {"proof": mock_proof, "custom_id": "2"}
], timeout=30)

```

response:

```json
{
    "results":
    [
        {
            "custom_id": "1",
            "error": null,
            "response": {
                "messages": [
                    {
                        "severity": "error",
                        "pos": {"line": 8, "column": 0},
                        "endPos": {"line": 9, "column": 22},
                        "data": "linarith failed to find a contradiction\ncase a\na b c : ℝ\nha : a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ a + b + c = 1\na✝ : 1 / 4 > a ^ 3 + b ^ 3 + c ^ 3 + 15 * a * b * c / 4\n⊢ False\nfailed"
                    }
                ],
                "env": 1,
                "time": 1.0048656463623047
            }
        },
        {
            "custom_id": "2",
            "..."
        }
    ]
}
```

## ⚙️ Environment Variables

| Variable                             | Default       | Description                                            |
| ------------------------------------ | ------------- | ------------------------------------------------------ |
| `LEANSERVER_HOST`                    | `0.0.0.0`     | Host address to bind the server                        |
| `LEANSERVER_PORT`                    | `12332`       | Port number for the server                             |
| `LEANSERVER_API_KEY`                 | `None`        | Optional API key for authentication                    |
| `LEANSERVER_LOG_DIR`                 | `./logs`      | Directory where logs are stored                        |
| `LEANSERVER_LOG_LEVEL`               | `INFO`        | Logging level (`DEBUG`, `INFO`, `ERROR`, etc.)         |
| `LEANSERVER_WORKSPACE`               | $(pwd)        | Root directory containing `mathlib` and `repl`         |
| `LEANSERVER_MAX_REPLS`               | **CPU count** | Maximum number of Lean REPL instances                  |
| `LEANSERVER_MAX_CONCURRENT_REQUESTS` | **CPU count** | Maximum number of concurrent requests in the Lean REPL |
| `LEANSERVER_HEALTHCHECK_CPU_USAGE_THRESHOLD` | **None** | CPU usage threshold for healthcheck |
| `LEANSERVER_HEALTHCHECK_MEMORY_USAGE_THRESHOLD` | **None** | Memory usage threshold for healthcheck |
| `LEANSERVER_REPL_MEMORY_LIMIT_GB` | **None** | Memory limit for REPLs |
| `LEANSERVER_REPL_MEMORY_CHECK_INTERVAL` | **None** | Number of consecutive commands that run on REPL before memory check |
| `LEANSERVER_HARD_ENFORCE_MEMORY_LIMIT` | **False** | Add per REPL memory limits directly when spawning the lake env repl process (may only work for Linux) |


Note:
-  `LEANSERVER_REPL_MEMORY_LIMIT_GB` needs to be used together with `LEANSERVER_REPL_MEMORY_CHECK_INTERVAL`
-  In some bloated systems, memory detection can be slow, which impacts performance. However, this isn't an issue in streamlined systems.
- `LEANSERVER_HARD_ENFORCE_MEMORY_LIMIT` can help avoid certain OOM issues (see Issue #25)


## 🚀 Performance Benchmarks

You can run benchmarks in the `benchmarks` directory on dataset: [Goedel-LM/Lean-workbook-proofs](https://huggingface.co/datasets/Goedel-LM/Lean-workbook-proofs)

If running benchmarks from an end-user computer, you may face the following error:

> tenacity.before_sleep:log_it:65 - Retrying **main**.Lean4Client.\_query.<locals>.query_with_retries in 10.0 seconds as it raised ClientConnectorError: Cannot connect to host 127.0.0.1:80 ssl:default [Too many open files].

You can check the maximum number of open files on your machine with `ulimit -n` (256 on a MacBook Pro). It may be smaller than what's needed to run the benchmark: increase it with `ulimit -n 65535`.

Server logs may show the following failure when a REPL gets acquired prior to be being deleted. It does not impact performances, it's only at the cache level.

> Failed to evict header 'import Mathlib\nimport Aesop with id 306512ca-8935-4cdb-b88b-7510e0c98ac3, putting it back

### Cached vs Non-Cached

| Mode       | Valid Proofs (%) | Total Verification Time (s) | Average Verification Time (s) |
| ---------- | ---------------- | --------------------------- | ----------------------------- |
| Cached     | 96.00            | 350.29                      | 3.65                          |
| Non-Cached | 96.00            | 493.67                      | 5.14                          |

**Note**:

- The benchmarks were run on a machine with **10 CPUs** (MacBook Pro M2).
- Script used: [`benchmark.py`](./benchmark.py)
- Dataset: First 100 samples from [`Goedel-LM/Lean-workbook-proofs`](https://huggingface.co/datasets/Goedel-LM/Lean-workbook-proofs)
- Params: `timeout = 60s`, `batch = 1`, `num_proc = 10` (number of CPU cores)
- Server: `LEANSERVER_MAX_REPLS = 10` and `LEANSERVER_MAX_CONCURRENT_REQUESTS = 10`

## 🙌 Contributing

Contributions are welcome! Please open an issue or submit a pull request.

## 📝 License

This project is licensed under the MIT License.
You are free to use, modify, and distribute this software with proper attribution. See the [LICENSE](./LICENSE) file for full details.

## 📑 Citation
```
@misc{santos2025kiminaleanservertechnical,
      title={Kimina Lean Server: Technical Report}, 
      author={Marco Dos Santos and Haiming Wang and Hugues de Saxcé and Ran Wang and Mantas Baksys and Mert Unsal and Junqi Liu and Zhengying Liu and Jia Li},
      year={2025},
      eprint={2504.21230},
      archivePrefix={arXiv},
      primaryClass={cs.LO},
      url={https://arxiv.org/abs/2504.21230}, 
}
```
