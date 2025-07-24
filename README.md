# Kimina Lean Server

This project serves the [Lean REPL](https://github.com/leanprover-community/repl) using FastAPI. 
It supports parallelization to check Lean 4 proofs at scale.

📄 Technical report: [Technical Report](./Technical_Report.pdf)

A Python SDK simplifies interaction with the server's API.

## Table of Contents

- [Server](#server)
- [Client](#client)
- [Contributing](#contributing)
- [License](#license)
- [Citation][#citation]

This repository contains the source code for:
- the Kimina Lean server
- a Python client to interact with it

## Server

From source (make sure you have Astral's uv installed):
```sh
cp .env.template .env # Optional
bash setup.sh
uv run python -m server
```

> [!NOTE]
> Make sure `mathlib4` and `repl` exist in the workspace directory before launching the server from source.


Or with `docker compose up` (pulls from Docker Hub).  
Equivalent run command is:
```sh
docker run -d \
  --name server \
  --restart unless-stopped \
  --env-file .env \
  -p 80:${LEAN_SERVER_PORT} \
  projectnumina/kimina-lean-server:2.0.0
```

To shut down the container / view logs:

```sh
docker compose down
docker compose logs -f
```

Build your own image with specific Lean version with:
```sh
docker build --build-arg=LEAN_SERVER_LEAN_VERSION=v4.21.0 .
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

Or use the client below.

## Client

From [PyPI](https://test.pypi.org/project/kimina/):
```sh
pip install kimina
```

Example use:
```python
from kimina import Kimina
client = Kimina() # Defaults to "http://localhost:8000", no API key
client.check("#check Nat")
```

Or from source with `pip install -e .`

## Contributing

Contributions are welcome, just open an issue or submit a pull request.

To contribute, ensure you have Astral's [uv](https://docs.astral.sh/uv/) installed and:

```sh
uv run pre-commit install
```

On commit, the hooks:
- run `pyright` and `mypy`
- enforce [conventional commits](https://www.conventionalcommits.org/en/v1.0.0/). 

An additional hook runs basic tests on push.

> [!TIP]
> Use `--no-verify` to skip hooks on commit / push (but the CI runs them).


Install [Lean 4](https://github.com/leanprover/lean4) and build the [repl](https://github.com/leanprover-community/repl) and [mathlib4](https://github.com/leanprover-community/mathlib4):
```sh
bash setup.sh
```

Run tests with:
```sh
pytest

# Performance tests on first rows of Goedel (ensures less than 10s average check time per proof)
pytest -m perfs

# Tests on 100 first Goedel rows to validate API backward-compatibility
pytest -m match
```

To release the client:
- bump the version in `pyproject.toml`
- run the "Publish to PyPI" action on Github

To release the server:
- bump the version in `compose-prod.yaml`
- run the "Deploy to Google Cloud" action on Github
- run the "Publish to Docker" action on Github (doesn't exist yet)

## License

This project is licensed under the MIT License.
You are free to use, modify, and distribute this software with proper attribution. See the [LICENSE](./LICENSE) file for full details.

## Citation
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



### Example: Batch Verifying Lean Proofs

You can verify a large number of Lean proofs in parallel using the following example:

```python
import nest_asyncio
from client import Lean4Client

# Enable nested asyncio for Jupyter notebooks
nest_asyncio.apply()

client = Lean4Client(base_url="http://localhost:8000")
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
| `LEAN_SERVER_HOST`                    | `0.0.0.0`     | Host address to bind the server                        |
| `LEAN_SERVER_PORT`                    | `12332`       | Port number for the server                             |
| `LEAN_SERVER_API_KEY`                 | `None`        | Optional API key for authentication                    |
| `LEAN_SERVER_LOG_DIR`                 | `./logs`      | Directory where logs are stored                        |
| `LEAN_SERVER_LOG_LEVEL`               | `INFO`        | Logging level (`DEBUG`, `INFO`, `ERROR`, etc.)         |
| `LEAN_SERVER_WORKSPACE`               | $(pwd)        | Root directory containing `mathlib` and `repl`         |
| `LEAN_SERVER_MAX_REPLS`               | **CPU count** | Maximum number of Lean REPL instances                  |
| `LEAN_SERVER_MAX_CONCURRENT_REQUESTS` | **CPU count** | Maximum number of concurrent requests in the Lean REPL |
| `LEAN_SERVER_HEALTHCHECK_CPU_USAGE_THRESHOLD` | **None** | CPU usage threshold for healthcheck |
| `LEAN_SERVER_HEALTHCHECK_MEMORY_USAGE_THRESHOLD` | **None** | Memory usage threshold for healthcheck |
| `LEAN_SERVER_REPL_MEMORY_LIMIT_GB` | **None** | Memory limit for REPLs |
| `LEAN_SERVER_REPL_MEMORY_CHECK_INTERVAL` | **None** | Number of consecutive commands that run on REPL before memory check |
| `LEAN_SERVER_HARD_ENFORCE_MEMORY_LIMIT` | **False** | Add per REPL memory limits directly when spawning the lake env repl process (may only work for Linux) |


Note:
-  `LEAN_SERVER_REPL_MEMORY_LIMIT_GB` needs to be used together with `LEANSERVER_REPL_MEMORY_CHECK_INTERVAL`
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
