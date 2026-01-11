# Contributing

Contributions are welcome 🤗, just open an issue or submit a pull request.

## Dev setup

To contribute, ensure you have Astral's [uv](https://docs.astral.sh/uv/) installed and:

```sh
uv run pre-commit install
```

On commit, the hooks:
- run `ruff`, `pyright` and `mypy`
- enforce [conventional commits](https://www.conventionalcommits.org/en/v1.0.0/). 

`mypy` was slow against the `client` directory, so I excluded it in the pre-commit config, therefore also on the CI. 
You can still run `mypy` manually to check. 

An additional hook runs basic tests on push.

> [!TIP]
> Use `--no-verify` to skip hooks on commit / push (but the CI runs them).


Install [Lean 4](https://github.com/leanprover/lean4) and build the [repl](https://github.com/leanprover-community/repl) and [mathlib4](https://github.com/leanprover-community/mathlib4):
```sh
bash setup.sh
```

## Tests

Run tests with (reads your `LEAN_SERVER_API_KEY` so make sure that line is commented):
```sh
pytest

# Performance tests on first rows of Goedel (ensures less than 10s average check time per proof)
pytest -m perfs

# Tests on 100 first Goedel rows to validate API backward-compatibility
pytest -m match # Use -n auto to use all cores.
```

## Releases

To release the client:
- bump the version in `pyproject.toml` and run `uv lock`
- run the "Publish to PyPI" action on Github

To release the server:
- bump the version in `compose-prod.yaml` and in Dockerfile
- run the "Publish to Docker" action on Github (doesn't exist yet)