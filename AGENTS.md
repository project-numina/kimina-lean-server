# Contributor Guide

## Dev Environment Tips
- Start by copying the environment variables with `cp .env.template .env`
- Use uv for most commands (add a dependency, run python) to ensure you have the proper dependencies: https://docs.astral.sh/uv/
- Use `uv run pre-commit install` to have pre-commits run automatically (pyright + mypy)
- Install the pre-push hook `uv run pre-commit install --hook-type pre-push` to automatically run tests before pushing
- Run `bash setup.sh` to install the elan suite with Lean 4 and sync of the `repl` and `mathlib4` repositories

## Testing Instructions
- Make sure you have a `.env` file where BASE points to `/workspace/fast-repl` as that's where you will iterate
- Run `uv run pre-commit run --all-files` to check typing
- Validate your changes by running tests: `uv run pytest`
- Add or update tests for the code you change, even if nobody asked.

## PR instructions
Title format: [<project_name>] <Title>