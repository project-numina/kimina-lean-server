#!/usr/bin/env bash
set -euxo pipefail

if [ -f .env ]; then
  set -a
  source .env
  set +a
fi

LEAN_SERVER_LEAN_VERSION="${LEAN_SERVER_LEAN_VERSION:-v4.15.0}"
REPL_REPO_URL="${REPL_REPO_URL:-https://github.com/leanprover-community/repl.git}"
REPL_BRANCH="${REPL_BRANCH:-$LEAN_SERVER_LEAN_VERSION}"
MATHLIB_REPO_URL="${MATHLIB_REPO_URL:-https://github.com/leanprover-community/mathlib4.git}"
MATHLIB_BRANCH="${MATHLIB_BRANCH:-$LEAN_SERVER_LEAN_VERSION}"

command -v curl >/dev/null 2>&1 || { echo >&2 "curl is required"; exit 1; }
command -v git  >/dev/null 2>&1 || { echo >&2 "git is required";  exit 1; }

echo "Installing Elan"
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf \
  | sh -s -- --default-toolchain "${LEAN_SERVER_LEAN_VERSION}" -y
source "$HOME/.elan/env"

echo "Installing Lean ${LEAN_SERVER_LEAN_VERSION}"
lean --version

install_repo() {
  local name="$1" url="$2" branch="$3" upd_manifest="$4"
  echo "Installing ${name}@${branch}..."
  if [ ! -d "$name" ]; then
    git clone --branch "${branch}" --single-branch --depth 1 "$url" "$name"
  fi
  pushd "$name"
    git checkout "${branch}"
    if [ "$name" = "mathlib4" ]; then
      lake exe cache get
    fi
    lake build
    if [ "$upd_manifest" = "true" ]; then
      jq '.packages |= map(.type="path"|del(.url)|.dir=".lake/packages/"+.name)' \
         lake-manifest.json > lake-manifest.json.tmp && mv lake-manifest.json.tmp lake-manifest.json
    fi
  popd
}

install_repo repl "$REPL_REPO_URL" "$REPL_BRANCH" false
install_repo mathlib4 "$MATHLIB_REPO_URL" "$MATHLIB_BRANCH" true
