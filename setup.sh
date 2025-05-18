#!/usr/bin/env bash
set -euxo pipefail

LEAN_VERSION="v4.15.0"

command -v curl > /dev/null 2>&1 || { echo "Error: curl is not installed." >&2; exit 1; }

# Install Lean
echo "Installing lean ${LEAN_VERSION}"
pushd ~
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- --default-toolchain ${LEAN_VERSION} -y
source $HOME/.elan/env
popd

# Install REPL
echo "Installing REPL..."
if [ ! -d "repl" ]; then
    git clone https://github.com/leanprover-community/repl.git 
fi
pushd repl
git checkout ${LEAN_VERSION}
lake build
popd

# Install Mathlib
echo "Installing Mathlib..."
if [ ! -d "mathlib4" ]; then
    git clone https://github.com/leanprover-community/mathlib4.git
fi
pushd mathlib4
git checkout ${LEAN_VERSION}
lake exe cache get && lake build
popd