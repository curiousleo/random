#!/usr/bin/env bash

# http://redsymbol.net/articles/unofficial-bash-strict-mode/
set -euo pipefail
IFS=$'\n\t'

# Change to project root directory
# https://stackoverflow.com/a/246128 and https://stackoverflow.com/a/8426110
DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
cd "$(dirname "$DIR")"

# Regenerate .travis.yml
haskell-ci regenerate

# Ensure that the patch still applies cleanly
patch --reverse --dry-run .travis.yml .travis.yml.patch
