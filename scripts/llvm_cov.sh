#!/usr/bin/env bash

set -euo pipefail

cargo llvm-cov \
  --open \
  --ignore-filename-regex '\.test\.rs$' \
  "$@"