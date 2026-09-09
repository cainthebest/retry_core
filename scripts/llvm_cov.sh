#!/usr/bin/env bash

set -euo pipefail

cargo llvm-cov --ignore-filename-regex '\.test\.rs$' "$@"