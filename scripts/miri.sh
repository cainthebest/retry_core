#!/usr/bin/env bash

set -euo pipefail

MIRIFLAGS="-Zmiri-strict-provenance -Zmiri-symbolic-alignment-check -Zmiri-tree-borrows" cargo +nightly miri test "$@"