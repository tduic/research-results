#!/bin/sh
# Build one module at a time, dependencies first: the kernel checks of the larger
# codes need most of a CI runner's memory, so parallel builds can be killed.
set -eu
cd -- "$(dirname -- "$0")"
export LEAN_NUM_THREADS=1
for m in Basic N10M30 N11M36 N12M48 N16M108 N17M109 Statement; do
  lake build "Trifference.$m"
done
lake build
