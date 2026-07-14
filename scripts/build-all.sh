#!/usr/bin/env bash
# Copyright (c) 2025 Andrew Farmer
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.
#
# Build retrie and run its test suite against every GHC listed in the
# `tested-with:` field of retrie.cabal.
#
#   ./scripts/build-all.sh              # all versions from tested-with
#   ./scripts/build-all.sh 9.10.3       # just the versions named
#   BUILD_ONLY=1 ./scripts/build-all.sh # skip the test run
#
# Each version gets its own build directory so switching compilers does not
# throw away the previous one's build products. `-w` is passed explicitly so a
# `with-compiler:` line in cabal.project.local does not override us.

set -uo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

if [ $# -gt 0 ]; then
  versions=("$@")
else
  # tested-with: GHC ==9.6.7, GHC ==9.8.4, ... -> 9.6.7 9.8.4 ...
  read -r -a versions <<<"$(sed -n 's/^tested-with:.*/&/p' retrie.cabal |
    grep -o '[0-9][0-9.]*' | tr '\n' ' ')"
fi

if [ ${#versions[@]} -eq 0 ]; then
  echo "error: no GHC versions found in the tested-with field of retrie.cabal" >&2
  exit 1
fi

results=()
status=0

for ghc in "${versions[@]}"; do
  compiler="ghc-$ghc"
  builddir="dist-newstyle/$compiler"

  if ! command -v "$compiler" >/dev/null 2>&1; then
    echo "==> $compiler not on PATH, skipping (try: ghcup install ghc $ghc)"
    results+=("SKIP  $compiler (not installed)")
    status=1
    continue
  fi

  echo "==> $compiler: build"
  if ! cabal build -w "$compiler" --builddir="$builddir" all; then
    results+=("FAIL  $compiler (build)")
    status=1
    continue
  fi

  if [ -n "${BUILD_ONLY:-}" ]; then
    results+=("OK    $compiler (build only)")
    continue
  fi

  echo "==> $compiler: test"
  if ! cabal test -w "$compiler" --builddir="$builddir" --test-show-details=direct all; then
    results+=("FAIL  $compiler (test)")
    status=1
    continue
  fi

  results+=("OK    $compiler")
done

echo
echo "Summary"
echo "-------"
printf '%s\n' "${results[@]}"

exit $status
