#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."

if [[ -e .lake/build || -L .lake/build ]]; then
  printf '%s\n' 'Use a fresh checkout or source archive with no .lake/build directory.' >&2
  exit 1
fi
sha256sum --check --strict --quiet SHA256SUMS SOURCE-SHA256SUMS

unset LEAN_PATH LEAN_SRC_PATH
export LAKE_ARTIFACT_CACHE=false LAKE_CACHE_DIR=
export LC_ALL=C
shopt -s globstar nullglob
cp -- SOURCE-SHA256SUMS verification/source-sha256.txt

sources=(AbcTwoNinths/**/*.lean Subexp/**/*.lean Subexp.lean Solution.lean)
targets=()
for source in "${sources[@]}"; do
  module=${source%.lean}
  targets+=("@/+${module//\//.}:olean")
done

lake -R -Kstrict=true --no-cache --wfail build "${targets[@]}" 2>&1 | tee verification/build.txt
for source in "${sources[@]}"; do
  test -s ".lake/build/lib/lean/${source%.lean}.olean"
done
test ! -e .lake/build/lib/lean/Challenge.olean
lake -R -Kstrict=true env lean -DwarningAsError=true SolutionAxioms.lean | tee verification/axioms.txt
expected_axioms="'AbcSubexp.subexp' depends on axioms: [propext, Classical.choice, Quot.sound]"
if [[ $(< verification/axioms.txt) != "$expected_axioms" ]]; then
  printf '%s\n' 'Unexpected axiom report.' >&2
  exit 1
fi

lake -R --no-cache build @/+Challenge:olean 2>&1 | tee verification/challenge.txt
lake -R env lean -DwarningAsError=true --run verification/StatementIdentity.lean > verification/statement-identity.json
cmp SOURCE-SHA256SUMS verification/source-sha256.txt
sha256sum --check --strict --quiet SHA256SUMS SOURCE-SHA256SUMS
