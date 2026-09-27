#!/usr/bin/env bash
# Synthetic intent fixtures only. This script never approves a project contract.
set -euo pipefail
cd "$(dirname "$0")/.."
if [[ "$(uname -s)" != Linux ]]; then
  echo 'The isolated proof worker requires Linux. Run this checkout in a Linux VM or remote Linux host.' >&2
  exit 2
fi
for binary in lean lake python3 bwrap; do
  command -v "$binary" >/dev/null || { echo "Missing prerequisite: $binary" >&2; exit 2; }
done
mkdir -p ci-evidence
run_logged() {
  local label="$1"; shift
  local status=0
  "$@" >"ci-evidence/$label.log" 2>&1 || status=$?
  printf '%s\n' "$status" >"ci-evidence/$label.exit"
  cat "ci-evidence/$label.log"
  return "$status"
}
lean --version > ci-evidence/stage2-lean-version.txt
run_logged stage2-protocol python3 -m unittest discover -s scripts -p test_m2_proof_jobs.py -v
run_logged stage2-build lake build Macaulean:shared MRDI:shared Macaulean.Verification.Proofs Macaulean.Verification.ProofJobs.Prover MacauleanTest.ProofJobKernel
run_logged stage2-export lake env lean \
  --load-dynlib="$PWD/.lake/build/lib/libMacaulean_MRDI.so" \
  --load-dynlib="$PWD/.lake/build/lib/libMacaulean_Macaulean.so" \
  MacauleanTest/ProofJobExport.lean
run_logged stage2-native python3 scripts/test_m2_proof_jobs_native.py
printf '%s\n' 'M2_PROOF_SMOKE_COMPLETE: synthesis, independent checking, fresh replay and rejection controls passed.'
