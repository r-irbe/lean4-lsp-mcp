#!/usr/bin/env bash
# Regenerate tests/fixtures/lean_oracle.tsv using the pinned Lean 4 toolchain.
# Strict 7-bit ASCII (INV-001). Runs one-shot `lake env lean --run`; it never starts lake serve.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CRATE_DIR="$(cd "${SCRIPT_DIR}/.." && pwd)"
OUT="${CRATE_DIR}/tests/fixtures/lean_oracle.tsv"
mkdir -p "$(dirname "${OUT}")"

if [[ -n "${LEAN_ORACLE_PROJECT_DIR:-}" && -d "${LEAN_ORACLE_PROJECT_DIR}" ]]; then
  cd "${LEAN_ORACLE_PROJECT_DIR}"
elif [[ -d "${CRATE_DIR}/lean" ]]; then
  cd "${CRATE_DIR}/lean"
elif [[ -d "${CRATE_DIR}/../../docs/easci/lean" ]]; then
  cd "${CRATE_DIR}/../../docs/easci/lean"
fi

lake env lean --run "${SCRIPT_DIR}/gen_oracle.lean" | LC_ALL=C tr -d '\r' > "${OUT}.tmp"
if LC_ALL=C grep -q '[^ -~	]' "${OUT}.tmp"; then
  echo "non-ASCII byte in oracle output" >&2
  rm -f "${OUT}.tmp"
  exit 1
fi
mv "${OUT}.tmp" "${OUT}"
echo "wrote ${OUT} ($(wc -l < "${OUT}") rows; $(head -1 "${OUT}"))"
