#!/usr/bin/env bash
# Build lean_analyzer.wasm (wasm32-unknown-unknown) and copy to data/lean_analyzer.wasm.
# Optionally pass downstream directories as arguments to sync the compiled WASM binary.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CRATE_DIR="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${CRATE_DIR}"
cargo build --target wasm32-unknown-unknown --release

WASM_OUT="${CRATE_DIR}/target/wasm32-unknown-unknown/release/lean_analyzer.wasm"
if [[ ! -f "${WASM_OUT}" && -f "${CRATE_DIR}/../../target/wasm32-unknown-unknown/release/lean_analyzer.wasm" ]]; then
  WASM_OUT="${CRATE_DIR}/../../target/wasm32-unknown-unknown/release/lean_analyzer.wasm"
fi
if [[ ! -f "${WASM_OUT}" ]]; then
  echo "ERROR: WASM binary not found at ${WASM_OUT}" >&2
  exit 1
fi

mkdir -p "${CRATE_DIR}/data" "${CRATE_DIR}/wasm"
cp "${WASM_OUT}" "${CRATE_DIR}/data/lean_analyzer.wasm"
cp "${WASM_OUT}" "${CRATE_DIR}/wasm/lean_analyzer.wasm"
echo "Updated ${CRATE_DIR}/data/lean_analyzer.wasm and ${CRATE_DIR}/wasm/lean_analyzer.wasm"

for dest_dir in "$@"; do
  if [[ -d "${dest_dir}" ]]; then
    cp "${WASM_OUT}" "${dest_dir}/lean_analyzer.wasm"
    echo "Synced ${dest_dir}/lean_analyzer.wasm"
  fi
done
