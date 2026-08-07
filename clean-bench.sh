#!/usr/bin/env bash

set -euo pipefail

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BENCH_DIR="${DIR}/bench"
DRY_RUN=false

usage() {
	cat <<EOF
Usage: ./clean-bench.sh [--dry-run]

Remove all benchmark build artifacts under bench/:
  - bench/**/target
  - bench/**/Cargo.lock

Options:
  --dry-run   only print what would be removed
EOF
}

if [[ "${1:-}" == "-h" || "${1:-}" == "--help" ]]; then
	usage
	exit 0
fi

if [[ "${1:-}" == "--dry-run" ]]; then
	DRY_RUN=true
fi

if [[ ! -d "$BENCH_DIR" ]]; then
	echo "bench directory not found: $BENCH_DIR" >&2
	exit 1
fi

mapfile -t target_dirs < <(find "$BENCH_DIR" -type d -name target | sort)
mapfile -t lock_files < <(find "$BENCH_DIR" -type f -name Cargo.lock | sort)

echo "target dirs : ${#target_dirs[@]}"
for path in "${target_dirs[@]}"; do
	echo "  $path"
done

echo "Cargo.lock  : ${#lock_files[@]}"
for path in "${lock_files[@]}"; do
	echo "  $path"
done

if [[ "$DRY_RUN" == true ]]; then
	exit 0
fi

if [[ ${#target_dirs[@]} -gt 0 ]]; then
	rm -rf "${target_dirs[@]}"
fi

if [[ ${#lock_files[@]} -gt 0 ]]; then
	rm -f "${lock_files[@]}"
fi

mapfile -t remaining < <(find "$BENCH_DIR" \( -type d -name target -o -type f -name Cargo.lock \) | sort)

if [[ ${#remaining[@]} -gt 0 ]]; then
	echo "cleanup incomplete, remaining paths:" >&2
	for path in "${remaining[@]}"; do
		echo "  $path" >&2
	done
	exit 1
fi

echo "bench cleanup complete"
