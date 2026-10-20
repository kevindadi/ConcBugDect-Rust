#!/usr/bin/env bash
#
# Petri-net pipeline smoke tests (todolist T-001).
#
# Builds `pn` (unless PN_BIN is set), analyzes the benchmark crates listed
# below, and asserts the deadlock report's `Bug count` — and, for the async
# cases, the number of lock groups discovered (`[lockgroup-detail]` log lines).
# These assertions guard the async modeling (C-001..C-012, T-003) and the
# sync regression baseline promised in the todolist "engineering constraints".
#
# Usage:
#   ./scripts/smoke.sh              # build pn + run all cases
#   PN_BIN=target/debug/pn ./scripts/smoke.sh   # reuse an existing binary
#
# Environment:
#   PN_BIN         pn binary to use (default: build target/debug/pn)
#   PN_SMOKE_DIR   scratch directory for reports/logs (default: <repo>/tmp/smoke)
#   PN_LOG         log level for pn (default: warn; lock-group lines need warn)

set -euo pipefail

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

PN_BIN="${PN_BIN:-}"
if [[ -z "$PN_BIN" ]]; then
	echo "==> building pn"
	cargo build --manifest-path "$DIR/Cargo.toml" --bin pn
	PN_BIN="$DIR/target/debug/pn"
fi
[[ -x "$PN_BIN" ]] || { echo "pn binary not found/executable: $PN_BIN" >&2; exit 1; }

# pn links dynamically against the active toolchain's librustc_driver.
RUSTC_SYSROOT="$(rustc --print sysroot)"
export LD_LIBRARY_PATH="${RUSTC_SYSROOT}/lib${LD_LIBRARY_PATH:+:${LD_LIBRARY_PATH}}"
export PN_LOG="${PN_LOG:-warn}"

TMP="${PN_SMOKE_DIR:-$DIR/tmp/smoke}"
rm -rf "$TMP"
mkdir -p "$TMP"

failures=0

# run_case <bench-dir> <crate-name> <expected-bugs> [expected-lock-groups|-]
run_case() {
	local bench="$1" crate="$2" expect_bugs="$3" expect_groups="${4:--}"
	local log="$TMP/$crate.log"
	local out="$TMP/$crate"

	local label="bugs=$expect_bugs"
	if [[ "$expect_groups" != "-" ]]; then
		label="$label groups=$expect_groups"
	fi
	echo "==> $bench (expect $label)"
	if ! RUSTC_WRAPPER="$PN_BIN" \
		PN_FLAGS="-m deadlock -p $crate --pn-analysis-dir=$out" \
		CARGO_TARGET_DIR="$TMP/target" \
		cargo build --manifest-path "$DIR/bench/$bench/Cargo.toml" >"$log" 2>&1; then
		echo "FAIL: $crate: build/analysis failed (see $log)"
		tail -n 5 "$log"
		failures=$((failures + 1))
		return
	fi

	local report="$out/$crate/deadlock_report.txt"
	if [[ ! -f "$report" ]]; then
		echo "FAIL: $crate: missing report $report"
		failures=$((failures + 1))
		return
	fi

	local bugs groups ok=1
	bugs="$(sed -nE 's/^Bug count *: *([0-9]+).*/\1/p' "$report")"
	if [[ "$bugs" != "$expect_bugs" ]]; then
		echo "FAIL: $crate: bug count '$bugs' != expected '$expect_bugs'"
		ok=0
	fi

	if [[ "$expect_groups" != "-" ]]; then
		groups="$(grep -c '\[lockgroup-detail\] group' "$log" || true)"
		if [[ "$groups" != "$expect_groups" ]]; then
			echo "FAIL: $crate: lock groups '$groups' != expected '$expect_groups'"
			ok=0
		fi
	fi

	if ((ok)); then
		echo "PASS: $crate (bugs=$bugs)"
	else
		failures=$((failures + 1))
	fi
}

# --- async corpus (T-001): suspend/resume, spawn/join, lock-group merging ---
run_case deadlock/async-deadlock async_deadlock 1 2
run_case deadlock/async-no-deadlock async_no_deadlock 0 1

# --- sync regression baseline (todolist "engineering constraints") ---
run_case deadlock/intra intra 4
run_case deadlock/inter inter 4
run_case deadlock/conflict-inter conflict_inter 1
run_case deadlock/lock-closure lock_closure 1
run_case deadlock/static-ref static_ref 1
run_case deadlock/condvar-closure condvar_closure 6

echo
if ((failures > 0)); then
	echo "smoke: $failures case(s) FAILED"
	exit 1
fi
echo "smoke: all cases passed"
