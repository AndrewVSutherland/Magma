#!/bin/bash
# Run the Magma package test suite: every tests/test_*.m, in parallel.
#
# Usage: ./tests/run_tests.sh [-jN]   (default -j4)
#
# Must be invoked so that the repo root (containing magma.spec) is the cwd,
# or from anywhere — the script cd's to the repo root itself.
# A test passes iff its log contains the line "ALL TESTS PASSED <basename>"
# AND contains no Magma error banner ("User error"/"Runtime error"/"Internal
# error") — identifier errors do not halt magma -b, so the sentinel alone
# could mask a partially-skipped test file.
# Exit status is nonzero if any test fails.

set -u

JOBS=4
for arg in "$@"; do
  case "$arg" in
    -j*) JOBS="${arg#-j}" ;;
    *) echo "Unknown argument: $arg" >&2; echo "Usage: $0 [-jN]" >&2; exit 2 ;;
  esac
done
case "$JOBS" in ''|*[!0-9]*) echo "Bad -j value" >&2; exit 2 ;; esac

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT" || exit 2
mkdir -p tests/logs

TESTS=(tests/test_*.m)
if [ ${#TESTS[@]} -eq 0 ]; then echo "No tests found" >&2; exit 2; fi

run_one() {
  local t="$1"
  local name log start end secs
  name="$(basename "$t")"
  log="tests/logs/${name%.m}.log"
  start=$(date +%s.%N)
  timeout 600 magma -b "$t" > "$log" 2>&1
  end=$(date +%s.%N)
  secs=$(awk -v a="$start" -v b="$end" 'BEGIN{printf "%.1f", b-a}')
  if grep -q "ALL TESTS PASSED ${name}" "$log" && \
     ! grep -qE '^(User error|Runtime error|Internal error)' "$log"; then
    echo "PASS $secs $name"
  else
    echo "FAIL $secs $name"
  fi
}
export -f run_one

RESULTS="$(printf '%s\n' "${TESTS[@]}" | xargs -P "$JOBS" -I{} bash -c 'run_one "$@"' _ {})"

echo
echo "==================== TEST SUMMARY ===================="
printf "%-28s %-6s %8s\n" "TEST" "RESULT" "SECONDS"
FAILED=0
while read -r status secs name; do
  printf "%-28s %-6s %8s\n" "$name" "$status" "$secs"
  [ "$status" = "FAIL" ] && FAILED=$((FAILED+1))
done <<< "$(echo "$RESULTS" | sort -k3)"
echo "======================================================="
TOTAL=${#TESTS[@]}
echo "$((TOTAL-FAILED))/$TOTAL passed"
if [ "$FAILED" -gt 0 ]; then
  echo "FAILURES: see tests/logs/ for details" >&2
  exit 1
fi
exit 0
