#!/usr/bin/env bash
# Gate a build log on the two things `lake build` exiting 0 does NOT prove:
#   1. the sorry count has not grown
#   2. nothing load-bearing depends on sorryAx
#
# Both matter here because sorries are warnings, not errors, and because a
# coherence field can be silently discharged by an autoparam riding on a sorry
# elsewhere (`sorry_if_sorry`) -- which looks identical to a real proof until
# you check the axioms.
#
# Usage: scripts/verify-build.sh [build.log]
#   (produce the log with: lake build 2>&1 | tee build.log)
set -uo pipefail

LOG="${1:-build.log}"
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BASELINE_FILE="$ROOT/.github/sorry-baseline"

# Every `#print axioms` we require to have actually run. A gate that greps for
# bad output passes vacuously if the output disappears, so assert presence too.
REQUIRED_AXIOM_DECLS=(
  "CategoryTheory.Bicategory.yonedaPairingComposite"
  "yonedaPairing"
)

fail=0
note() {
  echo "$*"
  if [ -n "${GITHUB_STEP_SUMMARY:-}" ]; then echo "$*" >> "$GITHUB_STEP_SUMMARY"; fi
  return 0
}

[ -f "$LOG" ] || { echo "::error::build log not found: $LOG"; exit 1; }

note "## Build verification"
note ""

# ── 1. sorry ratchet ────────────────────────────────────────────────────────
count=$(grep -c 'declaration uses' "$LOG" || true)
baseline=$(tr -dc '0-9' < "$BASELINE_FILE" 2>/dev/null || echo "")
if [ -z "$baseline" ]; then
  echo "::error::missing or unreadable baseline: $BASELINE_FILE"
  exit 1
fi

if [ "$count" -gt "$baseline" ]; then
  note "**Sorries: $count — up from $baseline.** ❌"
  note ""
  note "New sorried declarations:"
  grep 'declaration uses' "$LOG" | sed 's/^/    /' | sed 's/warning: //'
  echo "::error::sorry count rose from $baseline to $count"
  fail=1
elif [ "$count" -lt "$baseline" ]; then
  note "**Sorries: $count — down from $baseline.** ✅"
  note ""
  note "Lower the ratchet so it keeps protecting: put \`$count\` in \`.github/sorry-baseline\`."
  echo "::notice::sorry count fell to $count; update .github/sorry-baseline"
else
  note "**Sorries: $count**, matching the baseline. ✅"
fi

# ── 2. axiom gate ───────────────────────────────────────────────────────────
note ""
axiom_lines=$(grep 'depends on axioms' "$LOG" || true)

for decl in "${REQUIRED_AXIOM_DECLS[@]}"; do
  line=$(printf '%s\n' "$axiom_lines" | grep -F "'$decl' depends on axioms" || true)
  if [ -z "$line" ]; then
    note "**\`$decl\`: no axiom check ran.** ❌"
    echo "::error::expected '#print axioms $decl' in the build output; the assertion is missing"
    fail=1
  elif printf '%s' "$line" | grep -q 'sorryAx'; then
    note "**\`$decl\`: depends on sorryAx.** ❌"
    echo "::error::$decl depends on sorryAx"
    fail=1
  else
    note "**\`$decl\`**: sorryAx-free. ✅"
  fi
done

note ""
if [ "$fail" -eq 0 ]; then note "All gates passed."; else note "Gates failed."; fi
exit "$fail"
