#!/usr/bin/env bash
# Gate a build log on the three things `lake build` exiting 0 does NOT prove:
#   1. the sorry count has not grown
#   2. the sorryAx dependencies of load-bearing declarations are exactly the recorded ones
#   3. the warning count has not grown
#
# Both matter here because sorries are warnings, not errors, and because a
# coherence field can be silently discharged by an autoparam riding on a sorry
# elsewhere (`sorry_if_sorry`) -- which looks identical to a real proof until
# you check the axioms.
#
# Note on the baseline RISING: that is not always a regression. Splitting one declaration
# whose sorried coherence fields were invisible into several named standalone lemmas raises
# the count while making the debt explicit and independently attackable. The evaluation
# coherence cores did exactly that; see the header of Biyoneda/Evaluation.lean.
#
# Usage: scripts/verify-build.sh [build.log]
#   (produce the log with: lake build 2>&1 | tee build.log)
set -uo pipefail

LOG="${1:-build.log}"
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BASELINE_FILE="$ROOT/.github/sorry-baseline"
WARN_BASELINE_FILE="$ROOT/.github/warning-baseline"

# Every `#print axioms` we require to have actually run. A gate that greps for
# bad output passes vacuously if the output disappears, so assert presence too.
#
# Two lists, because asserting sorryAx-freedom of something that is not sorryAx-free is
# not a gate, it is a lie that fails every build. Each declaration must appear in exactly
# one list, and both lists assert presence.
#
#   CLEAN_DECLS        must be sorryAx-free. Becoming contaminated is an ERROR.
#   CONTAMINATED_DECLS known to depend on sorryAx today. Becoming clean is a NOTICE,
#                      telling you to promote it to CLEAN_DECLS so the gate tightens.
#
# The ratchet therefore still runs in both directions: nothing clean can silently rot,
# and nothing that gets fixed can silently stay untracked.
#
# There were three roots. `catPseudoULift` (UniverseLift.lean) and `homPseudo` (Gadgets.lean)
# are both now fully proved -- the latter took `yonedaPairingComposite` and `yonedaPairing`
# clean. The third, `evaluationPseudo` (Evaluation.lean), closed on 2026-09-02 and took
# `yonedaEvaluation` with it. There is now NO remaining root: every declaration that still
# depends on `sorryAx` does so through the assembly layers, and after 2026-09-05 those are
# exactly the unit's top square and the counit -- two sorries, both in Unit.lean.
#
# The counit closed on 2026-09-05, and with it the whole development: `yonedaLemma` itself is
# in CLEAN_DECLS, the sorry baseline is 0, and CONTAMINATED_DECLS is empty for good. If it ever
# needs an entry again, something regressed.
CLEAN_DECLS=(
  "CategoryTheory.Bicategory.StrongTransIntoCats.lift"
  "CategoryTheory.Bicategory.StrongTransIntoCats.liftDom"
  "CategoryTheory.Pseudofunctor.StrongTrans.appFunctor"
  "CategoryTheory.Bicategory.evalHom"
  "CategoryTheory.Bicategory.evalAt"
  "CategoryTheory.Bicategory.strongTrans_id_app"
  "CategoryTheory.Bicategory.evalMapComp_hom"
  "CategoryTheory.Bicategory.evalMapComp_inv"
  "CategoryTheory.Bicategory.StrongTransIntoCats.comp"
  "CategoryTheory.Bicategory.StrongTransIntoCats.Id"
  "CategoryTheory.Bicategory.StrongTransIntoCats.toStrongTrans"
  "CategoryTheory.Bicategory.StrongTransIntoCats.precomposeCounit"
  "CategoryTheory.Bicategory.StrongTransIntoCats.toStrongTransMax"
  "CategoryTheory.Bicategory.StrongTransIntoCats.lift_comp_liftDom_naturality_app"
  "CategoryTheory.Bicategory.StrongTransIntoCats.Id_naturality_app"
  "CategoryTheory.Bicategory.ModificationIntoCats.toModification"
  "CategoryTheory.Bicategory.ModificationIntoCats.isoMk"
  "CategoryTheory.Bicategory.ModificationIntoCats.lift"
  "CategoryTheory.Bicategory.lift_modification_lhs"
  "CategoryTheory.Bicategory.lift_modification_rhs"
  "CategoryTheory.Bicategory.StrongTransIntoCats.ofStrongTrans"
  "CategoryTheory.Bicategory.strongTrans_naturality_id_lhs_app"
  "CategoryTheory.Bicategory.strongTrans_naturality_id_rhs_app"
  "CategoryTheory.Bicategory.strongTrans_naturality_comp_lhs_app"
  "CategoryTheory.Bicategory.strongTrans_naturality_comp_rhs_app"
  "CategoryTheory.Bicategory.eval_left_unitor"
  "CategoryTheory.Bicategory.eval_right_unitor"
  "CategoryTheory.Bicategory.eval_left_unitor_rhs_app"
  "CategoryTheory.Bicategory.eval_right_unitor_rhs_app"
  "CategoryTheory.Pseudofunctor.StrongTrans.naturality_id_app"
  "CategoryTheory.Bicategory.eval_whisker_left"
  "CategoryTheory.Bicategory.eval_whisker_right"
  "CategoryTheory.Bicategory.map_comp_cancel"
  "CategoryTheory.Bicategory.strongTrans_naturality_comp_inv_app"
  "CategoryTheory.Bicategory.eval_associator"
  "CategoryTheory.Bicategory.eval_associator_rhs_app"
  "CategoryTheory.Bicategory.strongTrans_comp_naturality_app"
  "CategoryTheory.Bicategory.map_map_comp"
  "CategoryTheory.Bicategory.strongTrans_naturality_slide"
  "CategoryTheory.Bicategory.evaluationPseudo"
  "Biyoneda.yonedaEvaluation'"
  "Biyoneda.yonedaEvaluation"
  "CategoryTheory.Bicategory.evalMapComp_hom_app"
  "CategoryTheory.Bicategory.evalMapComp_inv_app"
  "CategoryTheory.Bicategory.strongTrans_naturality_conj"
  "CategoryTheory.Bicategory.modification_naturality_conj"
  "Biyoneda.backwardsFibreFunctor"
  "Biyoneda.backwardsTransData"
  "Biyoneda.backwardsTrans"
  "Biyoneda.mapComp_assoc_app'"
  "CategoryTheory.Bicategory.homMapIdApp"
  "CategoryTheory.Bicategory.homMapCompApp"
  "CategoryTheory.Bicategory.homMapIdApp_naturality"
  "CategoryTheory.Bicategory.homMapCompApp_naturality"
  "CategoryTheory.Bicategory.homMapId"
  "CategoryTheory.Bicategory.homMapComp"
  "CategoryTheory.Bicategory.homPseudo"
  "CategoryTheory.Bicategory.yonedaPairingComposite"
  "Biyoneda.yonedaPairing"
  "Biyoneda.backwards_inner_core"
  "Biyoneda.backwards_app_core"
  "Biyoneda.backwardsNaturalityIsoApp"
  "Biyoneda.backwardsNaturalityIsoApp_hom_app"
  "Biyoneda.backwards_square_lhs_app"
  "Biyoneda.backwards_square_rhs_app"
  "Biyoneda.backwards_square_tail_app"
  "Biyoneda.backwards_square_core"
  "Biyoneda.backwards_naturality_square"
  "Biyoneda.backwardsNaturalityIso"
  "Biyoneda.backwards_natural_lhs_app"
  "Biyoneda.backwards_natural_rhs_app"
  "Biyoneda.backwards_natural_core"
  "Biyoneda.backwards_naturality_iso_natural"
  "Biyoneda.unitor_conj_pad"
  "Biyoneda.forwards_naturality_naturality_unitor"
  "Biyoneda.forwards_naturality_naturality_lhs_app"
  "Biyoneda.forwards_naturality_naturality_rhs_app"
  "Biyoneda.forwards_naturality_naturality_core"
  "Biyoneda.forwards_naturality_id_core"
  "Biyoneda.map_map_comp_dist"
  "Biyoneda.backwards_naturality_naturality_core"
  "Biyoneda.backwards_nn_lhs_app"
  "Biyoneda.backwards_nn_rhs_app"
  "Biyoneda.backwards_nn_slide"
  "Biyoneda.yonedaPairing_mapId_app"
  "Biyoneda.yonedaPairing_mapComp_app"
  "Biyoneda.backwards_comp_map_app"
  "Biyoneda.backwards_comp_lhs_app"
  "Biyoneda.backwards_comp_rhs_app"
  "CategoryTheory.Bicategory.strongTrans_comp_naturality_inv_app"
  "CategoryTheory.Bicategory.naturality_comp_assoc_core"
  "Biyoneda.backwards_comp_core"
  "Biyoneda.yonedaLemmaBackwardsData"
  "Biyoneda.yonedaLemmaBackwards"
  "CategoryTheory.Pseudofunctor.StrongTrans.naturality_comp_app"
  "CategoryTheory.Pseudofunctor.StrongTrans.naturality_naturality_app"
  "Biyoneda.yonedaEvaluation_mapComp_app"
  "Biyoneda.yonedaEvaluation_map_map"
  "Biyoneda.yonedaPairing_mapObj_app_map"
  "Biyoneda.yonedaPairing_mapObj_naturality_app"
  "Biyoneda.forwards_naturality_comp_core"
  "Biyoneda.yonedaLemmaForwardsData"
  "Biyoneda.yonedaLemmaForwards"
  "Biyoneda.backwards_id_core"
  "Biyoneda.backwards_id_lhs_app"
  "Biyoneda.backwards_id_rhs_app"
  # The unit's three nested isomorphisms, and the three cores they rest on (2026-09-05).
  # Every layer below the top square is now real; what remains sorried is the modification
  # square itself (`yonedaHomInvIdIso`) and the counit.
  "Biyoneda.yonedaUnitAppIso"
  "Biyoneda.unit_functor_core"
  "Biyoneda.unit_obj_core"
  "Biyoneda.unit_natiso_core"
  "Biyoneda.yonedaHomInvIdFunctorIso"
  "Biyoneda.yonedaHomInvIdObjIso"
  "Biyoneda.yonedaHomInvIdNatIso"
  "Biyoneda.yonedaInvHomIdNatIso"
  # The unit's modification square, and with it the unit itself (2026-09-05).
  "Biyoneda.unit_top_lhs"
  "Biyoneda.unit_top_rhs"
  "Biyoneda.unit_top_alpha"
  "Biyoneda.unit_top_core"
  "Biyoneda.yonedaHomInvIdIso"
  "Biyoneda.yonedaHomInvId"
  # The counit, and the assembled theorem (2026-09-05).
  "Biyoneda.mapComp_id_left_app"
  "Biyoneda.counit_core"
  "Biyoneda.counit_square_lhs_app"
  "Biyoneda.counit_id_naturality_app"
  "Biyoneda.counit_square_rhs_app"
  "Biyoneda.counit_backwards_app"
  "Biyoneda.counit_forwards_app"
  "Biyoneda.yonedaInvHomId"
  "Biyoneda.yonedaLemma"
)

# Emptied on 2026-08-30, repopulated on 2026-09-03, and emptied again on 2026-09-05 when
# `forwards_naturality_comp_core` closed and took the forward direction clean.  Both
# transformations of the equivalence are now `sorryAx`-free, so nothing belongs here; the
# remaining debt is in `Unit.lean`, whose declarations still carry literal `sorry`s and are
# therefore visible to the sorry ratchet.  Keep the array: the moment a `Unit.lean` obligation
# is delegated to a named lemma, its warning disappears and its entry belongs here.
CONTAMINATED_DECLS=()

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
# Count distinct sorried DECLARATIONS, not warning lines: one declaration can be
# reported more than once (a replayed build, or a `simp` whose arguments each carry
# `sorryAx`), and counting lines would inflate the ratchet and mask a real regression.
sorried=$(grep -oE '[^ ]+\.lean:[0-9]+:[0-9]+: declaration uses' "$LOG" | sort -u || true)
if [ -z "$sorried" ]; then count=0; else count=$(printf '%s\n' "$sorried" | wc -l | tr -d ' '); fi
baseline=$(tr -dc '0-9' < "$BASELINE_FILE" 2>/dev/null || echo "")
if [ -z "$baseline" ]; then
  echo "::error::missing or unreadable baseline: $BASELINE_FILE"
  exit 1
fi

if [ "$count" -gt "$baseline" ]; then
  note "**Sorries: $count — up from $baseline.** ❌"
  note ""
  note "Sorried declarations:"
  printf '%s\n' "$sorried" | sed 's/: declaration uses$//' | sed 's/^/    /'
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
# `#print axioms` wraps its list across lines when the declaration name is long, so the
# axioms can land on continuation lines. Matching only the first line silently misses them --
# this gate once reported a genuinely sorryAx-dependent declaration as clean. Pull the match
# plus its continuations and truncate at the closing bracket.
# Note the TWO messages Lean can emit. A declaration with a non-empty axiom list prints
# "'X' depends on axioms: [...]", but one with an EMPTY list prints "'X' does not depend on any
# axioms" -- no bracket, different wording. Matching only the first form reports the cleanest
# possible result as "no axiom check ran", which is a false failure; caught 2026-08-30 by the
# first declaration in this project to depend on nothing at all.
axioms_of() {
  if grep -qF "'$1' does not depend on any axioms" "$LOG"; then
    echo "does not depend on any axioms"
    return 0
  fi
  grep -F -A6 "'$1' depends on axioms" "$LOG" | tr '\n' ' ' | sed 's/\].*//' || true
}

for decl in ${CLEAN_DECLS+"${CLEAN_DECLS[@]}"}; do
  line=$(axioms_of "$decl")
  if [ -z "$line" ]; then
    note "**\`$decl\`: no axiom check ran.** ❌"
    echo "::error::expected '#print axioms $decl' in the build output; the assertion is missing"
    fail=1
  elif printf '%s' "$line" | grep -q 'sorryAx'; then
    note "**\`$decl\`: depends on sorryAx.** ❌"
    echo "::error::$decl depends on sorryAx (it is listed as clean)"
    fail=1
  else
    note "**\`$decl\`**: sorryAx-free. ✅"
  fi
done

for decl in ${CONTAMINATED_DECLS+"${CONTAMINATED_DECLS[@]}"}; do
  line=$(axioms_of "$decl")
  if [ -z "$line" ]; then
    note "**\`$decl\`: no axiom check ran.** ❌"
    echo "::error::expected '#print axioms $decl' in the build output; the assertion is missing"
    fail=1
  elif printf '%s' "$line" | grep -q 'sorryAx'; then
    note "\`$decl\`: depends on sorryAx, as recorded. ⚠️"
  else
    note "**\`$decl\`: now sorryAx-free.** ✅"
    note ""
    note "Tighten the gate: move \`$decl\` from \`CONTAMINATED_DECLS\` to \`CLEAN_DECLS\`."
    echo "::notice::$decl is now sorryAx-free; promote it to CLEAN_DECLS"
  fi
done

if [ "${#CLEAN_DECLS[@]}" -eq 0 ]; then
  note ""
  note "⚠️  \`CLEAN_DECLS\` is empty: no declaration is currently asserted sorryAx-free."
fi

# ── 3. warning ratchet ──────────────────────────────────────────────────────
# Warnings are the early-warning system for two things this project actually cares about:
# a Mathlib bump deprecating something we use, and simp sets drifting out from under a
# `simp only` list. Neither is an error, so neither is visible without a ratchet.
#
# `declaration uses` lines are excluded: section 1 already gates those, by DECLARATION rather
# than by line, and counting them here too would report one regression twice.
#
# Same two-way discipline as the sorry ratchet -- but note the asymmetry with it. A rising
# sorry count can be legitimate (splitting invisible debt into named lemmas); a rising warning
# count is not, so this one has no "sometimes fine" escape hatch. If a bump makes it rise,
# fix the warnings or raise the baseline deliberately, in a commit that says why.
note ""
warnings=$(grep -c 'warning:' "$LOG" || true)
sorry_warns=$(grep -c 'declaration uses' "$LOG" || true)
warn_count=$(( warnings - sorry_warns ))
warn_baseline=$(tr -dc '0-9' < "$WARN_BASELINE_FILE" 2>/dev/null || echo "")
if [ -z "$warn_baseline" ]; then
  echo "::error::missing or unreadable baseline: $WARN_BASELINE_FILE"
  fail=1
elif [ "$warn_count" -gt "$warn_baseline" ]; then
  note "**Warnings: $warn_count — up from $warn_baseline.** ❌"
  note ""
  note "New warnings:"
  grep 'warning:' "$LOG" | grep -v 'declaration uses' \
    | sed -E 's/.*warning: //' | cut -c1-110 | sort -u | sed 's/^/    /'
  echo "::error::warning count rose from $warn_baseline to $warn_count"
  fail=1
elif [ "$warn_count" -lt "$warn_baseline" ]; then
  note "**Warnings: $warn_count — down from $warn_baseline.** ✅"
  note ""
  note "Lower the ratchet so it keeps protecting: put \`$warn_count\` in \`.github/warning-baseline\`."
  echo "::notice::warning count fell to $warn_count; update .github/warning-baseline"
else
  note "**Warnings: $warn_count**, matching the baseline. ✅"
fi

note ""
if [ "$fail" -eq 0 ]; then note "All gates passed."; else note "Gates failed."; fi
exit "$fail"
