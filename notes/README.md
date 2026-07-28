# Working notes

Resumption notes for the sorry-filling effort in `Biyoneda/Basic.lean`, and for the later
structural work that split the project into several files and explored rebuilding
`yonedaPairing` from general gadgets. These are working documents, not documentation of the
finished proof — they record captured goal states, the descent recipes that worked, and the
negative results worth not repeating.

## `Basic.lean` sorry-filling (Phases 1–3)

| File | Cluster |
|---|---|
| `evaluation_coherence_wip.md` | `yonedaEvaluation'` coherence (Phase 1 — **complete**, incl. the associator recipe) |
| `associator_reduced_goal.txt` | the staged `map₂_associator` goal, kept for reference |
| `forwards_naturality_wip.md` | `yonedaLemmaForwards` coherence ×3 (Phase 2 — **parked**, with the verified descent recipe and the two remaining gaps) |
| `backwards_naturality_wip.md` | `yonedaLemmaBackwards` naturality (closed) and its coherence fields (Phase 3) |
| `backwards_coherence_goals.txt` | captured goal states for the Phase 3 fields |
| `p3_backwards_wip.md` | resumption note for the backwards-coherence obligations |
| `p4_mapcomp_wip.md` | `yonedaPairing.mapComp` naturality — parked on a defeq-toxicity perf wall |
| `naturality_comp_partial.lean.txt` | a partial proof snapshot for `naturality_comp` |

## Structural work: splitting the file, and rebuilding `yonedaPairing` from gadgets

| File | Content |
|---|---|
| `level2_refactor.md` | extracting `Biyoneda/Evaluation.lean` and `UniverseLift.lean` out of `Basic.lean` — the "alias trap" (renaming a def breaks `simp`/`dsimp` unfold lists) was discovered and documented here |
| `hom_pseudofunctor_scoping.md` | feasibility scoping for `Biyoneda/Gadgets.lean` (`Pseudofunctor.prod`/`op`, the two-variable `homPseudo`) before it was built |
| `zulip_draft.md` | draft post to the Lean Zulip `#mathlib4` stream about upstreaming `Biyoneda.Evaluation` and `Biyoneda.ForMathlib` |

Where things stand with the gadgets and the `composite-pairing` branch is *not* in these notes —
see the project overview instead (ask, or check `MEMORY.md` / the project memory file), since it
changes faster than these are updated.

The phase plan and project-level status live in the Claude memory for this project; the
transferable Lean technique lives in the `lean-category-theory` skill.
