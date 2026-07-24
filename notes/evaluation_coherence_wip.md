# Phase 1 WIP: yonedaEvaluation' coherence (2026-07-17; golfed 2026-07-19)

NOTE (b86e6db): the field descent simps were linter-cleaned — six never-firing lemmas
(Cat.whiskerLeft/Right_app, Cat.Hom₂.comp_app, eqToHom_refl, Category.comp_id/id_comp)
were REMOVED from the simp only lists (the template block below shows the old lists).
The captured associator goal is unchanged (removed args never fired). unusedTactic
linter is silenced on the def (skip-fallbacks are structural).

DONE: map₂_whisker_left (cf48845), map₂_whisker_right (196444a), map₂_left_unitor +
map₂_right_unitor (3a7dc24). REMAIN: map₂_associator ONLY — its field already carries the
descent prefix (e37931d); the fully-reduced goal is in associator_reduced_goal.txt.

## Unitor lessons (beyond the template)
- Unitor-modification components in the pseudofunctor bicategory are DEFEQ identities:
  `have hl : ((λ_ f).hom.2.as.app a.1).toNatTrans.app Z = 𝟙 _ := rfl` (same for ρ_ and for
  the identity transformation's naturality inv). Then erw [hl]; erw [Functor.map_id];
  erw [Category.id_comp] kills the modification factor.
- naturality_id_hom_app's eqToHoms become 𝟙s after `dsimp at hid`.
- Inverse-form squares: (Iso.inv_comp_eq (…toNatIso…app…)).mpr then a `show` re-spelling
  the ((toNatIso e).app Z).hom head back to hom.toNatTrans.app (kabstract keys on the HEAD
  SYMBOL — erw cannot bridge Iso.hom vs NatTrans.app heads; only show/defeq-ascription can).
- Stray mid-chain 𝟙s that survive simp id-lemmas: bounded
  `iterate 6 (first | erw [Category.id_comp] | erw [Category.comp_id] | skip)` then rfl.

## map₂_associator battle plan
Goal shape (see associator_reduced_goal.txt): both sides ~5 atoms + 𝟙-noise; atoms include
(f ≫ g).2- and (g ≫ h).2-naturality components (COMPOSITE transformations → their point
values need categoryStruct_comp_naturality_hom unfolding, as in backwards A′), all four
mapComps of d.2/c.2, and h.2/g.2-naturality slides. Expected ingredients:
d.2.map₂_associator at points (hw), Pseudofunctor.mapComp_assoc_*_hom_app,
naturality_comp_hom_app for the composite transformations, plus the toolkit. Recipe:
transcribe core with uniform nested-atomic points + 𝟙s verbatim (plug needs them);
inside the core: id-erosion first, then unfold composite-naturality atoms, then the
slide/fold/cancel cascade. Budget a full session; the plug line is already staged as the
field's final `sorry`.

## The proven two-layer template (worked twice, use verbatim)

FIELD (in yonedaEvaluation', which carries `set_option maxHeartbeats 800000` with comment):
  apply Cat.Hom₂.ext_app; intro Z
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, whiskerLeftIso_hom,
    whiskerLeftIso_inv, whiskerRightIso_hom, whiskerRightIso_inv, Cat.Hom.toNatTrans_comp,
    NatTrans.comp_app, Cat.whiskerLeft_toNatTrans, Cat.whiskerRight_toNatTrans,
    whiskerLeft_app, whiskerRight_app, Cat.whiskerLeft_app, Cat.whiskerRight_app,
    Cat.Hom₂.comp_app, Cat.associator_hom_app, Cat.associator_inv_app, eqToHom_refl,
    Category.comp_id, Category.id_comp]
  simp only [prod_whisker*/product-projection lemmas as needed]
  iterate 12 (first | erw [eqToHom_refl] | erw [Category.id_comp] | erw [Category.comp_id] | skip)
  <maybe: dsimp+erw of c.2's own coherence axiom (hw), a mapComp-naturality slide (h1)>
  exact <core> ...args... Z
Then trace, transcribe the printed goal into a CORE lemma with:
  - UNIFORM NESTED-ATOMIC point spellings everywhere ((F).obj ((G).obj Z)), never composites;
    the exact-plug bridges those defeq (that is what the 800k heartbeats pays for);
  - the goal's paren-groups preserved verbatim in the statement.

CORE proof toolkit (in reliability order):
  1. haves: hw := Cat.Hom₂.congr_app (c.2.<axiom> ...) pt; hnn := congr_app of
     naturality_naturality; hs := (iso).inv/hom.toNatTrans.naturality m with defeq
     re-spelled ascription (+ .symm when orientation flips); iso cancellation is MATHLIB
     (golf b86e6db): c1 := Cat.Hom.inv_hom_id_toNatTrans_app e pt, and the c1'-shaped
     `inv ≫ hom ≫ m = m` is Cat.Hom.inv_hom_id_toNatTrans_app_assoc e pt m directly
     (hom_inv_id variants exist too) — no more toNatIso incantations or c1' microproofs.
  2. congrArg-LIFT squares through functors: hG := congrArg (fun m ↦ (F).toFunctor.map m) h;
     simp only [Functor.map_comp] at hG  — then rewrite WHOLE slice windows: slice_rhs i j => erw [hG].
     Window numbering is erratic near groups: iterate empirically, one window per compile.
  3. When window games stall: simp only [← Functor.map_comp] to fold everything into
     paired Gη-args, then ONE bridging `have key : <transcribed pair> = <target pair>` proved by
     `rw [← Functor.map_comp, ← Functor.map_comp]; refine congrArg _ ?_; rw [Category.assoc];
     erw [c1']; rfl`, then `erw [key]; erw [Category.assoc]; rfl`. This closed whisker_right.
  4. reassoc_of% is BROKEN here (its internal assoc-normalization fails on composite-typed
     naturality endpoints) — hand-build assoc forms or use the key-bridge instead.

## Remaining three: expected ingredients
- map₂_associator: c.2.map₂_associator + mapComp_assoc_left/right_hom_app + two nn-squares.
  Biggest of the three (goal has THREE mapComp pastings).
- map₂_left_unitor / right_unitor: c.2.map₂_left/right_unitor + mapComp_id_left/right_hom_app +
  naturality_id-style degeneration. Should be smaller than the whisker pair.
- The autoparam lurkers map₂_id/map₂_comp of evaluation' still pass (verify per build).

## PHASE 1 COMPLETE (2026-07-19, commit 8a40cc9)
map₂_associator CLOSED via evaluation_associator_core. Ledger 12 → 10 warning-decls
(11 explicit sorries; one HIDDEN sorry_if_sorry site in the unit/counit cluster now
discharges honestly — hidden count 5 → 4). Proof architecture (beyond the template):
- LHS: product-α factors are rfl-trivial ((α_ f g h).hom.1 = (α_ f.1 g.1 h.1).hom := rfl;
  .hom.2.as.app a.1 |>.app Z = 𝟙 := rfl), then hw := congr_app (d.2.map₂_associator) at Zfgh.
- naturality_comp_inv_app is ALREADY point-atomized (to_app) — rw fires directly.
- categoryStruct_comp_naturality_hom must be used RAW: dsimp at it DESTROYS it (defeq
  simps-equation — dsimp unfolds LHS into RHS). rw the goal, distribute afterwards.
- THE KEY MOVE: whole-goal `show` re-spelling after the lemma-rewrites (mixed instance
  paths block all ← Functor.map_comp folding; the show re-elaborates every node uniformly).
- Then: fold cascade (first|rw|erw menus), inv_hom_id_toNatTrans_app(_assoc) cancellations,
  key1 = hng.inv naturality slide at m := (g-nat f).inv.app Zf, key2 = mapComp_d(g,h).inv
  naturality slide at (n ≫ Hb.map m), final rfl. Forward map_comp splits create GROUPED
  pairs — simp only [Category.assoc] after, before the next erw.
- Erosion loops strip defeq-𝟙 α-components INSIDE composite args (load-bearing beyond
  eqToHom cleanup — removing the iterate changes downstream match shapes).
NEXT: Phase 2 (forwards coherence ×3, naturality_id first via catLift_hom₂_ext descent —
see forwards_naturality_wip.md), Phase 3 backwards ×3, Phase 4 pairing (probe blast radius
first), Phase 5 unit/counit rebuild (now 4 hidden sites), Phase 6 axiom check.
