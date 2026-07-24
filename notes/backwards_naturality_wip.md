# DONE 2026-07-16: cluster closed and integrated (see memory). Kept for the technique log.

# WIP: yonedaLemmaBackwards naturality — the last 2 sorries of cluster (2026-07-16)

Status: ~80% architected. Basic.lean is at green baseline (15 sorries). All work lives in
`Probe_backwards_naturality.lean` (this directory) — restore it to `Biyoneda/Probe.lean` and
iterate with `lake env lean Biyoneda/Probe.lean`.

## Verified architecture (all plugs typecheck!)

Four module-level declarations, to be inserted before `yonedaLemmaBackwards`:

1. `backwardsNaturalityIsoApp f X α` — **DONE, compiles.** The per-α component iso
   (mapComp.symm ≪≫ naturality.symm), with the inner naturality proof ported from the old
   inline field (uses `ULift.down X`, the big dsimp list, `erw [Pseudofunctor.map₂_whisker_left]`,
   `exact backwards_inner_component f h (ULift.down X)`).
2. `backwards_square_component f X f₁ ZZ` (**lemma A′ — PROVEN 2026-07-16**, via
   `backwards_square_core` (also proven; the real math). Core proof recipe: two goal-level
   `Iso.inv_comp_eq` flips (on `(Cat.Hom.toNatIso …).app` isos), `rw [naturality_naturality_hom_app,
   naturality_comp_hom_app]`, `simp only [Category.assoc]`, `erw [reassoc_of% mapComp_assoc_right_hom_app]`,
   then the KEY move — collapse the substituted chain back to one atom with `erw [← hN]` where
   `hN := h1; rw [h2] at hN; simp only [Category.assoc] at hN` (dodges ALL cross-paren association,
   which is motive-broken here), then cascade `erw [reassoc_of% h1/c1/h2/c2]`,
   `rw [← Functor.map_comp, ← Functor.map_comp]`, `erw [reassoc_of% c3]; erw [c4];
   erw [Functor.map_id]; erw [Category.comp_id]; rfl`. c1 = map₂-pair cancellation via
   `← Cat.Hom₂.comp_app, ← PrelaxFunctor.map₂_comp, Iso.hom_inv_id, map₂_id, Cat.Hom₂.id_app`;
   c2-c4 = `((Cat.Hom.toNatIso …).app …).inv_hom_id/hom_inv_id` defeq-plugs.
   `set_option maxHeartbeats 1600000 in` (BEFORE the docstring) needed. Point-level square whose middle atom is spelled
   `((postcomp₂ f.1.unop ≫ (yonedaLemmaBackwardsFunctorObj a X ≫ f.2)).naturality f₁).hom
   .toNatTrans.app ZZ` — VERIFIED defeq to `yonedaPairing.map`'s literal pasting: the plug
   `exact backwards_square_component f X f₁ ZZ` closes goal A after
   `apply Cat.Hom₂.ext_app; intro ZZ;` + the compact simp only
   `[Cat.Hom.toNatTrans_comp, NatTrans.comp_app, Cat.whiskerLeft_toNatTrans,
   Cat.whiskerRight_toNatTrans, whiskerLeft_app, whiskerRight_app]`.
3. `backwardsNaturalityIso f X` — **DONE, compiles** (StrongTrans.isoMk of 1 + 2).
4. `backwards_naturality_iso_natural f f₁` (**lemma B — sorried, not yet attacked**).
   Goal B (outer ofComponents naturality). Descent that worked in-place:
   `rcases X/Y/f₁; apply homCategory.ext; intro γ; apply Cat.Hom₂.ext_app; intro ZZ` —
   NOTE the in-place heavy descent hit whnf timeout; do it on the module lemma instead,
   expect the same texture as A′ (probably needs its own A″-style composite spelling).

Field replacement (verified elaborates):
```
naturality {a b} f :=
  Cat.Hom.isoMk (NatIso.ofComponents (fun X ↦ backwardsNaturalityIso f X)
    (fun {X Y} f₁ ↦ backwards_naturality_iso_natural f f₁))
```

## CRITICAL consequence of integrating (measured, not speculative)

Swapping the inline field for the named construction **breaks the 3 StrongTrans coherence
autoparams** of `yonedaLemmaBackwards` (naturality_naturality / naturality_id /
naturality_comp) — they currently pass ONLY via `sorry_if_sorry` (literal sorries in the old
inline goals). With named sorried lemmas the goals no longer contain `sorry` and aesop fails
(+ one whnf timeout at 400k heartbeats on naturality_comp). Integration therefore must write
these 3 fields explicitly (`:= by trace_state; sorry`, capture, downgrade) — sorry count
15 → 18 with 2 closed and 5 surfaced. Same event as yonedaLemmaForwards earlier.

## Proving A′ — exact plan (the distribution problem is SOLVED in principle)

- `simp only [categoryStruct_comp_naturality_hom, ...]` unfolds both vcomp pastings into
  named atoms (fires fine in the clean lemma context; it's the `@[simps!]` lemma from
  `Pseudofunctor.StrongTrans.categoryStruct`).
- Point-distribution over the pasting is blocked at reducible transparency —
  **`erw?` diagnosis**: `(StrongTrans.toOplax ... .vcomp ...).app` vs `(≫).app` endpoints,
  defeq only at default transparency. So each distribution step needs `erw`, NOT simp.
- **Do NOT use `repeat first | erw [...] | ...`** — the final all-fail round costs an
  isDefEq timeout on the big goal (observed at 200k heartbeats). Use a bounded, ordered erw
  list following the pasting structure: 4× `Cat.Hom₂.comp_app` (top level), then per factor:
  `Cat.associator_inv_app` / `Cat.whiskerRight_app` / `Cat.associator_hom_app` /
  `Cat.whiskerLeft_app` (which exposes the inner block at `(pc.app a₁).obj ZZ`), then 4× more
  `comp_app` + the inner factors, finishing `simp only [eqToHom_refl, Category.comp_id,
  Category.id_comp]`.
  ALTERNATIVE (maybe cheaper): the entire point-evaluation is a single defeq — try
  `calc LHS = <hand-written distributed form> := rfl` and prove the distributed equation.
- Distributed LHS atoms (T := yonedaLemmaBackwardsFunctorObj a X, pt := (f.2.app a.1).obj X↓,
  W := (postcomp₂ f.1.unop).app a₁ |>.obj ZZ i.e. ZZ ≫ f.1.unop up to op-dressing):
  1. `(b.2.mapComp f.1 (ZZ.op ≫ f₁)).inv.app pt ≫ (f.2.naturality (f.1 ≫ ZZ.op ≫ f₁)).inv.app X↓`
  2. `(S.app b₁).map` of postcomp₂-naturality component = image of an associator 2-cell of B
     (`associatorNatIsoMiddleCat_hom_toNatTrans_app`; component at ZZ is `(α_ f₁.unop ZZ f.1.unop).hom`
     up to op-dressing — TRANSCRIBE FROM TRACE, don't trust this by hand)
  3. `(f.2.app b₁).map ((a.2.mapComp W.op f₁).hom.app X↓)`  (T's naturality component)
  4. `(f.2.naturality f₁).hom.app ((a.2.map W.op).obj X↓)`
  = RHS: `(b.2.mapComp ZZ.op f₁).hom.app ((b.2.map f.1).obj pt) ≫ (b.2.map f₁).map (…inv ≫ …inv)`.
- Assembly ingredients (all point forms EXIST, verified by #check):
  `naturality_comp_hom_app` (for f.1 ≫ ZZ.op ≫ f₁ decomposition — THE key square),
  `naturality_naturality_hom_app` (associator 2-iso relating the two composites),
  `mapComp_assoc_*_hom_app` for b.2 on (f.1, ZZ.op, f₁), plus the Iso quartet
  (`Iso.comp_inv_eq`/`Iso.eq_inv_comp` + `erw [Category.assoc]` in Cat-fibres) as in
  `backwards_inner_component`.

## Tools that made this tractable (from the metaprogramming research)

- `erw?` (`import Mathlib.Tactic.ErwQuestion`) — names the blocking subterm; used twice.
- `@[simps!]`-generated names discovered by env-scan `run_cmd` (see skill
  references/metaprogramming.md): `categoryStruct_comp_naturality_hom`,
  `associatorNatIsoMiddleCat_hom/inv_toNatTrans_app`.
