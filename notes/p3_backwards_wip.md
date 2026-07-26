# P3 backwards coherence — WIP (resume here)

Close the three `yonedaLemmaBackwards` coherence obligations. **`naturality_naturality` is DONE**
(in Basic.lean, green). Remaining: `naturality_id`, `naturality_comp`.

## ✅ naturality_naturality — COMPLETE (2026-07-26)

Ported to Basic.lean and verified (full `lake build`, 6 sorries remain, was 7). Three pieces:

1. **`back_map_comp`** (Basic ~1832) — the lift-plumbing `rfl` reduction for the backwards
   functor's `.map` component (state `m` generic so the def's `rcases` fires; apply with **`erw`**).
2. **`backwards_naturality_naturality_core`** (Basic ~1842) — the reduced fibre-morphism core.
   **Winning idea:** use the *composite* 2-cell `θ = η.1 ▷ ZZ.op` to linearize into a 3-slide chain:
   - `hmc` = `b.2.toOplax.mapComp_naturality_left η.1 ZZ.op` → `hmc_inv` (inverse form via
     `Iso.comp_inv_eq`/`Iso.eq_inv_comp` + `hmc.symm`).
   - `hnn` = `g.2.naturality_naturality (η.1 ▷ ZZ.op)` → `hnn_inv` (same iso-flip pattern).
   - `hmod` = `modification_naturality_app η.2 (f.1 ≫ ZZ.op) x` → `hmod_inv`.
   - `hMCinv` = `(b.2.mapComp f.1 ZZ.op).inv.toNatTrans.naturality P` (front point-transport F↔G).
   - `hη2` = `(η.2.as.app γ).toNatTrans.naturality (a₂θ'.app x)` (auto-bridges the `op2(ZZ◁η.1)`
     vs `η.1▷ZZ.op` spelling — they're defeq via `op2_whiskerLeft`, closes by final `rfl`).
   Chain: `rw [Functor.map_comp]; erw [Category.assoc, reassoc_of% hmc_inv, Category.assoc, hnn_inv]`
   then `erw [reassoc_of% hMCinv, reassoc_of% hmod_inv, Category.assoc, ← hη2, ← Category.assoc]; rfl`.
   **Diamond note:** the fibre `≫`/`Category.assoc` do NOT fire at reducible transparency —
   MUST use `erw` (default transparency), not `slice`/`rw`/`simp only [Category.assoc]`.
3. **The field** (Basic ~1928) — descent (`Cat.Hom₂.ext_app; obtain ⟨x⟩; simp; homCategory.ext;
   erw homCategory_comp_as_app ×2; Cat.Hom₂.ext_app; intro ZZ; dsimp backwardsNaturalityIso; simp;
   erw back_map_comp; dsimp yonedaPairing/yonedaPairingMap₂/…; reduce`) then
   `exact backwards_naturality_naturality_core η x ZZ`.

This is the **reusable template** for id/comp: same descent + `back_map_comp`, then a core lemma
that bottoms out in an ALREADY-PROVEN object-level coherence.

## ⬜ naturality_id (Basic ~1963) — descent works, needs reduction pass

Object-level core ALREADY proven: **`mapComp_id_component`** (Basic ~1431). The field should
reduce to it (mirror how forwards `naturality_id` (Basic ~1371) uses `forwards_naturality_id_core`).

Verified descent prefix (compiles to the goal below):
```lean
  naturality_id a := by
    apply Cat.Hom₂.ext_app
    intro X
    obtain ⟨x⟩ := X
    simp only [Cat.Hom.toNatTrans_comp, NatTrans.comp_app, Cat.whiskerLeft_toNatTrans,
      Cat.whiskerRight_toNatTrans, whiskerLeft_app, whiskerRight_app, yonedaEvaluation_mapId_app_down,
      Cat.Hom.isoMk_hom, Cat.toCatHom₂_toNatTrans, NatIso.ofComponents_hom_app,
      homCategory_comp_as_app, Iso.trans_hom, Iso.symm_hom,
      Cat.leftUnitor_hom_toNatTrans_app, Cat.rightUnitor_inv_toNatTrans_app]
    apply homCategory.ext
    intro γ
    erw [homCategory_comp_as_app, homCategory_comp_as_app]
    apply Cat.Hom₂.ext_app
    intro ZZ
    -- GOAL (verified):
    --   (backwardsNaturalityIso (𝟙 a) {down:=x}).hom.as.app γ
    --     ≫ (postcompId₂ (unop a.1) ▷ᵢ (S ≫ 𝟙 a.2)).hom.as.app γ
    --     ≫ (bicategoricalIso S (𝟙 (yoneda₀ …) ≫ S ≫ 𝟙 a.2)).symm.hom.as.app γ ).toNatTrans.app ZZ
    --   = ((yonedaLemmaBackwardsFunctor a).map {down := (yonedaEvaluation'.mapId a).hom.app x}
    --       ≫ 𝟙 ≫ 𝟙).as.app γ .toNatTrans.app ZZ
    --   where S = (yonedaLemmaBackwardsFunctor a).obj {down:=x}
    sorry
```
**Next moves:** (1) RHS: distribute `.as.app γ` over the modification `≫` with
`erw [homCategory_comp_as_app, homCategory_comp_as_app]`, kill the `𝟙.as.app` (identity lemma),
then `erw [back_map_comp]` → `(a.2.map ZZ.op).map ((a.2.mapId a.1).hom.app x)`. (2) LHS: distribute
`.toNatTrans.app ZZ` over `≫` (`Cat.Hom.toNatTrans_comp, NatTrans.comp_app`), reduce
`backwardsNaturalityIso (𝟙 a)` (via `backwardsNaturalityIsoApp`, its hom = `mapComp(𝟙,ZZ.op).inv ≫
nat(𝟙≫ZZ.op).inv`), and reduce **`postcompId₂`** (Basic ~204, `postcomp₂ (𝟙 a) ≅ 𝟙`) and
**`bicategoricalIso`** (structural associator/unitor iso — components are `𝟙` via the ForMathlib
strictness lemmas + `bicategory`). (3) State a core = reduced goal, prove via `mapComp_id_component`
(+ the `mapId`/unitor coherence `Pseudofunctor.mapComp_id_right_hom`, already wrapped in that lemma).

## ⬜ naturality_comp (Basic ~1964) — same template

Object-level core ALREADY proven: **`mapComp_assoc_component`** (Basic ~1443). Mirror forwards
`naturality_comp` (Basic ~1391 → `forwards_naturality_comp_core`). Descent identical to above but
with `yonedaEvaluation_mapComp_app_down` and `Cat.associator_{hom,inv}_toNatTrans_app` in the first
simp (cf. forwards ~1394-1399). Watch for `postcompComp₂` defeq-toxicity (the P4 perf wall) if it
surfaces. Reduces to `mapComp_assoc_component` (the associator coherence).

## Scaffolding available (all verified, in Basic.lean)
- `back_map_comp` (~1832), `backwards_naturality_naturality_core` (~1842) — reuse the descent.
- `mapComp_id_component` (~1431), `mapComp_assoc_component` (~1443) — the object-level targets.
- `backwardsNaturalityIsoApp` (~1643): `.hom = mapComp(f.1,X.op).inv ≫ nat(f.1≫X.op).inv`.
- ForMathlib strictness lemmas (`Cat.{leftUnitor,rightUnitor,associator}_*_toNatTrans_app = 𝟙`).
- Diamond discipline: `erw` for fibre `≫`/assoc; `reassoc_of%` for non-terminal slides.
