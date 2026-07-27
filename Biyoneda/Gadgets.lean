/-
Copyright (c) 2026 Spencer Woolfson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Spencer Woolfson
-/
import Mathlib.CategoryTheory.Bicategory.Product
import Mathlib.CategoryTheory.Bicategory.Opposites
import Mathlib.Tactic.CategoryTheory.Bicategory.Basic
import Biyoneda.ForMathlib

/-!
# Gadgets for building `yonedaPairing` as a composite

**Status: scaffolding. Everything here is deliberately `sorry`-ed — this file is a worklist,
not a result. It is NOT imported by `Biyoneda.Basic`; nothing depends on it yet.**

## Why this file exists

Mathlib's 1-categorical Yoneda builds both sides of the pairing as one-line composites of
existing gadgets, so functoriality is *inherited* rather than proved:

```lean
def yonedaEvaluation : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁) ⥤ Type max u₁ v₁ :=
  evaluationUncurried Cᵒᵖ (Type v₁) ⋙ uliftFunctor
def yonedaPairing : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁) ⥤ Type max u₁ v₁ :=
  Functor.prod yoneda.op (𝟭 _) ⋙ Functor.hom (Cᵒᵖ ⥤ Type v₁)
```

We already have the bicategorical analogue of the first line (`Biyoneda.Evaluation`,
`evaluationPseudo` = bicategorical `evaluationUncurried`; `catPseudoULift` = `uliftFunctor`).
The second line needs three gadgets that **do not exist in Mathlib** — as of v4.29.0,
`grep -r` over `Mathlib/CategoryTheory/Bicategory/` finds no `Pseudofunctor.prod`,
no `Pseudofunctor.op`, and no two-variable hom-pseudofunctor.

If they existed, `yonedaPairing` would collapse to a composite and its hand-rolled coherence
fields — including the parked `mapComp` `sorry` in `Basic.lean` — would disappear.

## Scoping already done (see `notes/hom_pseudofunctor_scoping.md`)

Verified by probe **before** writing this file:
* `homPseudo`'s `obj` and `map` typecheck exactly as written below;
* its `map₂` and `mapId` data assemble from `▷`/`◁` and `ρ_`/`λ_`;
* `mapComp` does **not** come for free — `bicategoricalIso` fails to synthesize
  `BicategoricalCoherence` because the product/opposite projections `(fg ≫ gh).1.unop` are not
  in structural normal form. It needs a `dsimp`/`show` normalisation first, or an explicit
  associator chain. **This is the main open risk.**

## The decision point

Fill in `homPseudo` first, and stop at its five coherence fields. If they close with
`cat_disch` / `bicategory` (possibly after a normalising `dsimp`), continue to `prod` and `op`.
If instead they need bespoke `erw` chains of the kind in `evaluation_associator_core`, the
composite route costs *more* than the hand-rolled `yonedaPairing` it would replace — stop there.

Strong precedent for optimism: Mathlib's own one-variable `yoneda₀` and `yoneda`
(`Bicategory/Yoneda.lean`) are four lines each with **every** coherence field auto-discharged,
and `associatorNatIsoMiddleCat` — the pre/post *exchange* — already exists, which is exactly the
extra coherence a two-variable hom needs.

## Where each piece would live upstream

| here | Mathlib home | 1-categorical analogue |
|---|---|---|
| `Pseudofunctor.prod` | `Bicategory/Product.lean` | `Functor.prod` |
| `Pseudofunctor.op` | `Bicategory/Opposites.lean` | `Functor.op` |
| `homPseudo` | new `Bicategory/Functor/Hom.lean` | `Functor.hom` (3 lines!) |
-/

open CategoryTheory Bicategory Bicategory.Opposite Opposite Pseudofunctor StrongTrans Functor
open scoped Pseudofunctor.StrongTrans

universe w₁ v₁ u₁ w₂ v₂ u₂ w₃ v₃ u₃ w₄ v₄ u₄

namespace CategoryTheory.Pseudofunctor

/-! ### Gadget 1 — the product of two pseudofunctors

The 1-categorical `Functor.prod` sends `(F, G)` to `F × G : B × D ⥤ C × E`. The bicategorical
version is the same on data; the work is the coherence, where every field is a *pair* of the
corresponding fields of `F` and `G`, so each obligation should reduce componentwise via
`Bicategory.prod_*_fst` / `prod_*_snd`.
-/

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]
variable {D : Type u₃} [Bicategory.{w₃, v₃} D] {E : Type u₄} [Bicategory.{w₄, v₄} E]

/-- The product of two pseudofunctors, `F.prod G : B × D ⥤ᵖ C × E`.

TODO. Data: `obj`/`map`/`map₂` are componentwise and should be immediate. `mapId`/`mapComp` are
isos in a product hom-category, i.e. pairs of isos — check whether Mathlib has an `Iso.prod` for
product *categories* (`CategoryTheory/Products/Basic.lean`) before hand-rolling one.
Coherence: each field should follow from `F`'s and `G`'s corresponding field after projecting
with `Bicategory.prod_*_fst` / `prod_*_snd`. -/
def prod (F : B ⥤ᵖ C) (G : D ⥤ᵖ E) : B × D ⥤ᵖ C × E := sorry

/-! ### Gadget 2 — the opposite of a pseudofunctor

`Bicategory.Opposite` (`Bᵒᵖ`) reverses 1-morphisms and keeps 2-morphisms; the relevant
plumbing is `op`/`unop` on objects, `Quiver.Hom.op`/`.unop` on 1-cells, and `op2`/`unop2` on
2-cells (`Mathlib/CategoryTheory/Bicategory/Opposites.lean`).

Note the variance: `mapComp` flips, because `(f ≫ g)` in `Bᵒᵖ` is `g ≫ f` in `B`.
-/

/-- The opposite of a pseudofunctor, `F.op : Bᵒᵖ ⥤ᵖ Cᵒᵖ`.

TODO. Data: `obj x := op (F.obj (unop x))`, `map f := (F.map f.unop).op`,
`map₂ η := op2 (F.map₂ η.unop2)`. `mapId` is `F.mapId` transported by `Iso.op2`; `mapComp f g`
is `F.mapComp g.unop f.unop` transported — mind the swap.
Coherence: the axioms in `Bᵒᵖ` are the `B` axioms read backwards; `op2_associator`,
`op2_leftUnitor`, `op2_rightUnitor`, `op2_whiskerLeft/Right` are the translation lemmas. -/
def op (F : B ⥤ᵖ C) : Bᵒᵖ ⥤ᵖ Cᵒᵖ := sorry

end CategoryTheory.Pseudofunctor

namespace CategoryTheory.Bicategory

/-! ### Gadget 3 — the two-variable hom-pseudofunctor

`homPseudo B : Bᵒᵖ × B ⥤ᵖ Cat`, sending `(a, b)` to the hom-category `unop a ⟶ b`, and a 1-cell
`(f, g)` to `h ↦ f ≫ h ≫ g` (precompose, then postcompose).

The `obj` and `map` fields below are **verified to typecheck** as written. The remaining fields
are the worklist.
-/

variable (B : Type u₁) [Bicategory.{w₁, v₁} B]

/-- The two-variable hom-pseudofunctor `Bᵒᵖ × B ⥤ᵖ Cat`, `(a, b) ↦ (unop a ⟶ b)`.

This is the bicategorical analogue of `CategoryTheory.Functor.hom : Cᵒᵖ × C ⥤ Type v`, which is
three lines in the 1-categorical case.

TODO, in this order (see the decision point in the module docstring):
1. `map₂` — component at `h` is `(η.1.unop2 ▷ h) ▷ fg.2 ≫ (fg'.1.unop ≫ h) ◁ η.2`
   (verified to typecheck); its `naturality` is `whisker_exchange`.
2. `mapId` — component at `h` is `ρ_ _ ≪≫ λ_ h` (verified to typecheck).
3. `mapComp` — a structural re-bracketing of `gh.1.unop ≫ fg.1.unop ≫ h ≫ fg.2 ≫ gh.2`.
   `bicategoricalIso _ _` FAILS here (see module docstring); build the associator chain by hand,
   or normalise the projections first with `dsimp only [...]` and retry the coherence tactic.
4. The five coherence fields — **this is the decision point**. Try `cat_disch` / `bicategory`
   first; all the 2-cells involved are structural, which is why Mathlib's one-variable
   `yoneda₀` gets them for free. -/
def homPseudo : Bᵒᵖ × B ⥤ᵖ Cat.{w₁, v₁} where
  obj p := Cat.of (unop p.1 ⟶ p.2)
  map {p q} fg := (precomp p.2 fg.1.unop ⋙ postcomp (unop q.1) fg.2).toCatHom
  map₂ {p q fg fg'} η := sorry
  mapId p := sorry
  mapComp fg gh := sorry
  map₂_id := by sorry
  map₂_comp := by sorry
  map₂_whisker_left := by sorry
  map₂_whisker_right := by sorry
  map₂_associator := by sorry
  map₂_left_unitor := by sorry
  map₂_right_unitor := by sorry

end CategoryTheory.Bicategory

/-! ## The target

Once the three gadgets above are in place, `yonedaPairing` should be definable as the composite
below rather than hand-rolled, and `Basic.lean`'s `yonedaPairing` (with its parked `mapComp`
`sorry`) can be retired.

Note the hom-pseudofunctor needed is that of the **functor bicategory** `K = Bᵒᵖ ⥤ᵖ Cat`, whose
hom-categories are `StrongTrans` with modifications as morphisms — so `precomp`/`postcomp` there
are whiskering of strong transformations. `homPseudo` is generic in its bicategory, so it
applies; but that is the heavier instance to test against, and it is worth checking `homPseudo`
on a small bicategory first.

Sketch (types not yet checked — fill in once the gadgets exist):

```lean
-- yoneda : B ⥤ᵖ Bᵒᵖ ⥤ᵖ Cat                                    (Mathlib, exists)
-- yoneda.op : Bᵒᵖ ⥤ᵖ (Bᵒᵖ ⥤ᵖ Cat)ᵒᵖ                            (Gadget 2)
-- (yoneda.op).prod (Pseudofunctor.id _) :
--     Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat) ⥤ᵖ (Bᵒᵖ ⥤ᵖ Cat)ᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat)      (Gadget 1)
-- ... ⋙ homPseudo (Bᵒᵖ ⥤ᵖ Cat) : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat) ⥤ᵖ Cat     (Gadget 3)
```

A universe check is also owed here: `Basic.lean`'s `yonedaPairing` lands in
`Cat.{max u (max v w), max u (max v w)}`, whereas `homPseudo` as stated lands in `Cat.{w₁, v₁}`.
Expect to need `catPseudoULift` in the composite, exactly as `yonedaEvaluation` does.
-/
