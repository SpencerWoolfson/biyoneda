/-
Copyright (c) 2026 Spencer Woolfson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Spencer Woolfson
-/
import Mathlib.CategoryTheory.Bicategory.Product
import Mathlib.CategoryTheory.Bicategory.Opposites
import Mathlib.CategoryTheory.Bicategory.Yoneda
import Mathlib.Tactic.CategoryTheory.Bicategory.Basic
import Biyoneda.ForMathlib

/-!
# Gadgets for building `yonedaPairing` as a composite

**Status: work in progress. `Pseudofunctor.prod` is complete; `op` and `homPseudo` are not.
This file is NOT imported by `Biyoneda.Basic` — nothing depends on it yet.**

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

## Current status

| gadget | state |
|---|---|
| `Pseudofunctor.prod` | **complete, no sorries** — all five coherence fields auto-discharged |
| `Pseudofunctor.op` | data complete; four of five coherence fields auto-discharged, `map₂_associator` open |
| `homPseudo` | `obj`/`map`/`map₂` typecheck; `mapId`, `mapComp` and all coherence open |

The `prod` result is the important one: it confirms the premise of this whole file. When the data
is assembled from existing gadgets, the coherence really does come for free.

## What Mathlib's `Bicategory/Yoneda.lean` teaches (read it before continuing)

That file builds the *one-variable* hom-pseudofunctor, so it is the direct template here.

1. **Express `map`/`map₂` through `precomposingCat` / `postcomposingCat`** rather than building
   a `NatTrans` by hand (`fconstructor`, then `app` and `naturality` separately) — the packaged
   functors already carry the naturality. Mathlib additionally routes this through
   `PrelaxFunctor.mkOfHomFunctors`, which derives `map₂_id` and `map₂_comp` for free and is why
   `yoneda₀` is four lines; `homPseudo` below writes the fields directly instead and therefore
   owes those two proofs.
2. **The building blocks all exist**: `precomposingCat`, `postcomposingCat` (the functors),
   `leftUnitorNatIsoCat` / `rightUnitorNatIsoCat` (for `mapId`), and
   `associatorNatIsoRightCat` / `associatorNatIsoLeftCat` / `associatorNatIsoMiddleCat`
   (for `mapComp`). `associatorNatIsoMiddleCat` is the pre/post **exchange** — precisely the
   extra coherence a two-variable hom needs that a one-variable hom does not.
3. **Nearly every definition there carries
   `set_option backward.isDefEq.respectTransparency false in`.** That is not incidental; expect
   to need it here too (it is already on `homPseudo` below).

## The decision point

Finish `homPseudo` and stop at its coherence fields. If they close with `cat_disch` /
`bicategory` (possibly after a normalising `dsimp`), continue and wire everything together.
If instead they need bespoke `erw` chains of the kind in `evaluation_associator_core`, the
composite route costs *more* than the hand-rolled `yonedaPairing` it would replace — stop there.

Evidence so far points the right way: `prod` closed completely on autoparams, and `op` closed
four fields of five.

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

/-! ### Gadget 1 — the product of two pseudofunctors (COMPLETE)

Every field is the corresponding pair of fields of `F` and `G`, and the coherence obligations
reduce componentwise — all five are discharged by the autoparams with no help.
-/

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]
variable {D : Type u₃} [Bicategory.{w₃, v₃} D] {E : Type u₄} [Bicategory.{w₄, v₄} E]

/-- The product of two pseudofunctors, `F.prod G : B × D ⥤ᵖ C × E`.

The bicategorical analogue of `CategoryTheory.Functor.prod`. All coherence is inherited: the
hom-categories of a product bicategory are products, so each obligation is a pair of the
corresponding obligations for `F` and `G`, and `cat_disch` closes them componentwise. -/
def prod (F : B ⥤ᵖ C) (G : D ⥤ᵖ E) : B × D ⥤ᵖ C × E where
  obj p := (F.obj p.1, G.obj p.2)
  map {p q} fg := (F.map fg.1, G.map fg.2)
  map₂ {p q fg fg'} η := (F.map₂ η.1, G.map₂ η.2)
  mapId p := Iso.prod (F.mapId p.1) (G.mapId p.2)
  mapComp fg gh := Iso.prod (F.mapComp fg.1 gh.1) (G.mapComp fg.2 gh.2)

/-! ### Gadget 2 — the opposite of a pseudofunctor (one field open)

`Bicategory.Opposite` (`Bᵒᵖ`) reverses 1-morphisms and keeps 2-morphisms; the plumbing is
`op`/`unop` on objects, `Quiver.Hom.op`/`.unop` on 1-cells, and `op2`/`.unop2` on 2-cells
(`Mathlib/CategoryTheory/Bicategory/Opposites.lean`).

Note the variance: `mapComp` flips, because `f ≫ g` in `Bᵒᵖ` is `g ≫ f` in `B` — hence the
argument swap below.
-/

/-- The opposite of a pseudofunctor, `F.op : Bᵒᵖ ⥤ᵖ Cᵒᵖ`.

The data is a direct transport of `F` along `op`/`unop`. Four of the five coherence fields are
discharged by the autoparams; only `map₂_associator` is open, because the associator in `Bᵒᵖ` is
the `B` associator read backwards and the translation is not definitional. -/
def op (F : B ⥤ᵖ C) : Bᵒᵖ ⥤ᵖ Cᵒᵖ where
  obj x := Opposite.op (F.obj (unop x))
  map f := (F.map f.unop).op
  map₂ η := op2 (F.map₂ η.unop2)
  mapId x := Iso.op2 (F.mapId (unop x))
  mapComp f g := Iso.op2 (F.mapComp g.unop f.unop)
  map₂_associator f g h := by
    -- The `Bᵒᵖ` associator is the `B` associator read backwards, so this should follow from
    -- `F.map₂_associator` on the unopped 1-cells (note the reversed argument order), after
    -- translating the structural 2-cells with `op2_associator` / `op2_whiskerLeft` /
    -- `op2_whiskerRight` and stripping `op2` with `unop2_op2`.
    have h' := F.map₂_associator h.unop g.unop f.unop
    obtain ⟨f⟩ := f
    obtain ⟨g⟩ := g
    obtain ⟨h⟩ := h
    dsimp at h'
    sorry

end CategoryTheory.Pseudofunctor

namespace CategoryTheory.Bicategory

/-! ### Gadget 3 — the two-variable hom-pseudofunctor (in progress)

`homPseudo B : Bᵒᵖ × B ⥤ᵖ Cat`, sending `(a, b)` to the hom-category `unop a ⟶ b`, and a 1-cell
`(f, g)` to `h ↦ f ≫ h ≫ g` (precompose, then postcompose).

Fields are written out directly. `map` and `map₂` use Mathlib's packaged `precomposingCat` /
`postcomposingCat` functors, so their naturality is inherited rather than hand-proved.
-/

variable (B : Type u₁) [Bicategory.{w₁, v₁} B]

set_option backward.isDefEq.respectTransparency false in
/-- The two-variable hom-pseudofunctor `Bᵒᵖ × B ⥤ᵖ Cat`, `(a, b) ↦ (unop a ⟶ b)`.

The bicategorical analogue of `CategoryTheory.Functor.hom : Cᵒᵖ × C ⥤ Type v`.

The fields are written out directly rather than going through
`PrelaxFunctor.mkOfHomFunctors`.  That constructor would derive `map₂_id` and `map₂_comp` for
free (it is how Mathlib's `yoneda₀` gets them), so writing the fields explicitly means owing
those two proofs as well — the trade is that the definition stays readable and each field is
independently inspectable.

`obj`, `map` and `map₂` are verified to typecheck.  Remaining work, in order:

1. **`map₂_comp`** — exactly the **interchange law**.  Writing `A` for `(precomposingCat ..).map`
   and `B` for `(postcomposingCat ..).map`, the goal is
   `A (η ≫ θ).1.unop2 ▷ _ ≫ _ ◁ B (η ≫ θ).2`
   `= (A η.1.unop2 ▷ _ ≫ _ ◁ B η.2) ≫ (A θ.1.unop2 ▷ _ ≫ _ ◁ B θ.2)`.
   It needs, in order: (i) expand `(η ≫ θ).1.unop2` and `(η ≫ θ).2` over the composite — this
   does **not** fire from `unop2_comp` alone, the product-bicategory projection `(η ≫ θ).1` has
   to be reduced first (`Bicategory.prod_comp_fst` / `prod_comp_snd`); (ii) `Functor.map_comp`,
   then `comp_whiskerRight` / `whiskerLeft_comp`; (iii) `Bicategory.whisker_exchange` to swap the
   two middle factors.  A bare `simp [whisker_exchange]` does not fire and `bicategory` rewrites
   the goal into an `Iso`-composite form without closing it, so (iii) wants a *positional*
   rewrite (`rw` at the right occurrence, or `slice`).
2. **`map₂_id`** — should be `Functor.map_id` on both halves, then the whiskerings of identities
   collapse (`id_whiskerRight`, `whiskerLeft_id`, `Category.comp_id`).
3. **`mapId`** — component at `h` is `ρ_ _ ≪≫ λ_ h` (verified to typecheck).  Mathlib's
   `leftUnitorNatIsoCat` / `rightUnitorNatIsoCat` are the packaged versions.
4. **`mapComp`** — a structural re-bracketing of `gh.1.unop ≫ fg.1.unop ≫ h ≫ fg.2 ≫ gh.2`.
   `bicategoricalIso _ _` FAILS here: the product/opposite projections `(fg ≫ gh).1.unop` are
   not in structural normal form, so `BicategoricalCoherence` cannot be synthesized.  Either
   normalise the projections first (`dsimp only [...]`) and retry, or assemble it from
   `associatorNatIsoRightCat` / `associatorNatIsoLeftCat` / `associatorNatIsoMiddleCat`.
5. **The five coherence fields** — the decision point (see the module docstring). -/
def homPseudo : Bᵒᵖ × B ⥤ᵖ Cat.{w₁, v₁} where
  obj p := Cat.of (unop p.1 ⟶ p.2)
  map {p q} fg :=
    (precomposingCat (unop q.1) (unop p.1) p.2).obj fg.1.unop ≫
      (postcomposingCat (unop q.1) p.2 q.2).obj fg.2
  map₂ {p q fg fg'} η :=
    (precomposingCat (unop q.1) (unop p.1) p.2).map η.1.unop2 ▷ _ ≫
      _ ◁ (postcomposingCat (unop q.1) p.2 q.2).map η.2
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
--     Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat) ⥤ᵖ (Bᵒᵖ ⥤ᵖ Cat)ᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat)      (Gadget 1, DONE)
-- ... ⋙ homPseudo (Bᵒᵖ ⥤ᵖ Cat) : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat) ⥤ᵖ Cat     (Gadget 3)
```

A universe check is also owed here: `Basic.lean`'s `yonedaPairing` lands in
`Cat.{max u (max v w), max u (max v w)}`, whereas `homPseudo` as stated lands in `Cat.{w₁, v₁}`.
Expect to need `catPseudoULift` in the composite, exactly as `yonedaEvaluation` does.
-/
