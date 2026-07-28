/-
Copyright (c) 2026 Spencer Woolfson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Spencer Woolfson
-/
import Mathlib.CategoryTheory.Bicategory.Product
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Bicategory.Opposites
import Mathlib.CategoryTheory.Bicategory.Yoneda
import Mathlib.Tactic.CategoryTheory.Bicategory.Basic
import Biyoneda.ForMathlib

/-!
# Gadgets for building `yonedaPairing` as a composite

**Status: `Pseudofunctor.prod` and `Pseudofunctor.op` are complete. `homPseudo` has a single
open obligation (the naturality square in `mapComp`). This file is NOT imported by
`Biyoneda.Basic` — nothing depends on it yet.**

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
| `Pseudofunctor.op` | **complete, no sorries** — four coherence fields auto-discharge; `map₂_associator` proved via `mapComp_assoc_left_inv` |
| `homPseudo` | prelax + `mapId` + `mapComp` data done; all five coherence fields close with `cat_disch`; only `mapComp`'s naturality square open |

Two of the three gadgets are finished, and the third is one square away. That confirms the
premise of this file: when the data is assembled from existing gadgets, the coherence really does
come for free.

The `op.map₂_associator` proof is worth reading as a pattern. 2-cells of `Cᵒᵖ` are `Hom2` records
with a single `unop2` field and **no registered `ext` lemma**, so descend with the injectivity of
`op2` instead (`op2_unop2` rewritten on both sides). That turns an opaque goal about opposite
2-cells into a clean statement in `C`, which is then exactly `mapComp_assoc_left_inv` followed by
`simp` to cancel the inverse pairs.

## What Mathlib's `Bicategory/Yoneda.lean` teaches (read it before continuing)

That file builds the *one-variable* hom-pseudofunctor, so it is the direct template here.

1. **Use `PrelaxFunctor.mkOfHomFunctors`, and make its hom-functor a composite.** The
   constructor derives `map₂_id` and `map₂_comp` from the hom-functor's own `map_id`/`map_comp`;
   building that hom-functor as a composite of existing functors means those two come for free
   as well. This is why `yoneda₀` is four lines, and it is what removed the interchange-law
   obligation here.
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

**The decision point has been answered: GO.** All five of `homPseudo`'s coherence fields
(`map₂_whisker_left`, `map₂_whisker_right`, `map₂_associator`, `map₂_left_unitor`,
`map₂_right_unitor`) close with a bare `cat_disch`, as does `map₂_id`. No bespoke `erw` chains
were needed anywhere. Together with `prod` closing completely and `op` closing four fields of
five, the "assemble from gadgets and inherit the coherence" premise holds.

What remains in `homPseudo` is *not* coherence: `mapComp`'s naturality (a `NatIso.ofComponents`
obligation for a hand-built associator chain) and `map₂_comp` (the interchange law). Both are
noted in detail at their sites.

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
    dsimp [op2]
    -- 2-cells of `Cᵒᵖ` are determined by their `unop2`, and `op2_unop2` gives the injectivity.
    have ext2 : ∀ {p q : Cᵒᵖ} {u v : p ⟶ q} (x y : u ⟶ v), x.unop2 = y.unop2 → x = y := by
      intro p q u v x y hxy
      rw [← Bicategory.Opposite.op2_unop2 x, ← Bicategory.Opposite.op2_unop2 y, hxy]
    apply ext2
    simp
    rw [F.mapComp_assoc_left_inv]
    simp


end CategoryTheory.Pseudofunctor

namespace CategoryTheory.Bicategory

/-! ### Gadget 3 — the two-variable hom-pseudofunctor (in progress)

`homPseudo B : Bᵒᵖ × B ⥤ᵖ Cat`, sending `(a, b)` to the hom-category `unop a ⟶ b`, and a 1-cell
`(f, g)` to `h ↦ f ≫ h ≫ g` (precompose, then postcompose).

The prelax part is built with `PrelaxFunctor.mkOfHomFunctors`, and its hom-functor is itself a
*composite of functors* (`unopFunctor ⋙ precomposingCat`, paired with `postcomposingCat`, then
uncurried composition). So `map`, `map₂`, `map₂_id` and `map₂_comp` are all inherited — including
the interchange law, which had been the sticking point when the fields were written out by hand.
-/

variable (B : Type u₁) [Bicategory.{w₁, v₁} B]

/-- The underlying prelax functor of `homPseudo`.

The hom-functor is assembled as a **composite of functors**, so `map_id` and `map_comp` — the
latter being the interchange law — are inherited rather than proved:

* `unopFunctor ⋙ precomposingCat` turns a 1-cell of `Bᵒᵖ` into precomposition;
* `postcomposingCat` turns a 1-cell of `B` into postcomposition;
* `Functor.prod` pairs them, and `CategoryTheory.Functor.uncurry.obj (precomposing ..)` composes the two
  resulting `Cat`-morphisms.
-/
def prelax : PrelaxFunctor (Bᵒᵖ × B) Cat.{w₁, v₁} :=
  PrelaxFunctor.mkOfHomFunctors
    (fun p => Cat.of (unop p.1 ⟶ p.2))
    (fun a b =>
      ((unopFunctor a.1 b.1 ⋙ precomposingCat (unop b.1) (unop a.1) a.2).prod
          (postcomposingCat (unop b.1) a.2 b.2)) ⋙
        Functor.uncurry.obj
          (precomposing (Cat.of (unop a.1 ⟶ a.2)) (Cat.of (unop b.1 ⟶ a.2))
            (Cat.of (unop b.1 ⟶ b.2))))

set_option backward.isDefEq.respectTransparency false in
/-- The two-variable hom-pseudofunctor `Bᵒᵖ × B ⥤ᵖ Cat`, `(a, b) ↦ (unop a ⟶ b)`.

The bicategorical analogue of `CategoryTheory.Functor.hom : Cᵒᵖ × C ⥤ Type v`.

Built on `prelax` above, so `map`, `map₂`, `map₂_id` and `map₂_comp` are all inherited — in
particular the interchange law, which is what `map₂_comp` amounts to, never has to be proved.

**All five coherence fields close with a bare `cat_disch`.** The only remaining obligation is the
naturality square inside `mapComp`; see the comment at that `sorry`. -/
def homPseudo : Bᵒᵖ × B ⥤ᵖ Cat.{w₁, v₁} where
  toPrelaxFunctor := prelax B
  mapId p := by
    rcases p with ⟨a, b⟩
    refine CategoryTheory.Cat.Hom.isoMk ?_
    refine NatIso.ofComponents ?_ ?_
    · intro h
      refine (ρ_ (𝟙 (unop a) ≫ h)) ≪≫ λ_ h
    · intros h h' η
      simp
  mapComp fg gh := by
    rcases fg with ⟨f, g⟩
    rcases gh with ⟨h, k⟩
    refine CategoryTheory.Cat.Hom.isoMk ?_
    refine NatIso.ofComponents ?_ ?_
    · intro l
      refine (α_ ((h.unop ≫ f.unop) ≫ l) g k).symm ≪≫ (?_  ▷ᵢ k)
      refine ?_ ≪≫ (α_ h.unop (f.unop ≫ l) g)
      exact (α_ h.unop f.unop l) ▷ᵢ g
    · intros l l' η
      -- OPEN — the only obligation left in this file.
      -- Naturality in `l` of the associator chain above. Tried and failed: `cat_disch`;
      -- `bicategory` (partially succeeds, leaves goals — so it is unsafe inside `first`);
      -- `simp [associator_naturality_{left,middle,right}, whisker_exchange]`, both before and
      -- after a `dsimp` that reduces the `prelax`-functor applications to whiskerings.
      sorry

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
