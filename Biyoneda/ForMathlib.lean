import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Bicategory.Yoneda

/-!
# Lemmas staged for upstreaming to Mathlib

This file collects general-purpose lemmas about Mathlib's own definitions that are missing
upstream and that we need here. Nothing in this file mentions the bicategorical-Yoneda
development; everything is about `CategoryTheory.Cat` and the bicategory of categories.
Keeping them here (rather than inline in `Biyoneda/Basic.lean`) makes them easy to lift into a
Mathlib PR later, and lets the whole project share one canonical simp-normal form.

(No copyright header yet — the repository has no LICENSE; add the Apache-2.0 header before any
actual PR.)

## `Cat` is strict: coherence 2-cells are the identity

`Cat` is a `Bicategory.Strict` (functor composition is *definitionally* associative and unital),
so the associator and unitor `2`-morphisms are literally identity natural transformations. Mathlib
states their component lemmas (`Cat.associator_hom_app`, `Cat.leftUnitor_hom_app`, …) as
`eqToHom (by simp)`, whose proof is `rfl` only at **default** transparency — so `simp`
(which matches at *reducible* transparency) cannot fire `eqToHom_refl` on them, and proofs are
forced onto slow `erw`. The lemmas below give `𝟙` directly (each holds by `rfl`), so `simp` can do
the coherence cleanup that `erw` used to. They are the correct `@[simp]` normal form for a strict
bicategory and are the natural thing to upstream (ideally by making the existing Mathlib lemmas
produce `𝟙`).

**`@[simp]` note.** For an actual Mathlib PR these should be `@[simp]`. Here we deliberately leave
them un-tagged and use them *explicitly* in the proofs that need them: tagging them `@[simp]`
globally adds a match attempt to every bare `simp`/`dsimp` across the 2000-line development for a
tiny per-call cost that, summed over the file, can outweigh the local wins. Keeping them opt-in
makes each golf a guaranteed *localized* net improvement. Flip them to `@[simp]` at upstream time.
-/

open CategoryTheory Bicategory

namespace CategoryTheory.Cat

variable {B C D E : Cat}

theorem associator_hom_toNatTrans_app (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E) (X : B) :
    (α_ F G H).hom.toNatTrans.app X = 𝟙 _ := rfl

theorem associator_inv_toNatTrans_app (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E) (X : B) :
    (α_ F G H).inv.toNatTrans.app X = 𝟙 _ := rfl

theorem leftUnitor_hom_toNatTrans_app (F : B ⟶ C) (X : B) :
    (λ_ F).hom.toNatTrans.app X = 𝟙 _ := rfl

theorem leftUnitor_inv_toNatTrans_app (F : B ⟶ C) (X : B) :
    (λ_ F).inv.toNatTrans.app X = 𝟙 _ := rfl

theorem rightUnitor_hom_toNatTrans_app (F : B ⟶ C) (X : B) :
    (ρ_ F).hom.toNatTrans.app X = 𝟙 _ := rfl

theorem rightUnitor_inv_toNatTrans_app (F : B ⟶ C) (X : B) :
    (ρ_ F).inv.toNatTrans.app X = 𝟙 _ := rfl

end CategoryTheory.Cat
