/-
Copyright (c) 2026 Spencer Woolfson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Spencer Woolfson
-/
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Bicategory.Yoneda
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo

/-!
# Lemmas staged for upstreaming to Mathlib

This file collects general-purpose lemmas about Mathlib's own definitions that are missing
upstream and that we need here. Nothing in this file mentions the bicategorical-Yoneda
development; everything is about `CategoryTheory.Cat` and the bicategory of categories.
Keeping them here (rather than inline in `Biyoneda/Basic.lean`) makes them easy to lift into a
Mathlib PR later, and lets the whole project share one canonical simp-normal form.

## Component lemmas for `Cat` 2-cells and modifications

`Cat.Hom₂.congr_app` / `Cat.Hom₂.ext_app` are the "2-cells are determined by their components"
pair, and `modification_naturality_app` is the point-level form of `Modification.naturality`.
All three are general facts about `Cat`-valued pseudofunctors, independent of this development.

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

open CategoryTheory Bicategory Pseudofunctor StrongTrans Functor

universe w v u₁ v₁ w₁

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

namespace CategoryTheory

/-- Equal 2-morphisms in `Cat` have equal components at every object. -/
lemma Cat.Hom₂.congr_app {C D : Cat} {F G : C ⟶ D} {η θ : F ⟶ G} (h : η = θ) (X : C) :
    η.toNatTrans.app X = θ.toNatTrans.app X := by rw [h]

/-- Two parallel 2-morphisms in `Cat` are equal if their components agree at every object. -/
lemma Cat.Hom₂.ext_app {C D : Cat} {F G : C ⟶ D} {η θ : F ⟶ G}
    (h : ∀ X, η.toNatTrans.app X = θ.toNatTrans.app X) : η = θ :=
  Cat.Hom₂.ext (NatTrans.ext (funext h))

/-- `NatTrans.toCatHom₂` and `.toNatTrans` are inverse: the underlying transformation of the
2-cell built from `η` is `η` again. -/
@[simp] lemma Cat.toCatHom₂_toNatTrans {C D : Type u₁} [Category.{v₁} C] [Category.{v₁} D]
    {F G : C ⥤ D} (η : F ⟶ G) : (NatTrans.toCatHom₂ η).toNatTrans = η := rfl

/-- Point-level form of `Modification.naturality` for `Cat`-valued pseudofunctors: the
naturality square of a modification, evaluated at an object of the fibre. -/
lemma modification_naturality_app {C : Type u₁} [Bicategory.{w₁, v₁} C]
    {F G : C ⥤ᵖ Cat.{w, v}} {η θ : F ⟶ G} (Γ : η ⟶ θ) {a b : C} (f : a ⟶ b)
    (z : ↑(F.obj a)) :
    (Γ.as.app b).toNatTrans.app ((F.map f).toFunctor.obj z) ≫
      (θ.naturality f).hom.toNatTrans.app z =
    (η.naturality f).hom.toNatTrans.app z ≫
      (G.map f).toFunctor.map ((Γ.as.app a).toNatTrans.app z) := by
  simpa only [Cat.Hom.toNatTrans_comp, NatTrans.comp_app, Cat.whiskerLeft_toNatTrans,
    Cat.whiskerRight_toNatTrans, whiskerLeft_app, whiskerRight_app]
    using Cat.Hom₂.congr_app (Γ.as.naturality f) z

end CategoryTheory
