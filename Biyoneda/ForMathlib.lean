/-
Copyright (c) 2026 Spencer Woolfson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Spencer Woolfson
-/
module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Bicategory.Yoneda
public import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
public import Mathlib.Tactic.CategoryTheory.ToApp

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
so its associators and unitors are literally identity 2-cells. This file records that twice:
once at the level of 2-cells (`leftUnitor_hom_eq_id` and friends), which Mathlib does not state
at all — it has only the `Strict` instance, whose `associator_eqToIso` and friends route through
`eqToIso` — and once at the level of components (`leftUnitor_hom_toNatTrans_app` and friends),
where Mathlib's own `Cat.leftUnitor_hom_app` states `eqToHom (by simp)` instead of `𝟙`.

Each of ours holds by `rfl`. That is the case for upstreaming them: a `rfl` statement is
available to `dsimp`, to `change`, and to definitional reasoning, not only to `simp`. It is
also the form `to_app`'s cleanup pass is already trying to reach — `catAppSimp` lists the six
`Cat.*_app` lemmas followed by `eqToHom_refl`, `Category.comp_id` and `Category.id_comp`,
i.e. a pipeline whose job is to undo the `eqToHom` those lemmas introduce.

**Corrected 2026-09-06.** This section previously claimed that `simp` *cannot* fire
`eqToHom_refl` on Mathlib's form, forcing proofs onto `erw`. That is false and was never
measured: `(λ_ F).hom.toNatTrans.app X = 𝟙 _` closes by `simp` against the current lemmas. The
honest case is "strictly stronger, and `rfl`", not "the existing one is broken".

**`@[simp]` note.** Left un-tagged, and that is a measured decision rather than a local
convenience: on 2026-08-29, tagging the 2-cell forms globally shifted the simp normal form
enough to break an unrelated proof in this development. Mathlib's existing `Cat.*_app` lemmas
are not `@[simp]` either, so un-tagged also matches precedent. Any upstream version should stay
un-tagged, or be tagged only after benchmarking — do not flip them on the way out.

## `naturality_naturality`, solved for the whiskered `map₂`

`Pseudofunctor.StrongTrans.naturality_naturality_conj` states a strong transformation's naturality
at a 2-cell `σ` as a conjugation by its naturality isomorphisms. It is a 2-cell equation for any
target bicategory, and `@[to_app]` generates the component form for `Cat`-valued pseudofunctors,
which this development used to state and prove by hand at a point. Mathlib's closest lemma,
`StrongTrans.naturality_naturality_hom`, needs `σ` to be an isomorphism.

-/

@[expose] public section

open CategoryTheory Bicategory Pseudofunctor StrongTrans Functor

universe w v u u₁ v₁ w₁ u₂ v₂ w₂

namespace CategoryTheory.Cat

variable {B C D E : Cat}

/-! ### The same six, at the level of 2-cells

Mathlib has no 2-cell-level statement of `Cat`'s strictness at all -- only the `Strict`
instance, whose `associator_eqToIso` / `leftUnitor_eqToIso` / `rightUnitor_eqToIso` route
through `eqToIso`.  These are strictly stronger, hold by `rfl`, and are what makes a structural
block collapse in one `simp only`.

**Not `@[simp]`, and that is a measured decision** (2026-08-29): tagging them globally shifts
the simp normal form enough to break an unrelated proof in this development.  Any upstream
version should either stay un-tagged, matching the existing `Cat.leftUnitor_hom_app` and
friends, or be tagged only after benchmarking. -/

theorem leftUnitor_hom_eq_id {X Y : Cat.{v, u}} (f : X ⟶ Y) : (λ_ f).hom = 𝟙 f := rfl

theorem leftUnitor_inv_eq_id {X Y : Cat.{v, u}} (f : X ⟶ Y) : (λ_ f).inv = 𝟙 f := rfl

theorem rightUnitor_hom_eq_id {X Y : Cat.{v, u}} (f : X ⟶ Y) : (ρ_ f).hom = 𝟙 f := rfl

theorem rightUnitor_inv_eq_id {X Y : Cat.{v, u}} (f : X ⟶ Y) : (ρ_ f).inv = 𝟙 f := rfl

theorem associator_hom_eq_id {X Y Z W : Cat.{v, u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) :
    (α_ f g h).hom = 𝟙 _ := rfl

theorem associator_inv_eq_id {X Y Z W : Cat.{v, u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) :
    (α_ f g h).inv = 𝟙 _ := rfl

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

/-- `NatIso.naturality_1` for `Cat`-bundled 2-isomorphisms: conjugating a functor's action by a
2-isomorphism gives the other functor's action.  Mathlib's version does not apply directly because
`Cat`'s 1-morphisms are bundled (`Cat.Hom`), so its components go through `.toNatTrans.app`. -/
lemma Cat.naturality_1 {C D : Cat} {F G : C ⟶ D} (ι : F ≅ G) {X Y : ↑C} (m : X ⟶ Y) :
    ι.inv.toNatTrans.app X ≫ F.toFunctor.map m ≫ ι.hom.toNatTrans.app Y
      = G.toFunctor.map m :=
  NatIso.naturality_1 (Cat.Hom.toNatIso ι) m

/-- `NatIso.naturality_2` for `Cat`-bundled 2-isomorphisms. -/
lemma Cat.naturality_2 {C D : Cat} {F G : C ⟶ D} (ι : F ≅ G) {X Y : ↑C} (m : X ⟶ Y) :
    ι.hom.toNatTrans.app X ≫ G.toFunctor.map m ≫ ι.inv.toNatTrans.app Y
      = F.toFunctor.map m :=
  NatIso.naturality_2 (Cat.Hom.toNatIso ι) m

/-! ### The three `StrongTrans` coherence fields, at a point

Mathlib tags most bicategory coherence lemmas `@[to_app]`, which generates the component form
automatically — but the three `StrongTrans` structure fields are tagged only
`@[reassoc (attr := simp)]`, while the `whiskerLeft_`/`whiskerRight_` variants a few lines below
them in `Mathlib/CategoryTheory/Bicategory/NaturalTransformation/Pseudo.lean` *are* tagged
`to_app`.  That looks like an oversight rather than a decision.

Applying the attribute downstream works and produces exactly the three lemmas this development
had otherwise written by hand:

* `naturality_naturality_app` — was stated here explicitly;
* `naturality_id_app` — was `Bicategory.strongTrans_naturality_id_app` in `Evaluation.lean`,
  modulo `.symm`;
* `naturality_comp_app` — was `Bicategory.strongTrans_naturality_comp_hom_app`, modulo `.symm`,
  and that one needed a twenty-line proof writing `Cat`'s three associators in by hand and
  stripping them again.  `to_app`'s own cleanup pass does that work.

**Staged for upstream.** The proposed change is three names added to the existing `attribute`
line in Mathlib; when that lands, delete this block. -/

attribute [to_app] Pseudofunctor.StrongTrans.naturality_naturality
attribute [to_app] Pseudofunctor.StrongTrans.naturality_id
attribute [to_app] Pseudofunctor.StrongTrans.naturality_comp

/-- A strong transformation's naturality at a 2-cell `σ`, solved for the whiskered `map₂`: a
conjugation by the naturality isomorphisms. Unlike `StrongTrans.naturality_naturality_hom`, `σ`
need not be invertible. `@[to_app]` generates the component form for `Cat`-valued
pseudofunctors. -/
@[to_app]
lemma Pseudofunctor.StrongTrans.naturality_naturality_conj {B : Type u₁} [Bicategory.{w₁, v₁} B]
    {C : Type u₂} [Bicategory.{w₂, v₂} C] {F G : B ⥤ᵖ C} (α : F ⟶ G) {y z : B}
    {v v' : y ⟶ z} (σ : v ⟶ v') :
    F.map₂ σ ▷ α.app z = (α.naturality v).hom ≫ α.app y ◁ G.map₂ σ ≫ (α.naturality v').inv := by
  rw [← Category.assoc, Iso.eq_comp_inv]; exact α.naturality_naturality σ



/-- Taking the component at `b` is a functor from the hom-category of pseudofunctors `B ⥤ᵖ C`
(strong transformations and modifications) to the hom-category `F.obj b ⟶ G.obj b`.

This is the `Pseudofunctor` analogue of `CategoryTheory.evaluation`, and it is *strictly*
functorial: vertical composition of strong transformations and of modifications is both
computed componentwise, so both functor laws are `rfl`.  It is the second factor of
`Bicategory.evalHom`. -/
@[simps]
def Pseudofunctor.StrongTrans.appFunctor {B : Type u₁} [Bicategory.{w₁, v₁} B]
    {C : Type u₂} [Bicategory.{w₂, v₂} C] (F G : B ⥤ᵖ C) (b : B) :
    (F ⟶ G) ⥤ (F.obj b ⟶ G.obj b) where
  obj η := η.app b
  map Γ := Γ.as.app b

end CategoryTheory
