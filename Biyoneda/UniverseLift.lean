/-
Copyright (c) 2026 Spencer Woolfson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Spencer Woolfson
-/
import Mathlib.CategoryTheory.Category.ULift
import Biyoneda.ForMathlib

/-!
# Universe lifting for `Cat`

The bicategorical Yoneda lemma compares two pseudofunctors that naturally land in *different*
universes: `evaluationPseudo` lands in `Cat.{w, v}` while the pairing lands in
`Cat.{max u (max v w), max u (max v w)}`.  This file supplies the machinery that promotes the
smaller one, so the two can be compared.

* `catLift` — the strict functor `Cat.{v₁, u₁} ⥤ Cat.{max v₁ v₂, max u₁ u₂}`, sending `C` to
  `ULiftHom (ULift C)`, lifting both the object type and the hom-sets.
* `catPseudoULift` — the same as a *pseudofunctor* (its coherence isos are trivial, because
  `ULift`/`ULiftHom` are strictly functorial).
* `catLiftEquiv` — the equivalence `C ≃ catLift.obj (Cat.of C)`, witnessing that the lift is
  lossless; used to lower morphisms back through the lift.
* `catLift_hom₂_ext` / `catLift_hom₂_congr_down` — the "strip the plumbing" pair: 2-cells into a
  lifted category are determined by their unlifted components.

Nothing here mentions the Yoneda development; this is general `Cat` universe machinery and is a
candidate for upstreaming (Mathlib has `uliftFunctor` for `Type`, and this is its `Cat`
analogue).
-/

open CategoryTheory Bicategory Opposite Pseudofunctor StrongTrans Functor

universe u v w v₁ v₂ u₁ u₂

attribute [local instance] uliftCategory

/--
The `Category` instance on `ULiftHom.{v₂} (ULift.{u₂} C)`, which simultaneously lifts the
object universe from `u₁` to `max u₁ u₂` and the morphism universe from `v₁` to `max v₁ v₂`.

This is the category structure that `catLift` produces on objects; it is assembled by first
applying `uliftCategory` to get a `Category (ULift C)` and then `ULiftHom.category`.
-/
instance catPseudoULiftObjCategory (C : Type u₁) [Category.{v₁} C] :
    Category.{max v₁ v₂} (ULiftHom.{v₂} (ULift.{u₂, u₁} C)) :=
  ULiftHom.category (C := ULift.{u₂, u₁} C)

/--
The strict 1-functor `Cat.{v₁, u₁} ⥤ Cat.{max v₁ v₂, max u₁ u₂}` that promotes a small
category to a larger universe.

* **On objects**: `C ↦ ULiftHom (ULift C)`, lifting both the object type and the hom-sets.
* **On 1-morphisms**: given `F : C ⥤ D`, the lifted functor sends `⟨⟨x⟩⟩ ↦ ⟨F x⟩` and maps
  morphisms via `ULiftHom.up ∘ F.map ∘ ULiftHom.down`.

Because `ULift` and `ULiftHom` are both strictly functorial, no coherence isos are needed.
The pseudofunctor extension (with trivial coherence isos) is `catPseudoULift`.
-/
def catLift : Cat.{v₁, u₁} ⥤ Cat.{max v₁ v₂, max u₁ u₂} where
  obj C := Cat.of (ULiftHom.{v₂} (ULift.{u₂, u₁} C.α))
  map {C D} F :=
    Functor.toCatHom (ULiftHomULiftCategory.equivCongrLeft.toFun
      (ULiftHom.down ⋙ ULift.downFunctor ⋙ F.toFunctor))

/--
The equivalence of categories `C ≃ catLift.obj (Cat.of C)`.

This witnesses that universe-lifting is lossless: the original category `C` is equivalent to
its image under `catLift`, via the composite equivalence
  `C  ≃  ULift C  ≃  ULiftHom (ULift C)`
built from `ULift.equivalence` and `ULiftHom.equiv`.

Used in `yonedaLemmaBackwardsFunctor` to lower morphisms through the universe lift.
-/
def catLiftEquiv (C : Type u₁) [Category.{v₁} C] :
    Equivalence C (catLift.{v₁, v₂, u₁, u₂}.obj (Cat.of C)) :=
  (@ULift.equivalence.{v₁, u₁, u₂} C _).trans ULiftHom.equiv

/--
The pseudofunctor `Cat.{v₁, u₁} ⥤ᵖ Cat.{max v₁ v₂, max u₁ u₂}` that promotes every small
category to a larger universe.

* **On objects and 1-morphisms**: agrees with the strict functor `catLift`.
* **On 2-morphisms**: a natural transformation `η : F ⟶ G` is lifted by applying `ULiftHom.up`
  component-wise.
* **Coherence isos** (`mapId`, `mapComp`): both are `Iso.refl`, since `catLift` is strictly
  functorial and requires no non-trivial coherence.

This pseudofunctor is used to bring `yonedaEvaluation'` (which lands in `Cat.{w, v}`) up to
the universe `Cat.{max u (max v w), max u (max v w)}` required by `yonedaPairing`.
-/
def catPseudoULift : Cat.{v₁, u₁} ⥤ᵖ Cat.{max v₁ v₂, max u₁ u₂} where
  obj C := catLift.{v₁, v₂, u₁, u₂}.obj C
  map {C D} F := catLift.{v₁, v₂, u₁, u₂}.map F
  map₂ {C D} f {g} {η} := by
    refine { toNatTrans := { app := ?_, naturality := ?_ } }
    · intro x
      unfold catLift ULiftHom at x
      exact ULiftHom.up.map (η.toNatTrans.app x.down)
    · exact fun _ _ h ↦ Quiver.homOfEq_injective rfl rfl
        (congrArg (ULiftHom.up.map) (η.toNatTrans.naturality h.down))
  mapId C := Iso.refl (catLift.map (𝟙 C))
  mapComp F G := Iso.refl (catLift.map (F ≫ G))
  map₂_id f := by congr
  map₂_whisker_left {a b c} f g h η := by
    ext x
    erw [Category.comp_id, Category.id_comp]
    congr
  map₂_whisker_right η h := by
    congr
    ext ⟨x⟩
    erw [Category.comp_id, Category.id_comp]
    exact eq_of_comp_right_eq fun {Z} ↦ congrFun rfl
  map₂_associator {a b c d} f g h := by
    ext ⟨x⟩
    erw [Category.comp_id, Category.id_comp]
    simp only [Cat.Hom.comp_toFunctor, comp_obj, ULiftHom.down_obj, ULift.downFunctor_obj,
      ULiftHom.up_obj, Cat.associator_hom_toNatTrans, associator_hom_app, Iso.refl_hom,
      Iso.refl_inv, Cat.Hom.toNatTrans_comp, Cat.whiskerRight_toNatTrans, Cat.Hom.toNatTrans_id,
      Cat.whiskerLeft_toNatTrans, NatTrans.comp_app, whiskerRight_app, NatTrans.id_app,
      whiskerLeft_app, Category.id_comp]
    erw [(catLift.map h).toFunctor.map_id, Category.id_comp, ULiftHom.up.map_id]
    congr
  map₂_left_unitor {a b} f := by
    ext ⟨x⟩
    simp only [Cat.Hom.comp_toFunctor, Cat.Hom.id_toFunctor, comp_obj, ULiftHom.down_obj,
      ULift.downFunctor_obj, id_obj, ULiftHom.up_obj, Cat.leftUnitor_hom_toNatTrans,
      leftUnitor_hom_app, Iso.refl_hom, Cat.Hom.toNatTrans_comp, Cat.Hom.toNatTrans_id,
      Cat.whiskerRight_toNatTrans, NatTrans.comp_app, NatTrans.id_app, whiskerRight_app,
      Category.comp_id]
    erw [ULiftHom.up.map_id, (catLift.map f).toFunctor.map_id, Category.comp_id]
    congr
  map₂_right_unitor {a b} f := by
    ext ⟨x⟩
    simp only [Cat.Hom.comp_toFunctor, Cat.Hom.id_toFunctor, comp_obj, ULiftHom.down_obj,
      ULift.downFunctor_obj, id_obj, ULiftHom.up_obj, Cat.rightUnitor_hom_toNatTrans,
      rightUnitor_hom_app, Iso.refl_hom, Cat.Hom.toNatTrans_comp, Cat.Hom.toNatTrans_id,
      Cat.whiskerLeft_toNatTrans, NatTrans.comp_app, NatTrans.id_app, whiskerLeft_app,
      Category.comp_id]
    erw [ULiftHom.up.map_id, Category.id_comp]
    congr
/-- Two 2-cells of `Cat` landing in a universe-lifted category are equal as soon as their
unlifted components agree: morphisms of `ULiftHom (ULift D)` are `ULift`-wrapped, so the
lifting plumbing can be stripped once and for all. -/
lemma catLift_hom₂_ext {E : Cat} {D : Cat.{v₁, u₁}}
    {H K : E ⟶ catPseudoULift.{v₁, v₂, u₁, u₂}.obj D} {η θ : H ⟶ K}
    (h : ∀ X : E, (η.toNatTrans.app X).down = (θ.toNatTrans.app X).down) : η = θ := by
  apply Cat.Hom₂.ext_app
  intro X
  exact congrArg ULift.up (h X)

/-- Components of equal 2-cells into a lifted category have equal unlifted parts. -/
lemma catLift_hom₂_congr_down {E : Cat} {D : Cat.{v₁, u₁}}
    {H K : E ⟶ catPseudoULift.{v₁, v₂, u₁, u₂}.obj D} {η θ : H ⟶ K}
    (h : η = θ) (X : E) :
    (η.toNatTrans.app X).down = (θ.toNatTrans.app X).down := by rw [h]
