/-
Copyright (c) 2026 Spencer Woolfson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Spencer Woolfson
-/
import Biyoneda.UniverseLift
import Biyoneda.Gadgets

/-!
# Strong transformations across a universe lift

Defining a `StrongTrans` where one side is `catPseudoULift`-composed costs about fifteen lines
of `ULift` plumbing per coherence field.  These two gadgets pay that cost once.

* `StrongTransIntoCats` / `.lift` — the lift is in the **codomain**,
  `StrongTrans F (G.comp catPseudoULift)`.
* `StrongTransIntoCats` / `.lift` — the lift is in the **domain**,
  `StrongTrans (G.comp catPseudoULift) F`.

Both take their coherence obligations *pointwise*, which is the form fibre-level lemmas are
usually already in.  Neither can be assembled from `Pseudofunctor.comp` and friends: `F ⟶ G`
does not elaborate when the two live in different universes, so these are genuinely
heterogeneous notions.
-/

namespace CategoryTheory.Bicategory

open CategoryTheory Bicategory Opposite Pseudofunctor StrongTrans Functor

universe u v w v₁ v₂ u₁ u₂

attribute [local instance] uliftCategory

section CatLiftCodomain

variable {A : Type u} [Bicategory A]

variable {F : Pseudofunctor A Cat.{max v₁ v₂, max u₁ u₂}} {G : Pseudofunctor A Cat.{v₁, u₁}}
  (data : StrongTransIntoCats F G)

/-- Whiskered form of `naturality_naturality'`, in the shape `StrongTrans` asks for. -/
lemma StrongTransIntoCats.naturality_naturality {a b : A} {f g : a ⟶ b} (η : f ⟶ g) :
    Functor.whiskerRight (F.map₂ η).toNatTrans (data.app b) ≫ (data.naturality g).hom =
      (data.naturality f).hom ≫ Functor.whiskerLeft (data.app a) (G.map₂ η).toNatTrans := by
  ext x
  simpa using data.naturality_naturality' η x

/-- Whiskered form of `naturality_id'`, in the shape `StrongTrans` asks for. -/
lemma StrongTransIntoCats.naturality_id (a : A) :
    (data.naturality (𝟙 a)).hom ≫ Functor.whiskerLeft (data.app a) (G.mapId a).hom.toNatTrans =
      Functor.whiskerRight (F.mapId a).hom.toNatTrans (data.app a) ≫
        (Functor.leftUnitor (data.app a)).hom ≫ (Functor.rightUnitor (data.app a)).inv := by
  ext x
  dsimp [Functor.whiskerLeft]
  simpa only [Category.comp_id] using data.naturality_id' a x

/-- Whiskered form of `naturality_comp'`, in the shape `StrongTrans` asks for. -/
lemma StrongTransIntoCats.naturality_comp {a b c : A} (f : a ⟶ b) (g : b ⟶ c) :
    (data.naturality (f ≫ g)).hom ≫
        Functor.whiskerLeft (data.app a) (G.mapComp f g).hom.toNatTrans =
      Functor.whiskerRight (F.mapComp f g).hom.toNatTrans (data.app c) ≫
        (Functor.associator (F.map f).toFunctor (F.map g).toFunctor (data.app c)).hom ≫
        Functor.whiskerLeft (F.map f).toFunctor (data.naturality g).hom ≫
        (Functor.associator (F.map f).toFunctor (data.app b) (G.map g).toFunctor).inv ≫
        Functor.whiskerRight (data.naturality f).hom (G.map g).toFunctor ≫
        (Functor.associator (data.app a) (G.map f).toFunctor (G.map g).toFunctor).hom := by
  ext x
  simpa [Functor.associator, Functor.whiskerRight] using data.naturality_comp' f g x

set_option backward.isDefEq.respectTransparency false in
/-- Assemble `StrongTransIntoCats` into a genuine strong transformation into the lift. -/
def StrongTransIntoCats.lift : StrongTrans F (G.comp catPseudoULift) where
  app a := { toFunctor := data.app a ⋙ catLiftUnit (G.obj a) }
  naturality {a b} f :=
    Cat.Hom.isoMk (Functor.isoWhiskerRight (data.naturality f) (catLiftUnit (G.obj b)) ≪≫
      Iso.refl ((data.app a ⋙ (G.map f).toFunctor) ⋙ catLiftUnit (G.obj b)))
  naturality_naturality {a b f g} η := by
    apply catLift_hom₂_ext; intro X
    dsimp [catLiftUnit]
    simpa only [Category.comp_id] using NatTrans.congr_app (data.naturality_naturality η) X
  naturality_id a := by
    apply catLift_hom₂_ext; intro X
    dsimp [catLiftUnit, catPseudoULift, catLift, ULiftHom.up]
    simpa using NatTrans.congr_app (data.naturality_id a) X
  naturality_comp {a b c} f g := by
    apply catLift_hom₂_ext; intro X
    have h := NatTrans.congr_app (data.naturality_comp f g) X
    simp at h
    -- reduce the Cat-level structure and unfold the composite pseudofunctor's projections,
    -- but keep `catLiftUnit` folded so the stripping lemmas above can fire
    dsimp only [Pseudofunctor.comp, Functor.comp_map]
    -- every factor becomes `catLiftUnit.map _`; combine through the functor and apply `h`
    simpa [Cat.Hom.isoMk_hom, Iso.trans_hom, isoWhiskerRight_hom,
      Cat.Hom.toNatTrans_comp, NatTrans.comp_app,
      Cat.whiskerLeft_toNatTrans, Cat.whiskerRight_toNatTrans, whiskerLeft_app,
      whiskerRight_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      catPseudoULift_map_catLiftUnit_map, catPseudoULift_map₂_app_catLiftUnit,
      catPseudoULift_mapComp_hom_app, Category.comp_id]
      using congrArg (catLiftUnit.{v₁, u₁, v₂, u₂} (G.obj c)).map h

end CatLiftCodomain

section LiftSimp
variable {A : Type u} [Bicategory A] {F : Pseudofunctor A Cat.{max v₁ v₂, max u₁ u₂}}
  {G : Pseudofunctor A Cat.{v₁, u₁}} (data : StrongTransIntoCats F G)

/-- The lifted transformation's component, at the **functor** level: it is the unlifted
component followed by the (strict, transparent) unit.  Downstream reasoning should translate
through this rather than unfolding the lift to `ULift.up`/`.down`. -/
@[simp] lemma StrongTransIntoCats.lift_app_toFunctor (a : A) :
    ((StrongTransIntoCats.lift data).app a).toFunctor
      = data.app a ⋙ catLiftUnit (G.obj a) := rfl

/-- `Cat.Hom`-level form of `lift_app_toFunctor`. -/
lemma StrongTransIntoCats.lift_app (a : A) :
    (StrongTransIntoCats.lift data).app a
      = Functor.toCatHom (data.app a ⋙ catLiftUnit (G.obj a)) := rfl

end LiftSimp

/-! ### The dual gadget: a lifted *domain*

`StrongTransIntoCats` / `StrongTransIntoCats.lift` handle a transformation *into* a lifted
codomain, `StrongTrans F (G.comp catPseudoULift)`.  The Yoneda development also needs the other
side — `yonedaLemmaBackwards : yonedaEvaluation ⟶ yonedaPairing` has the lift in its **domain**.
The data is the same shape; only the plumbing moves from `catLiftUnit` to `catLiftCounit`.
-/

set_option linter.flexible false in
set_option backward.isDefEq.respectTransparency false in
/-- Assemble `StrongTransIntoCats` into a genuine strong transformation out of the lift. -/
def StrongTransIntoCats.liftDom {A : Type u} [Bicategory A]
    {G : Pseudofunctor A Cat.{v₁, u₁}} {F : Pseudofunctor A Cat.{max v₁ v₂, max u₁ u₂}}
    (data : StrongTransIntoCats G F) : StrongTrans (G.comp catPseudoULift) F where
  app a := { toFunctor := catLiftCounit (G.obj a) ⋙ data.app a }
  naturality {a b} f :=
    Cat.Hom.isoMk (Functor.isoWhiskerLeft (catLiftCounit (G.obj a)) (data.naturality f))
  naturality_naturality {a b f g} η := by
    apply catLift_hom₂_dom_ext; intro x
    exact data.naturality_naturality' η x
  naturality_id a := by
    apply catLift_hom₂_dom_ext; intro x
    simpa using data.naturality_id' a x
  naturality_comp {a b c} f g := by
    apply catLift_hom₂_dom_ext; intro x
    -- unfold the composite pseudofunctor's projections, then let the domain-side stripping
    -- lemmas above bring every factor back down through `catLiftCounit`
    dsimp only [Pseudofunctor.comp, Functor.comp_map]
    simp [Cat.Hom.isoMk_hom, isoWhiskerLeft_hom, Cat.Hom.toNatTrans_comp, NatTrans.comp_app,
      Cat.whiskerLeft_toNatTrans, Cat.whiskerRight_toNatTrans, whiskerLeft_app, whiskerRight_app,
      Cat.associator_hom_toNatTrans, Cat.associator_inv_toNatTrans, associator_hom_app,
      associator_inv_app, Functor.whiskerLeft_app, catPseudoULift_mapComp_hom_app,
      Category.comp_id]
    -- the residual `𝟙` sits at a different spelling of the fibre category, so `id_comp` needs
    -- to match up to unfolding
    erw [Category.id_comp]
    exact data.naturality_comp' f g x

end CategoryTheory.Bicategory
