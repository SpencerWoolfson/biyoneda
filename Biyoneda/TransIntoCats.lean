/-
Copyright (c) 2026 Spencer Woolfson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Spencer Woolfson
-/
import Mathlib.CategoryTheory.Bicategory.Modification.Pseudo
import Biyoneda.ForMathlib
import Biyoneda.UniverseLift

/-!
# Transformations between `Cat`-valued pseudofunctors

`StrongTrans F G` requires `F` and `G` to land in the *same* bicategory, so two `Cat`-valued
pseudofunctors whose fibres sit in different universes cannot be related by one — even when the
data is perfectly well defined.  This file supplies that data, with the universes left
independent, and the constructions that decide the universe relationship afterwards.

* `StrongTransIntoCats` — a strong transformation whose two sides may live in different
  universes.  Its coherence obligations are stated *pointwise*.
* `ModificationIntoCats` — a modification between two of those.
* `lift` / `liftDom` / `toStrongTransMax` — turn the data into a genuine `StrongTrans` by
  lifting the codomain, the domain, or both.  The first two are the useful ones in practice:
  each leaves one side alone, which is what lets the result land on a pseudofunctor you can
  still destructure.

Independent of the composite gadgets in `Biyoneda/Gadgets.lean`; both sit directly on
`Biyoneda/UniverseLift.lean`.
-/

open CategoryTheory Bicategory Bicategory.Opposite Opposite Pseudofunctor StrongTrans Functor
open scoped Pseudofunctor.StrongTrans

universe w₁ v₁ u₁ w₂ v₂ u₂ w₃ v₃ u₃ u v w

attribute [local instance] uliftCategory

namespace CategoryTheory.Bicategory

/-! ### Gadget 4 — strong transformations between `Cat`-valued pseudofunctors

`StrongTrans F G` requires `F` and `G` to land in the *same* bicategory, so two `Cat`-valued
pseudofunctors whose fibres sit in different universes cannot be related by one, even when the
data is perfectly well defined. `StrongTransIntoCats` is that data, with the two universes left
independent: `app a : F.obj a ⥤ G.obj a` typechecks across universes even though
`F ⟶ G` does not.

The coherence obligations are stated *pointwise*, which is the form fibre-level lemmas are
usually already in.

The universe relationship is deliberately absent from this type. It belongs to whatever consumes
the data: `StrongTransIntoCats.lift` and `.liftDom`, below, each
lift one side, and when the two universes happen to agree the transformation can be read off
directly with no lift at all. That is the improvement over carrying `catPseudoULift` in the
type: nothing is forced to be the bigger side. -/
structure StrongTransIntoCats {B : Type u} [Bicategory.{w₁, v₁} B]
    (F : B ⥤ᵖ Cat.{w₂, v₂}) (G : B ⥤ᵖ Cat.{w₃, v₃}) where
  /-- The component functor at each object. Its source and target may live in different
  universes — this is what `StrongTrans` cannot express. -/
  app : (b : B) → (F.obj b ⥤ G.obj b)
  /-- The naturality isomorphism, as a functor iso rather than a `Cat` 2-cell. -/
  naturality : {a b : B} → (f : a ⟶ b) →
    ((F.map f).toFunctor ⋙ app b) ≅ (app a ⋙ (G.map f).toFunctor)
  naturality_naturality' {a b : B} {f g : a ⟶ b} (η : f ⟶ g) (x : F.obj a) :
      (app b).map ((F.map₂ η).toNatTrans.app x) ≫ (naturality g).hom.app x =
      (naturality f).hom.app x ≫ (G.map₂ η).toNatTrans.app ((app a).obj x) := by cat_disch
  naturality_id' (a : B) (x : F.obj a) :
      (naturality (𝟙 a)).hom.app x ≫ (G.mapId a).hom.toNatTrans.app ((app a).obj x) =
      (app a).map ((F.mapId a).hom.toNatTrans.app x) := by cat_disch
  naturality_comp' {a b c : B} (f : a ⟶ b) (g : b ⟶ c) (x : F.obj a) :
      (naturality (f ≫ g)).hom.app x ≫ (G.mapComp f g).hom.toNatTrans.app ((app a).obj x) =
      (app c).map ((F.mapComp f g).hom.toNatTrans.app x) ≫
        (naturality g).hom.app ((F.map f).toFunctor.obj x) ≫
        (G.map g).toFunctor.map ((naturality f).hom.app x) := by cat_disch

structure ModificationIntoCats {B : Type u} [Bicategory.{w₁, v₁} B]
    {F : B ⥤ᵖ Cat.{w₂, v₂}} {G : B ⥤ᵖ Cat.{w₃, v₃}} (η θ : StrongTransIntoCats F G) where
    app (a : B) : NatTrans (η.app a) (θ.app a)
    naturality {a b : B} (f : a ⟶ b) :
      Functor.whiskerLeft (F.map f).toFunctor (app b) ≫ (θ.naturality f).hom =
        (η.naturality f).hom ≫ (Functor.whiskerRight (app a) (G.map f).toFunctor) := by cat_disch

/-! ### Turning the data into an actual `StrongTrans`

`StrongTransIntoCats` deliberately says nothing about how the two universes relate.  The three
constructions below are where that gets decided: `lift` lifts the codomain, `liftDom` the
domain, and `toStrongTransMax` both.  `lift` and `liftDom` are the useful ones in practice
because they leave one side alone — which is what lets them land on a pseudofunctor you can
still destructure.
-/

section CatLiftCodomain

variable {A : Type u} [Bicategory A]

variable {F : Pseudofunctor A Cat.{max v₁ v₂, max u₁ u₂}} {G : Pseudofunctor A Cat.{v₁, u₁}}
  (data : StrongTransIntoCats F G)

/-- Counit-stripping for the **composite** `G ⋙ catPseudoULift`.

`catLiftCounit_map_catPseudoULift_map₂'` already strips a bare `catPseudoULift.map₂`, but the
composite spells its `map₂` as `(G.comp catPseudoULift).map₂`, which `simp` treats as an opaque
head even though the two are definitionally equal.  Every field of `lift` lands on this shape,
so bridging it once here is what lets the default simp set finish those goals. -/
@[simp] lemma catLiftCounit_map_comp_map₂ {a b : A} {f g : a ⟶ b} (η : f ⟶ g)
    (x : ↑(catPseudoULift.{v₁, v₂, u₁, u₂}.obj (G.obj a))) :
    (catLiftCounit.{v₁, v₂, u₁, u₂} (G.obj b)).map
        (((G.toPrelaxFunctor.comp
          catPseudoULift.{v₁, v₂, u₁, u₂}.toPrelaxFunctor).map₂ η).toNatTrans.app x)
      = (G.map₂ η).toNatTrans.app
          ((catLiftCounit.{v₁, v₂, u₁, u₂} (G.obj a)).obj x) := rfl

/-- The object-level companion: a 1-cell of the composite, applied to a lifted object and brought
back down. -/
@[simp] lemma catLiftCounit_obj_comp_map_obj {a b : A} (f : a ⟶ b)
    (x : ↑(catPseudoULift.{v₁, v₂, u₁, u₂}.obj (G.obj a))) :
    (catLiftCounit.{v₁, v₂, u₁, u₂} (G.obj b)).obj
        (((G.toPrelaxFunctor.comp
          catPseudoULift.{v₁, v₂, u₁, u₂}.toPrelaxFunctor).map f).toFunctor.obj x)
      = (G.map f).toFunctor.obj ((catLiftCounit.{v₁, v₂, u₁, u₂} (G.obj a)).obj x) := rfl

/-- ...and on morphisms. -/
@[simp] lemma catLiftCounit_map_comp_map_map {a b : A} (f : a ⟶ b)
    {x y : ↑(catPseudoULift.{v₁, v₂, u₁, u₂}.obj (G.obj a))} (m : x ⟶ y) :
    (catLiftCounit.{v₁, v₂, u₁, u₂} (G.obj b)).map
        (((G.toPrelaxFunctor.comp
          catPseudoULift.{v₁, v₂, u₁, u₂}.toPrelaxFunctor).map f).toFunctor.map m)
      = (G.map f).toFunctor.map ((catLiftCounit.{v₁, v₂, u₁, u₂} (G.obj a)).map m) := rfl

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
    apply catLift_hom₂_counit_ext; intro X
    dsimp only [Pseudofunctor.comp, Functor.comp_map]
    simpa using NatTrans.congr_app (data.naturality_naturality η) X
  naturality_id a := by
    apply catLift_hom₂_counit_ext; intro X
    dsimp only [Pseudofunctor.comp, Functor.comp_map]
    simpa using NatTrans.congr_app (data.naturality_id a) X
  naturality_comp {a b c} f g := by
    apply catLift_hom₂_counit_ext; intro X
    dsimp only [Pseudofunctor.comp, Functor.comp_map]
    simpa using NatTrans.congr_app (data.naturality_comp f g) X

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
    exact data.naturality_comp' f g x

/-- Precompose the data with the counit, turning a transformation out of `F` into one out of
the *lifted* `F`.  `catLiftCounit`'s interaction with `catPseudoULift` is definitional, so each
obligation is `d`'s own at the lowered point.

`naturality_naturality'` closes outright.  The other two reduce to `d`'s field modulo a single
residual `≫ 𝟙` that `Category.comp_id` will not collapse reducibly and `erw` does not bridge
either -- see the note on `toStrongTransMax`. -/
def StrongTransIntoCats.precomposeCounit {A : Type u} [Bicategory A]
    {F : Pseudofunctor A Cat.{v₁, u₁}} {G : Pseudofunctor A Cat.{v₂, u₂}}
    (d : StrongTransIntoCats F G) :
    StrongTransIntoCats (F.comp catPseudoULift.{v₁, v₂, u₁, u₂}) G where
  app a := catLiftCounit (F.obj a) ⋙ d.app a
  naturality {a b} f := Functor.isoWhiskerLeft (catLiftCounit (F.obj a)) (d.naturality f)
  naturality_naturality' {a b} {f g} η x :=
    d.naturality_naturality' η ((catLiftCounit (F.obj a)).obj x)
  naturality_id' a x := by
    -- PARKED.  The reduction that gets closest is
    --   dsimp only [Pseudofunctor.comp, Functor.comp_map, Functor.comp_obj]
    --   simp only [Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.trans_hom,
    --     PrelaxFunctor.map₂Iso_hom, Cat.Hom.toNatTrans_comp, NatTrans.comp_app,
    --     catLiftCounit_map_catPseudoULift_map₂', catPseudoULift_mapId_hom_app']
    -- after which the goal is `d`'s own `naturality_id'` at `(catLiftCounit _).obj x`, except
    -- for a residual `≫ 𝟙` on the right that neither `Category.comp_id` nor `erw` collapses:
    --   (d.app a).map ((counit).map ((map₂ (F.mapId a).hom).app x ≫ 𝟙 _))
    -- versus
    --   (d.app a).map ((F.mapId a).hom.app (counit.obj x))
    sorry
  naturality_comp' {a b c} f g x := by
    -- PARKED.  Same shape as `naturality_id'` above, with more factors.
    sorry

/-- The symmetric lift: a strong transformation between the *lifted copies* of both sides, so
neither is privileged.

This is the general form.  `lift` and `liftDom` are the cases where one side is already at the
target universe and can be left alone -- which is what makes them land on `yonedaPairing` and
`yonedaEvaluation` themselves rather than on lifted copies.

The construction is modular rather than hand-rolled: lower the domain with `precomposeCounit`,
then reuse the already-proven `lift`.  The universe arithmetic works because Lean's `max` is
commutative, so `F.comp catPseudoULift.{v₁, v₂, u₁, u₂}` and
`G.comp catPseudoULift.{v₂, v₁, u₂, u₁}` land in the same universe.  **That part typechecks**;
what is open is two of `precomposeCounit`'s three coherence fields. -/
def StrongTransIntoCats.toStrongTransMax {A : Type u} [Bicategory A]
    {F : Pseudofunctor A Cat.{v₁, u₁}} {G : Pseudofunctor A Cat.{v₂, u₂}}
    (d : StrongTransIntoCats F G) :
    StrongTrans (F.comp catPseudoULift.{v₁, v₂, u₁, u₂})
                (G.comp catPseudoULift.{v₂, v₁, u₂, u₁}) :=
  d.precomposeCounit.lift

end CategoryTheory.Bicategory
