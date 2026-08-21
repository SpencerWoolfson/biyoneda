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
* `catLift_hom₂_ext` — 2-cells into a lifted category are determined by their unlifted
  components.
* `CatliftStrongTransData` / `CatliftStrongTrans.lift` — define a strong transformation into a
  universe-lifted codomain from pointwise data, paying the `ULift` plumbing once.

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

def catLiftUnit (A : Cat.{v₁, u₁}) : A ⥤ (catLift.obj A) where
  obj x := {down := x}
  map {x y} f := {down := f}


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

/-- The counit of the universe lift: `catLiftUnit`'s inverse, as a functor.  Kept at the functor
level so that reasoning about a lifted *domain* never has to reach for `ULift.down`. -/
def catLiftCounit (A : Cat.{v₁, u₁}) : (catLift.{v₁, v₂, u₁, u₂}.obj A) ⥤ A :=
  (catLiftEquiv.{v₁, v₂, u₁, u₂} A.α).inverse

@[simp] lemma catLiftUnit_comp_catLiftCounit (A : Cat.{v₁, u₁}) :
    catLiftUnit A ⋙ catLiftCounit.{v₁, v₂, u₁, u₂} A = 𝟭 A := rfl

@[simp] lemma catLiftCounit_comp_catLiftUnit (A : Cat.{v₁, u₁}) :
    catLiftCounit.{v₁, v₂, u₁, u₂} A ⋙ catLiftUnit A = 𝟭 _ := rfl

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


/-! ### Stripping the lift at the functor level

The lemmas below eliminate a `catPseudoULift` while it is still applied as a *functor*, rather
than unfolding `catLift`/`ULiftHom` down to raw `ULift.up` wrappers. Unfolding all the way
leaves goals of the form `ULift.up x ≫ ULift.up y`, which do not recombine; rewriting at the
functor level keeps everything inside `catLiftUnit` and stays composable. All hold by `rfl`
because `ULift`/`ULiftHom` are strictly functorial and the lift's coherence isos are identities.
-/

@[simp] lemma catLiftUnit_map_down {C : Cat.{v₁, u₁}} {x y : C} (m : x ⟶ y) :
    ((catLiftUnit C).map m).down = m := rfl

/-- Stripping the lift on the **domain** side: a lifted 1-cell precomposed with the counit is the
counit followed by the unlifted 1-cell. -/
@[simp] lemma catLiftCounit_naturality {C D : Cat.{v₁, u₁}} (F : C ⟶ D) :
    (catPseudoULift.{v₁, v₂, u₁, u₂}.map F).toFunctor ⋙ catLiftCounit D
      = catLiftCounit C ⋙ F.toFunctor := rfl

/-- The unit followed by the counit is the identity, at a point.  The functor-level
`catLiftUnit_comp_catLiftCounit` cannot fire here because `simp` normalises composites apart. -/
@[simp] lemma catLiftCounit_obj_catLiftUnit_obj {C : Cat.{v₁, u₁}} (x : C) :
    (catLiftCounit.{v₁, v₂, u₁, u₂} C).obj ((catLiftUnit C).obj x) = x := rfl

@[simp] lemma catLiftCounit_map_catLiftUnit_map {C : Cat.{v₁, u₁}} {x y : C} (m : x ⟶ y) :
    (catLiftCounit.{v₁, v₂, u₁, u₂} C).map ((catLiftUnit C).map m) = m := rfl

/-- A lifted 1-cell applied to a lifted object, brought back down. -/
@[simp] lemma catLiftCounit_obj_catPseudoULift_map_obj {C D : Cat.{v₁, u₁}} (F : C ⟶ D) (x : C) :
    (catLiftCounit.{v₁, v₂, u₁, u₂} D).obj
        ((catPseudoULift.{v₁, v₂, u₁, u₂}.map F).toFunctor.obj ((catLiftUnit C).obj x))
      = F.toFunctor.obj x := rfl

/-- A lifted 2-cell, evaluated at a lifted object and brought back down. -/
@[simp] lemma catLiftCounit_map_catPseudoULift_map₂ {C D : Cat.{v₁, u₁}} {F G : C ⟶ D}
    (η : F ⟶ G) (x : C) :
    (catLiftCounit.{v₁, v₂, u₁, u₂} D).map
        ((catPseudoULift.{v₁, v₂, u₁, u₂}.map₂ η).toNatTrans.app ((catLiftUnit C).obj x))
      = η.toNatTrans.app x := rfl

@[simp] lemma catPseudoULift_map_catLiftUnit_map {C D : Cat.{v₁, u₁}} (F : C ⟶ D)
    {x y : C} (m : x ⟶ y) :
    (catPseudoULift.{v₁, v₂, u₁, u₂}.map F).toFunctor.map ((catLiftUnit C).map m)
      = (catLiftUnit D).map (F.toFunctor.map m) := rfl

@[simp] lemma catPseudoULift_map₂_app_catLiftUnit {C D : Cat.{v₁, u₁}} {F G : C ⟶ D}
    (η : F ⟶ G) (x : C) :
    (catPseudoULift.{v₁, v₂, u₁, u₂}.map₂ η).toNatTrans.app ((catLiftUnit C).obj x)
      = (catLiftUnit D).map (η.toNatTrans.app x) := rfl

@[simp] lemma catPseudoULift_mapComp_hom_app {C D E : Cat.{v₁, u₁}} (F : C ⟶ D) (G : D ⟶ E)
    (x : ↑(catPseudoULift.{v₁, v₂, u₁, u₂}.obj C)) :
    (catPseudoULift.{v₁, v₂, u₁, u₂}.mapComp F G).hom.toNatTrans.app x = 𝟙 _ := rfl

@[simp] lemma catPseudoULift_mapId_hom_app {C : Cat.{v₁, u₁}}
    (x : ↑(catPseudoULift.{v₁, v₂, u₁, u₂}.obj C)) :
    (catPseudoULift.{v₁, v₂, u₁, u₂}.mapId C).hom.toNatTrans.app x = 𝟙 _ := rfl


section CatliftCodomain

variable {A : Type u} [Bicategory A]

/-- Pointwise data for a strong transformation *into* a universe-lifted pseudofunctor.

`F ⟶ G.comp catPseudoULift` cannot be handed a plain `StrongTrans F G`: `F` and `G` live in
different universes, so that type does not even elaborate.  This is the heterogeneous stand-in.
Its three coherence obligations are stated *at a point*, which is the form fibre-level lemmas
are usually already in; `CatliftStrongTrans.lift` supplies the plumbing. -/
structure CatliftStrongTransData (F : Pseudofunctor A Cat.{max v₁ v₂, max u₁ u₂})
    (G : Pseudofunctor A Cat.{v₁, u₁}) where
  app : (a : A) → (F.obj a ⥤ G.obj a)
  naturality : {a b : A} → (f : a ⟶ b) →
    ((F.map f).toFunctor ⋙ app b) ≅ (app a ⋙ (G.map f).toFunctor)
  naturality_naturality' {a b : A} {f g : a ⟶ b} (η : f ⟶ g) (x : F.obj a) :
      (app b).map ((F.map₂ η).toNatTrans.app x) ≫ (naturality g).hom.app x =
      (naturality f).hom.app x ≫ (G.map₂ η).toNatTrans.app ((app a).obj x) := by cat_disch
  naturality_id' (a : A) (x : F.obj a) :
      (naturality (𝟙 a)).hom.app x ≫ (G.mapId a).hom.toNatTrans.app ((app a).obj x) =
      (app a).map ((F.mapId a).hom.toNatTrans.app x) := by cat_disch
  naturality_comp' {a b c : A} (f : a ⟶ b) (g : b ⟶ c) (x : F.obj a) :
      (naturality (f ≫ g)).hom.app x ≫ (G.mapComp f g).hom.toNatTrans.app ((app a).obj x) =
      (app c).map ((F.mapComp f g).hom.toNatTrans.app x) ≫
        (naturality g).hom.app ((F.map f).toFunctor.obj x) ≫
        (G.map g).toFunctor.map ((naturality f).hom.app x) := by cat_disch

variable {F : Pseudofunctor A Cat.{max v₁ v₂, max u₁ u₂}} {G : Pseudofunctor A Cat.{v₁, u₁}}
  (data : CatliftStrongTransData F G)

/-- Whiskered form of `naturality_naturality'`, in the shape `StrongTrans` asks for. -/
lemma CatliftStrongTransData.naturality_naturality {a b : A} {f g : a ⟶ b} (η : f ⟶ g) :
    Functor.whiskerRight (F.map₂ η).toNatTrans (data.app b) ≫ (data.naturality g).hom =
      (data.naturality f).hom ≫ Functor.whiskerLeft (data.app a) (G.map₂ η).toNatTrans := by
  ext x
  simpa using data.naturality_naturality' η x

/-- Whiskered form of `naturality_id'`, in the shape `StrongTrans` asks for. -/
lemma CatliftStrongTransData.naturality_id (a : A) :
    (data.naturality (𝟙 a)).hom ≫ Functor.whiskerLeft (data.app a) (G.mapId a).hom.toNatTrans =
      Functor.whiskerRight (F.mapId a).hom.toNatTrans (data.app a) ≫
        (Functor.leftUnitor (data.app a)).hom ≫ (Functor.rightUnitor (data.app a)).inv := by
  ext x
  dsimp [Functor.whiskerLeft]
  simpa only [Category.comp_id] using data.naturality_id' a x

/-- Whiskered form of `naturality_comp'`, in the shape `StrongTrans` asks for. -/
lemma CatliftStrongTransData.naturality_comp {a b c : A} (f : a ⟶ b) (g : b ⟶ c) :
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
/-- Assemble `CatliftStrongTransData` into a genuine strong transformation into the lift. -/
def CatliftStrongTrans.lift : StrongTrans F (G.comp catPseudoULift) where
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

end CatliftCodomain

section LiftSimp
variable {A : Type u} [Bicategory A] {F : Pseudofunctor A Cat.{max v₁ v₂, max u₁ u₂}}
  {G : Pseudofunctor A Cat.{v₁, u₁}} (data : CatliftStrongTransData F G)

/-- The lifted transformation's component, at the **functor** level: it is the unlifted
component followed by the (strict, transparent) unit.  Downstream reasoning should translate
through this rather than unfolding the lift to `ULift.up`/`.down`. -/
@[simp] lemma CatliftStrongTrans.lift_app_toFunctor (a : A) :
    ((CatliftStrongTrans.lift data).app a).toFunctor
      = data.app a ⋙ catLiftUnit (G.obj a) := rfl

/-- `Cat.Hom`-level form of `lift_app_toFunctor`. -/
lemma CatliftStrongTrans.lift_app (a : A) :
    (CatliftStrongTrans.lift data).app a
      = Functor.toCatHom (data.app a ⋙ catLiftUnit (G.obj a)) := rfl

end LiftSimp

/-! ### The dual gadget: a lifted *domain*

`CatliftStrongTransData` / `CatliftStrongTrans.lift` handle a transformation *into* a lifted
codomain, `StrongTrans F (G.comp catPseudoULift)`.  The Yoneda development also needs the other
side — `yonedaLemmaBackwards : yonedaEvaluation ⟶ yonedaPairing` has the lift in its **domain**.
The data is the same shape; only the plumbing moves from `catLiftUnit` to `catLiftCounit`.
-/

/-- Two 2-cells out of a universe-lifted category are equal as soon as they agree on the image
of `catLiftUnit`, which hits every object.  The domain-side counterpart of `catLift_hom₂_ext`;
stated through the unit functor rather than `ULift.down` so it composes with the functor-level
stripping lemmas. -/
lemma catLift_hom₂_dom_ext {D : Cat.{v₁, u₁}} {E : Cat}
    {H K : catPseudoULift.{v₁, v₂, u₁, u₂}.obj D ⟶ E} {η θ : H ⟶ K}
    (h : ∀ x : D, η.toNatTrans.app ((catLiftUnit D).obj x)
        = θ.toNatTrans.app ((catLiftUnit D).obj x)) : η = θ := by
  apply Cat.Hom₂.ext_app
  intro X
  exact h ((catLiftCounit D).obj X)

/-- Pointwise data for a strong transformation *out of* a universe-lifted pseudofunctor.
Mirrors `CatliftStrongTransData`; `CatliftStrongTrans.liftDom` supplies the plumbing. -/
structure CatliftStrongTransDomData {A : Type u} [Bicategory A]
    (G : Pseudofunctor A Cat.{v₁, u₁})
    (F : Pseudofunctor A Cat.{max v₁ v₂, max u₁ u₂}) where
  app : (a : A) → (G.obj a ⥤ F.obj a)
  naturality : {a b : A} → (f : a ⟶ b) →
    ((G.map f).toFunctor ⋙ app b) ≅ (app a ⋙ (F.map f).toFunctor)
  naturality_naturality' {a b : A} {f g : a ⟶ b} (η : f ⟶ g) (x : G.obj a) :
      (app b).map ((G.map₂ η).toNatTrans.app x) ≫ (naturality g).hom.app x =
      (naturality f).hom.app x ≫ (F.map₂ η).toNatTrans.app ((app a).obj x) := by cat_disch
  naturality_id' (a : A) (x : G.obj a) :
      (naturality (𝟙 a)).hom.app x ≫ (F.mapId a).hom.toNatTrans.app ((app a).obj x) =
      (app a).map ((G.mapId a).hom.toNatTrans.app x) := by cat_disch
  naturality_comp' {a b c : A} (f : a ⟶ b) (g : b ⟶ c) (x : G.obj a) :
      (naturality (f ≫ g)).hom.app x ≫ (F.mapComp f g).hom.toNatTrans.app ((app a).obj x) =
      (app c).map ((G.mapComp f g).hom.toNatTrans.app x) ≫
        (naturality g).hom.app ((G.map f).toFunctor.obj x) ≫
        (F.map g).toFunctor.map ((naturality f).hom.app x) := by cat_disch

-- see the note on `yonedaLemmaForwardsStructure`: squeezing `naturality_comp`'s `simp` would
-- freeze 34 lemma names right before the Mathlib walk, for a proof that fails loudly anyway
set_option linter.flexible false in
set_option backward.isDefEq.respectTransparency false in
/-- Assemble `CatliftStrongTransDomData` into a genuine strong transformation out of the lift. -/
def CatliftStrongTrans.liftDom {A : Type u} [Bicategory A]
    {G : Pseudofunctor A Cat.{v₁, u₁}} {F : Pseudofunctor A Cat.{max v₁ v₂, max u₁ u₂}}
    (data : CatliftStrongTransDomData G F) : StrongTrans (G.comp catPseudoULift) F where
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
