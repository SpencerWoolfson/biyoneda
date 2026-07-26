import Mathlib.CategoryTheory.Bicategory.Product
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Bicategory.Yoneda
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.Tactic.CategoryTheory.Bicategory.Basic
import Mathlib.Tactic.CategoryTheory.Slice
import Biyoneda.ForMathlib

/-!
# Bicategorical Yoneda Lemma

This file formalises the Yoneda lemma for bicategories.  Given a bicategory `B` with Yoneda
embedding `yoneda : B ⥤ᵖ Bᵒᵖ ⥤ᵖ Cat` (see `Bicategory.yoneda`), we construct a bicategorical
equivalence

  `StrongTrans (yoneda₀ b) F  ≃  F.obj b`

natural in `b : Bᵒᵖ` and `F : Bᵒᵖ ⥤ᵖ Cat`.

## Main definitions

* `yonedaPairing : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat) ⥤ᵖ Cat` — the pseudofunctor sending `(b, F)` to
  the category of strong transformations `StrongTrans (yoneda₀ b) F`.
* `yonedaEvaluation : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat) ⥤ᵖ Cat` — the pseudofunctor sending `(b, F)`
  to the category `F.obj b`.
* `yonedaLemmaForwards : yonedaPairing ⟶ yonedaEvaluation` — the "evaluate at identity"
  strong transformation, sending `η : yoneda₀ b ⟶ F` to `η.app b (𝟙 b)`.
* `yonedaLemmaBackwards : yonedaEvaluation ⟶ yonedaPairing` — the inverse strong
  transformation, sending `s : F.obj b` to the strong transformation `(a, f) ↦ F.map f s`.
* `yonedaLemma : BiEquiv yonedaPairing yonedaEvaluation` — the Yoneda lemma assembled as
  a `BiEquiv` (an internal equivalence in the bicategory of pseudofunctors).

## Universe notes

`yonedaEvaluation'` lands in `Cat.{w, v}` while `yonedaPairing` lands in
`Cat.{max u (max v w), max u (max v w)}`.  The auxiliary pseudofunctor `catPseudoULift` is
used to promote `yonedaEvaluation'` to the correct universe level, yielding `yonedaEvaluation`.
-/

-- Sorry Count (11)

open CategoryTheory Bicategory Bicategory.Opposite Opposite Pseudofunctor StrongTrans Functor
open scoped Pseudofunctor.StrongTrans

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

variable {B : Type u} [Bicategory.{w, v} B]

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

universe w₁

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

/-- `postcomp₂` at an identity 1-morphism is isomorphic to the identity strong transformation.
This is `Bicategory.yoneda.mapId` restated for `postcomp₂`. -/
def postcompId₂ (a : B) : postcomp₂ (𝟙 a) ≅ 𝟙 (yoneda₀ a) := by
  let := Bicategory.yoneda.mapId a
  dsimp [yoneda, postcomposing₂] at this
  exact this

/-- `postcomp₂` is functorial in the 1-morphism, up to isomorphism: `postcomp₂ (f ≫ g)` is
isomorphic to `postcomp₂ f ≫ postcomp₂ g`.  This is `Bicategory.yoneda.mapComp` restated. -/
def postcompComp₂ {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    postcomp₂ (f ≫ g) ≅ postcomp₂ f ≫ postcomp₂ g := by
  let := Bicategory.yoneda.mapComp f g
  dsimp [yoneda, postcomposing₂] at this
  exact this

/--
The functor underlying `yonedaPairing.map f`, expressed as the composite of the
"postcompose with `f.2`" functor and the "precompose with `postcomp₂ f.1.unop`" functor
on hom-categories of the pseudofunctor bicategory.

Its action agrees definitionally with the functor used in `yonedaPairing.map`
(`η ↦ postcomp₂ f.1.unop ≫ η ≫ f.2`); phrasing it as a composite of the `precomposing` and
`postcomposing` functors makes functoriality and naturality properties available for free.
-/
def yonedaPairingMapFunctor {x y : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : x ⟶ y) :
    (yoneda₀ (unop x.1) ⟶ x.2) ⥤ (yoneda₀ (unop y.1) ⟶ y.2) :=
  (postcomposing (yoneda₀ (unop x.1)) x.2 y.2).obj f.2 ⋙
    (precomposing (yoneda₀ (unop y.1)) (yoneda₀ (unop x.1)) y.2).obj (postcomp₂ f.1.unop)

/--
The natural transformation underlying `yonedaPairing.map₂ η`, built by whiskering the
images of `η.1` and `η.2` under `precomposing`/`postcomposing`.  Because it is assembled
from whiskerings of natural transformations, naturality is automatic, and its components
agree definitionally with `(h1 ▷ (a ≫ f.2)) ≫ postcomp₂ g.1.unop ◁ (a ◁ h2)` as used in
`yonedaPairing.map₂`.
-/
def yonedaPairingMap₂ {x y : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} {f g : x ⟶ y} (η : f ⟶ g) :
    yonedaPairingMapFunctor f ⟶ yonedaPairingMapFunctor g :=
  Functor.whiskerLeft ((postcomposing (yoneda₀ (unop x.1)) x.2 y.2).obj f.2)
      ((precomposing (yoneda₀ (unop y.1)) (yoneda₀ (unop x.1)) y.2).map
        ((postcomposing₂ (unop y.1) (unop x.1)).map η.1.unop2)) ≫
    Functor.whiskerRight ((postcomposing (yoneda₀ (unop x.1)) x.2 y.2).map η.2)
      ((precomposing (yoneda₀ (unop y.1)) (yoneda₀ (unop x.1)) y.2).obj (postcomp₂ g.1.unop))

/-- `yonedaPairingMap₂ η` is the horizontal composition of the whiskering transformations
induced by `η.2` and `η.1`. -/
lemma yonedaPairingMap₂_hcomp {x y : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} {f g : x ⟶ y} (η : f ⟶ g) :
    yonedaPairingMap₂ η =
      ((postcomposing (yoneda₀ (unop x.1)) x.2 y.2).map η.2) ◫
        ((precomposing (yoneda₀ (unop y.1)) (yoneda₀ (unop x.1)) y.2).map
          ((postcomposing₂ (unop y.1) (unop x.1)).map η.1.unop2)) :=
  (NatTrans.hcomp_eq_whiskerLeft_comp_whiskerRight _ _).symm

/-- `yonedaPairingMap₂` sends identity 2-morphisms to the identity. -/
lemma yonedaPairingMap₂_id {x y : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : x ⟶ y) :
    yonedaPairingMap₂ (𝟙 f) = 𝟙 (yonedaPairingMapFunctor f) := by
  dsimp only [yonedaPairingMap₂]
  rw [show (𝟙 f : f ⟶ f).1 = 𝟙 f.1 from rfl, show (𝟙 f : f ⟶ f).2 = 𝟙 f.2 from rfl,
    unop2_id, Functor.map_id, Functor.map_id]
  erw [(precomposing (yoneda₀ (unop y.1)) (yoneda₀ (unop x.1)) y.2).map_id]
  erw [Functor.whiskerLeft_id', Functor.whiskerRight_id', Category.comp_id]
  rfl

/-- `yonedaPairingMap₂` is compatible with vertical composition of 2-morphisms. -/
lemma yonedaPairingMap₂_comp {x y : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} {f g h : x ⟶ y}
    (η : f ⟶ g) (θ : g ⟶ h) :
    yonedaPairingMap₂ (η ≫ θ) = yonedaPairingMap₂ η ≫ yonedaPairingMap₂ θ := by
  simp only [yonedaPairingMap₂_hcomp]
  rw [show (η ≫ θ).1 = η.1 ≫ θ.1 from rfl, show (η ≫ θ).2 = η.2 ≫ θ.2 from rfl,
    unop2_comp, Functor.map_comp, Functor.map_comp]
  erw [(precomposing (yoneda₀ (unop y.1)) (yoneda₀ (unop x.1)) y.2).map_comp]
  rw [NatTrans.exchange]
  rfl

/--
The *pairing pseudofunctor* `Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat) ⥤ᵖ Cat`.

This is the left-hand side of the Yoneda equivalence, encoding "strong transformations out of
the Yoneda embedding":

* **On objects**: `(b, F) ↦ StrongTrans (yoneda₀ b) F` — the category whose objects are strong
  transformations `yoneda₀ b ⟶ F` and whose morphisms are modifications between them.
* **On 1-morphisms**: a pair `(f : b' ⟶ b, α : F ⟶ G)` acts on a strong transformation `η`
  by `η ↦ postcomp₂ f ≫ η ≫ α` — precomposing with the Yoneda image of `f` and
  postcomposing with `α`.
* **On 2-morphisms**: a pair `(σ : f ⟶ f', τ : α ⟶ β)` acts by left- and right-whiskering
  the corresponding postcomposing transformations.
-/
def yonedaPairing : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v}) ⥤ᵖ Cat.{max u (max v w), max u (max v w)} where
  obj x := @Cat.of (Pseudofunctor.StrongTrans (yoneda₀ x.fst.unop) x.snd)
    (Pseudofunctor.StrongTrans.homCategory)
  map {x y} f := by
    apply Functor.toCatHom
      { obj η := Bicategory.postcomp₂ f.1.unop ≫ (η ≫ f.2)
        map m := StrongTrans.whiskerLeft (Bicategory.postcomp₂ f.1.unop)
          (StrongTrans.whiskerRight m f.2) }
  map₂ {x y f g} η := NatTrans.toCatHom₂ (yonedaPairingMap₂ η)
  mapId x := by
    refine Cat.Hom.isoMk (NatIso.ofComponents ?_ ?_)
    · intro X
      refine Iso.trans (postcompId₂ (unop x.1) ▷ᵢ (X ≫ 𝟙 x.2)) ?_
      exact (bicategoricalIso X (𝟙 (yoneda₀ (unop x.1)) ≫ X ≫ 𝟙 x.2)).symm
    · intro X Y f
      apply homCategory.ext
      intro b
      dsimp
      -- naturality of `mapId`'s component iso: `f` passes the coherence 2-cell by interchange
      simp only [Bicategory.whisker_exchange_assoc]
      bicategory
  mapComp f g := by
    refine Cat.Hom.isoMk ?_
    refine NatIso.ofComponents ?_ ?_
    · intro x
      refine ?_ ≪≫ (α_ _ _ _)
      refine (α_ (postcomp₂ (g.1.unop ≫ f.1.unop)) x (f.2 ≫ g.2)).symm ≪≫ ?_
      refine (α_ (postcomp₂ (g.1.unop ≫ f.1.unop) ≫ x) f.2 g.2).symm ≪≫ ?_
      refine (?_ ▷ᵢ g.2)
      refine (α_ (postcomp₂ (g.1.unop ≫ f.1.unop)) x f.2) ≪≫ ?_
      refine ?_ ≪≫ (α_ _ _ _)
      refine (?_ ▷ᵢ (x ≫ f.2))
      apply postcompComp₂
    · intro X Y f
      apply homCategory.ext
      intro b
      dsimp
      sorry
  map₂_id {a b} X := congrArg NatTrans.toCatHom₂ (yonedaPairingMap₂_id X)
  map₂_comp {a b f g h} η θ := congrArg NatTrans.toCatHom₂ (yonedaPairingMap₂_comp η θ)

/-- The cancellation core of `yonedaEvaluation'.map₂_left_unitor`, at a point `Z`. -/
lemma evaluation_left_unitor_core {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b)
    (Z : ↑(a.2.obj a.1)) :
    (b.2.map (𝟙 a.1 ≫ f.1)).toFunctor.map
        (((λ_ f).hom.2.as.app a.1).toNatTrans.app Z) ≫
      (b.2.map₂ (λ_ f.1).hom).toNatTrans.app ((f.2.app a.1).toFunctor.obj Z) =
    ((b.2.mapComp (𝟙 a.1) f.1).hom.toNatTrans.app ((f.2.app a.1).toFunctor.obj Z) ≫
      𝟙 ((b.2.map f.1).toFunctor.obj
        ((b.2.map (𝟙 a.1)).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z))) ≫
      𝟙 ((b.2.map f.1).toFunctor.obj
        ((b.2.map (𝟙 a.1)).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z))) ≫
      (b.2.map f.1).toFunctor.map
        ((f.2.naturality (𝟙 a.1)).inv.toNatTrans.app Z)) ≫
      (b.2.map f.1).toFunctor.map
        ((f.2.app a.1).toFunctor.map ((a.2.mapId a.1).hom.toNatTrans.app Z)) := by
  have hw := Cat.Hom₂.congr_app (b.2.map₂_left_unitor f.1) ((f.2.app a.1).toFunctor.obj Z)
  dsimp at hw
  have hid := Pseudofunctor.StrongTrans.naturality_id_hom_app f.2 a.1 Z
  dsimp at hid
  simp only [Category.id_comp]
  have hl : ((λ_ f).hom.2.as.app a.1).toNatTrans.app Z =
      𝟙 ((f.2.app a.1).toFunctor.obj Z) := rfl
  have c1 := Cat.Hom.inv_hom_id_toNatTrans_app (b.2.mapId a.1) ((f.2.app a.1).toFunctor.obj Z)
  have key : (f.2.naturality (𝟙 a.1)).inv.toNatTrans.app Z ≫
      (f.2.app a.1).toFunctor.map ((a.2.mapId a.1).hom.toNatTrans.app Z) =
      (b.2.mapId a.1).hom.toNatTrans.app ((f.2.app a.1).toFunctor.obj Z) := by
    apply (Iso.inv_comp_eq ((Cat.Hom.toNatIso (f.2.naturality (𝟙 a.1))).app Z)).mpr
    show (f.2.app a.1).toFunctor.map ((a.2.mapId a.1).hom.toNatTrans.app Z) =
      (f.2.naturality (𝟙 a.1)).hom.toNatTrans.app Z ≫
      (b.2.mapId a.1).hom.toNatTrans.app ((f.2.app a.1).toFunctor.obj Z)
    rw [hid]
    simp only [Category.id_comp]
    erw [Category.assoc]
    erw [c1]
    erw [Category.comp_id]
    rfl
  erw [hl]
  erw [Functor.map_id]
  erw [Category.id_comp]
  erw [hw]
  simp only [Category.assoc]
  erw [← Functor.map_comp]
  erw [key]
  erw [Category.comp_id]
  erw [Category.id_comp]
  rfl

/-- The cancellation core of `yonedaEvaluation'.map₂_right_unitor`, at a point `Z`. -/
lemma evaluation_right_unitor_core {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b)
    (Z : ↑(a.2.obj a.1)) :
    (b.2.map (f.1 ≫ 𝟙 b.1)).toFunctor.map
        (((ρ_ f).hom.2.as.app a.1).toNatTrans.app Z) ≫
      (b.2.map₂ (ρ_ f.1).hom).toNatTrans.app ((f.2.app a.1).toFunctor.obj Z) =
    ((b.2.mapComp f.1 (𝟙 b.1)).hom.toNatTrans.app ((f.2.app a.1).toFunctor.obj Z) ≫
      𝟙 ((b.2.map (𝟙 b.1)).toFunctor.obj
        ((b.2.map f.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z))) ≫
      (𝟙 ((b.2.map (𝟙 b.1)).toFunctor.obj
          ((b.2.map f.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z))) ≫
        (b.2.map (𝟙 b.1)).toFunctor.map
          (((𝟙 b.2 : b.2 ⟶ b.2).naturality f.1).inv.toNatTrans.app
            ((f.2.app a.1).toFunctor.obj Z)) ≫
        𝟙 ((b.2.map (𝟙 b.1)).toFunctor.obj
          ((b.2.map f.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z)))) ≫
      𝟙 ((b.2.map (𝟙 b.1)).toFunctor.obj
        ((b.2.map f.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z)))) ≫
      (b.2.mapId b.1).hom.toNatTrans.app
        ((b.2.map f.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z)) ≫
      𝟙 ((b.2.map f.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z)) := by
  have hw := Cat.Hom₂.congr_app (b.2.map₂_right_unitor f.1) ((f.2.app a.1).toFunctor.obj Z)
  dsimp at hw
  have hr : ((ρ_ f).hom.2.as.app a.1).toNatTrans.app Z =
      𝟙 ((f.2.app a.1).toFunctor.obj Z) := rfl
  have hidt : ((𝟙 b.2 : b.2 ⟶ b.2).naturality f.1).inv.toNatTrans.app
      ((f.2.app a.1).toFunctor.obj Z) =
      𝟙 ((b.2.map f.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z)) := by
    first
      | rfl
      | simp
  erw [hr]
  erw [Functor.map_id]
  erw [Category.id_comp]
  erw [hw]
  erw [hidt]
  erw [Functor.map_id]
  simp only [Category.id_comp, Category.comp_id, Category.assoc]
  iterate 6 (first | erw [Category.id_comp] | erw [Category.comp_id] | skip)
  rfl

/-- The cancellation core of `yonedaEvaluation'.map₂_whisker_right`, at a point `Z`. -/
lemma evaluation_whisker_right_core {a b c : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} {f g : a ⟶ b}
    (h : f ⟶ g) (η : b ⟶ c) (Z : ↑(a.2.obj a.1)) :
    ((c.2.mapComp f.1 η.1).hom.toNatTrans.app
        ((η.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z)) ≫
      (c.2.map η.1).toFunctor.map ((c.2.map f.1).toFunctor.map
        ((h.2.as.app a.1 ▷ η.2.app a.1).toNatTrans.app Z))) ≫
      (c.2.map η.1).toFunctor.map ((c.2.map₂ h.1).toNatTrans.app
        ((η.2.app a.1).toFunctor.obj ((g.2.app a.1).toFunctor.obj Z))) ≫
      (c.2.mapComp g.1 η.1).inv.toNatTrans.app
        ((η.2.app a.1).toFunctor.obj ((g.2.app a.1).toFunctor.obj Z)) =
    ((c.2.mapComp f.1 η.1).hom.toNatTrans.app
        ((η.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z)) ≫
      (c.2.map η.1).toFunctor.map
        ((η.2.naturality f.1).inv.toNatTrans.app ((f.2.app a.1).toFunctor.obj Z))) ≫
      (η.2.app b.1 ≫ c.2.map η.1).toFunctor.map
        ((b.2.map f.1).toFunctor.map ((h.2.as.app a.1).toNatTrans.app Z) ≫
          (b.2.map₂ h.1).toNatTrans.app ((g.2.app a.1).toFunctor.obj Z)) ≫
      (c.2.map η.1).toFunctor.map
        ((η.2.naturality g.1).hom.toNatTrans.app ((g.2.app a.1).toFunctor.obj Z)) ≫
      (c.2.mapComp g.1 η.1).inv.toNatTrans.app
        ((η.2.app a.1).toFunctor.obj ((g.2.app a.1).toFunctor.obj Z)) := by
  have hnn := Cat.Hom₂.congr_app (η.2.naturality_naturality h.1)
    ((g.2.app a.1).toFunctor.obj Z)
  dsimp at hnn
  have hs : (η.2.naturality f.1).inv.toNatTrans.app ((f.2.app a.1).toFunctor.obj Z) ≫
      (η.2.app b.1).toFunctor.map
        ((b.2.map f.1).toFunctor.map ((h.2.as.app a.1).toNatTrans.app Z)) =
      (c.2.map f.1).toFunctor.map
        ((η.2.app a.1).toFunctor.map ((h.2.as.app a.1).toNatTrans.app Z)) ≫
      (η.2.naturality f.1).inv.toNatTrans.app ((g.2.app a.1).toFunctor.obj Z) :=
    ((η.2.naturality f.1).inv.toNatTrans.naturality
      ((h.2.as.app a.1).toNatTrans.app Z)).symm
  have c1' := Cat.Hom.inv_hom_id_toNatTrans_app_assoc (η.2.naturality f.1)
    ((g.2.app a.1).toFunctor.obj Z)
    ((c.2.map₂ h.1).toNatTrans.app ((η.2.app a.1).toFunctor.obj ((g.2.app a.1).toFunctor.obj Z)))
  simp only [Category.assoc]
  rw [Functor.map_comp]
  rw [Cat.Hom.comp_map, Cat.Hom.comp_map]
  have hnnG := congrArg (fun m ↦ (c.2.map η.1).toFunctor.map m) hnn
  simp only [Functor.map_comp] at hnnG
  have hsG := congrArg (fun m ↦ (c.2.map η.1).toFunctor.map m) hs
  simp only [Functor.map_comp] at hsG
  slice_rhs 3 4 =>
    erw [Category.assoc]
    erw [hnnG]
  slice_rhs 2 3 => erw [hsG]
  simp only [← Functor.map_comp]
  have key : (c.2.map η.1).toFunctor.map
        ((c.2.map f.1).toFunctor.map
          ((η.2.app a.1).toFunctor.map ((h.2.as.app a.1).toNatTrans.app Z)) ≫
          (η.2.naturality f.1).inv.toNatTrans.app ((g.2.app a.1).toFunctor.obj Z)) ≫
      (c.2.map η.1).toFunctor.map
        ((η.2.naturality f.1).hom.toNatTrans.app ((g.2.app a.1).toFunctor.obj Z) ≫
          (c.2.map₂ h.1).toNatTrans.app
            ((η.2.app a.1).toFunctor.obj ((g.2.app a.1).toFunctor.obj Z))) =
      (c.2.map η.1).toFunctor.map
        ((c.2.map f.1).toFunctor.map ((h.2.as.app a.1 ▷ η.2.app a.1).toNatTrans.app Z)) ≫
      (c.2.map η.1).toFunctor.map
        ((c.2.map₂ h.1).toNatTrans.app
          ((η.2.app a.1).toFunctor.obj ((g.2.app a.1).toFunctor.obj Z))) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    refine congrArg _ ?_
    rw [Category.assoc]
    erw [c1']
    rfl
  erw [key]
  erw [Category.assoc]
  rfl

/-- The cancellation core of `yonedaEvaluation'.map₂_whisker_left`, at a point `Z`. -/
lemma evaluation_whisker_left_core {a b c : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b)
    {g h : b ⟶ c} (η : g ⟶ h) (Z : ↑(a.2.obj a.1)) :
    ((c.2.mapComp f.1 g.1).hom.toNatTrans.app
        ((g.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z)) ≫
      (c.2.map g.1).toFunctor.map ((c.2.map f.1).toFunctor.map
        ((η.2.as.app a.1).toNatTrans.app ((f.2.app a.1).toFunctor.obj Z)))) ≫
      (c.2.map₂ η.1).toNatTrans.app
        ((c.2.map f.1).toFunctor.obj
          ((h.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z))) ≫
      (c.2.mapComp f.1 h.1).inv.toNatTrans.app
        ((h.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z)) =
    (c.2.mapComp f.1 g.1).hom.toNatTrans.app
        ((g.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z)) ≫
      (c.2.map g.1).toFunctor.map
        ((g.2.naturality f.1).inv.toNatTrans.app ((f.2.app a.1).toFunctor.obj Z)) ≫
      ((c.2.map g.1).toFunctor.map
          ((η.2.as.app b.1).toNatTrans.app
            ((b.2.map f.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z))) ≫
        (c.2.map₂ η.1).toNatTrans.app
          ((h.2.app b.1).toFunctor.obj
            ((b.2.map f.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z)))) ≫
      (c.2.map h.1).toFunctor.map
        ((h.2.naturality f.1).hom.toNatTrans.app ((f.2.app a.1).toFunctor.obj Z)) ≫
      (c.2.mapComp f.1 h.1).inv.toNatTrans.app
        ((h.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z)) := by
  have h2 := modification_naturality_app η.2 f.1 ((f.2.app a.1).toFunctor.obj Z)
  have h3 : (c.2.map g.1).toFunctor.map
        ((h.2.naturality f.1).hom.toNatTrans.app ((f.2.app a.1).toFunctor.obj Z)) ≫
      (c.2.map₂ η.1).toNatTrans.app
        ((c.2.map f.1).toFunctor.obj
          ((h.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z))) =
      (c.2.map₂ η.1).toNatTrans.app
        ((h.2.app b.1).toFunctor.obj
          ((b.2.map f.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z))) ≫
      (c.2.map h.1).toFunctor.map
        ((h.2.naturality f.1).hom.toNatTrans.app ((f.2.app a.1).toFunctor.obj Z)) :=
    (c.2.map₂ η.1).toNatTrans.naturality
      ((h.2.naturality f.1).hom.toNatTrans.app ((f.2.app a.1).toFunctor.obj Z))
  simp only [Category.assoc]
  slice_rhs 4 5 => rw [← h3]
  slice_rhs 3 4 =>
    erw [← Category.assoc]
    erw [← Functor.map_comp]
  erw [h2]
  slice_rhs 2 3 => erw [← Functor.map_comp]
  have c1' := Cat.Hom.inv_hom_id_toNatTrans_app_assoc (g.2.naturality f.1)
    ((f.2.app a.1).toFunctor.obj Z)
    ((c.2.map f.1).toFunctor.map
      ((η.2.as.app a.1).toNatTrans.app ((f.2.app a.1).toFunctor.obj Z)))
  erw [c1']
  simp only [Category.assoc]
  rfl

set_option maxHeartbeats 800000 in
-- the `show` re-spelling and the `exact`-plug both bridge composite/nested point
-- spellings by defeq at default transparency
/-- The cancellation core of `yonedaEvaluation'.map₂_associator`, at a point `Z`. -/
lemma evaluation_associator_core {a b c d : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})}
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (Z : ↑(a.2.obj a.1)) :
    (d.2.map ((f.1 ≫ g.1) ≫ h.1)).toFunctor.map
        (((α_ f g h).hom.2.as.app a.1).toNatTrans.app Z) ≫
      (d.2.map₂ (α_ f.1 g.1 h.1).hom).toNatTrans.app
        ((h.2.app a.1).toFunctor.obj
          ((g.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z))) =
    ((d.2.mapComp (f.1 ≫ g.1) h.1).hom.toNatTrans.app
        ((h.2.app a.1).toFunctor.obj
          ((g.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z))) ≫
      ((d.2.map h.1).toFunctor.map
            ((h.2.naturality (f.1 ≫ g.1)).inv.toNatTrans.app
              ((g.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z))) ≫
          𝟙 ((d.2.map h.1).toFunctor.obj
            ((h.2.app c.1).toFunctor.obj
              ((c.2.map (f.1 ≫ g.1)).toFunctor.obj
                ((g.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z)))))) ≫
        𝟙 ((d.2.map h.1).toFunctor.obj
          ((h.2.app c.1).toFunctor.obj
            ((c.2.map (f.1 ≫ g.1)).toFunctor.obj
              ((g.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z)))))) ≫
      (h.2.app c.1 ≫ d.2.map h.1).toFunctor.map
          ((c.2.mapComp f.1 g.1).hom.toNatTrans.app
              ((g.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z)) ≫
            ((c.2.map g.1).toFunctor.map
                  ((g.2.naturality f.1).inv.toNatTrans.app ((f.2.app a.1).toFunctor.obj Z)) ≫
                𝟙 ((c.2.map g.1).toFunctor.obj
                  ((g.2.app b.1).toFunctor.obj
                    ((b.2.map f.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z))))) ≫
              𝟙 ((c.2.map g.1).toFunctor.obj
                ((g.2.app b.1).toFunctor.obj
                  ((b.2.map f.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z))))) ≫
        ((((d.2.map h.1).toFunctor.map
                  ((h.2.naturality g.1).hom.toNatTrans.app
                    ((g.2.app b.1).toFunctor.obj
                      ((b.2.map f.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z)))) ≫
                𝟙 ((d.2.map h.1).toFunctor.obj
                  ((d.2.map g.1).toFunctor.obj
                    ((h.2.app b.1).toFunctor.obj
                      ((g.2.app b.1).toFunctor.obj
                        ((b.2.map f.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z))))))) ≫
              𝟙 ((d.2.map h.1).toFunctor.obj
                ((d.2.map g.1).toFunctor.obj
                  ((h.2.app b.1).toFunctor.obj
                    ((g.2.app b.1).toFunctor.obj
                      ((b.2.map f.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z))))))) ≫
            (d.2.mapComp g.1 h.1).inv.toNatTrans.app
              ((h.2.app b.1).toFunctor.obj
                ((g.2.app b.1).toFunctor.obj
                  ((b.2.map f.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z))))) ≫
          (((𝟙 ((d.2.map (g.1 ≫ h.1)).toFunctor.obj
                  ((h.2.app b.1).toFunctor.obj
                    ((g.2.app b.1).toFunctor.obj
                      ((b.2.map f.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z))))) ≫
                (d.2.map (g.1 ≫ h.1)).toFunctor.map
                  (((g.2 ≫ h.2).naturality f.1).hom.toNatTrans.app
                    ((f.2.app a.1).toFunctor.obj Z))) ≫
              𝟙 ((d.2.map (g.1 ≫ h.1)).toFunctor.obj
                ((d.2.map f.1).toFunctor.obj
                  ((h.2.app a.1).toFunctor.obj
                    ((g.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z)))))) ≫
            𝟙 ((d.2.map (g.1 ≫ h.1)).toFunctor.obj
              ((d.2.map f.1).toFunctor.obj
                ((h.2.app a.1).toFunctor.obj
                  ((g.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z)))))) ≫
        (d.2.mapComp f.1 (g.1 ≫ h.1)).inv.toNatTrans.app
          ((h.2.app a.1).toFunctor.obj
            ((g.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z))) := by
  have hα : ((α_ f g h).hom.2.as.app a.1).toNatTrans.app Z = 𝟙 _ := rfl
  rw [hα]
  erw [Functor.map_id]
  erw [Category.id_comp]
  have hw := Cat.Hom₂.congr_app (d.2.map₂_associator f.1 g.1 h.1)
    ((h.2.app a.1).toFunctor.obj ((g.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z)))
  dsimp at hw
  erw [hw]
  rw [Pseudofunctor.StrongTrans.naturality_comp_inv_app h.2 f.1 g.1
    ((g.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z))]
  have hD := Cat.Hom₂.congr_app
    (Pseudofunctor.StrongTrans.categoryStruct_comp_naturality_hom g.2 h.2 f.1)
    ((f.2.app a.1).toFunctor.obj Z)
  rw [hD]
  simp only [Category.id_comp, Category.comp_id, Category.assoc, Functor.map_comp,
    Cat.Hom.comp_map]
  iterate 12 (first | erw [eqToHom_refl] | erw [Category.id_comp] | erw [Category.comp_id] | skip)
  have hsplit : ((g.2.naturality f.1).hom ▷ h.2.app b.1 ≫
      g.2.app a.1 ◁ (h.2.naturality f.1).hom).toNatTrans.app
        ((f.2.app a.1).toFunctor.obj Z) =
      (h.2.app b.1).toFunctor.map
        ((g.2.naturality f.1).hom.toNatTrans.app ((f.2.app a.1).toFunctor.obj Z)) ≫
      (h.2.naturality f.1).hom.toNatTrans.app
        ((g.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z)) := rfl
  erw [hsplit]
  simp only [← Functor.map_comp]
  show (d.2.mapComp (f.1 ≫ g.1) h.1).hom.toNatTrans.app
        ((h.2.app a.1).toFunctor.obj
          ((g.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z))) ≫
      (d.2.map h.1).toFunctor.map
        ((d.2.mapComp f.1 g.1).hom.toNatTrans.app
          ((h.2.app a.1).toFunctor.obj
            ((g.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z)))) ≫
      (d.2.mapComp g.1 h.1).inv.toNatTrans.app
        ((d.2.map f.1).toFunctor.obj
          ((h.2.app a.1).toFunctor.obj
            ((g.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z)))) ≫
      (d.2.mapComp f.1 (g.1 ≫ h.1)).inv.toNatTrans.app
        ((h.2.app a.1).toFunctor.obj
          ((g.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z))) =
    (d.2.mapComp (f.1 ≫ g.1) h.1).hom.toNatTrans.app
        ((h.2.app a.1).toFunctor.obj
          ((g.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z))) ≫
      (d.2.map h.1).toFunctor.map
        ((d.2.mapComp f.1 g.1).hom.toNatTrans.app
            ((h.2.app a.1).toFunctor.obj
              ((g.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z))) ≫
          (d.2.map g.1).toFunctor.map
            ((h.2.naturality f.1).inv.toNatTrans.app
              ((g.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z))) ≫
          (h.2.naturality g.1).inv.toNatTrans.app
            ((c.2.map f.1).toFunctor.obj
              ((g.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z))) ≫
          (h.2.app c.1).toFunctor.map
            ((c.2.mapComp f.1 g.1).inv.toNatTrans.app
              ((g.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z)))) ≫
      (d.2.map h.1).toFunctor.map
        ((h.2.app c.1).toFunctor.map
          ((c.2.mapComp f.1 g.1).hom.toNatTrans.app
              ((g.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z)) ≫
            (c.2.map g.1).toFunctor.map
              ((g.2.naturality f.1).inv.toNatTrans.app ((f.2.app a.1).toFunctor.obj Z)) ≫
            𝟙 ((c.2.map g.1).toFunctor.obj
              ((g.2.app b.1).toFunctor.obj
                ((b.2.map f.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z)))))) ≫
      (d.2.map h.1).toFunctor.map
        ((h.2.naturality g.1).hom.toNatTrans.app
          ((g.2.app b.1).toFunctor.obj
            ((b.2.map f.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z)))) ≫
      (d.2.mapComp g.1 h.1).inv.toNatTrans.app
        ((h.2.app b.1).toFunctor.obj
          ((g.2.app b.1).toFunctor.obj
            ((b.2.map f.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z)))) ≫
      (d.2.map (g.1 ≫ h.1)).toFunctor.map
        ((h.2.app b.1).toFunctor.map
            ((g.2.naturality f.1).hom.toNatTrans.app ((f.2.app a.1).toFunctor.obj Z)) ≫
          (h.2.naturality f.1).hom.toNatTrans.app
            ((g.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z))) ≫
      (d.2.mapComp f.1 (g.1 ≫ h.1)).inv.toNatTrans.app
        ((h.2.app a.1).toFunctor.obj
          ((g.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z)))
  rw [← Functor.map_comp_assoc]
  first
    | rw [← Functor.map_comp_assoc]
    | erw [← Functor.map_comp_assoc]
  simp only [Category.assoc]
  first
    | rw [← Functor.map_comp_assoc]
    | erw [← Functor.map_comp_assoc]
  first
    | rw [Cat.Hom.inv_hom_id_toNatTrans_app_assoc]
    | erw [Cat.Hom.inv_hom_id_toNatTrans_app_assoc]
  first
    | rw [Category.comp_id]
    | erw [Category.comp_id]
  have key1 : (h.2.naturality g.1).inv.toNatTrans.app
        ((c.2.map f.1).toFunctor.obj
          ((g.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z))) ≫
      (h.2.app c.1).toFunctor.map ((c.2.map g.1).toFunctor.map
        ((g.2.naturality f.1).inv.toNatTrans.app ((f.2.app a.1).toFunctor.obj Z))) ≫
      (h.2.naturality g.1).hom.toNatTrans.app
        ((g.2.app b.1).toFunctor.obj
          ((b.2.map f.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z))) =
      (d.2.map g.1).toFunctor.map ((h.2.app b.1).toFunctor.map
        ((g.2.naturality f.1).inv.toNatTrans.app ((f.2.app a.1).toFunctor.obj Z))) := by
    have hn : (h.2.naturality g.1).inv.toNatTrans.app
          ((c.2.map f.1).toFunctor.obj
            ((g.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z))) ≫
        (h.2.app c.1).toFunctor.map ((c.2.map g.1).toFunctor.map
          ((g.2.naturality f.1).inv.toNatTrans.app ((f.2.app a.1).toFunctor.obj Z))) =
        (d.2.map g.1).toFunctor.map ((h.2.app b.1).toFunctor.map
          ((g.2.naturality f.1).inv.toNatTrans.app ((f.2.app a.1).toFunctor.obj Z))) ≫
        (h.2.naturality g.1).inv.toNatTrans.app
          ((g.2.app b.1).toFunctor.obj
            ((b.2.map f.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z))) :=
      ((h.2.naturality g.1).inv.toNatTrans.naturality
        ((g.2.naturality f.1).inv.toNatTrans.app ((f.2.app a.1).toFunctor.obj Z))).symm
    rw [← Category.assoc]
    erw [hn]
    first | rw [Category.assoc] | erw [Category.assoc]
    erw [Cat.Hom.inv_hom_id_toNatTrans_app]
    first | rw [Category.comp_id] | erw [Category.comp_id]
  erw [key1]
  erw [← Functor.map_comp]
  erw [Functor.map_comp]
  simp only [Category.assoc]
  have key2 : (d.2.map h.1).toFunctor.map ((d.2.map g.1).toFunctor.map
        ((h.2.naturality f.1).inv.toNatTrans.app
          ((g.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z)) ≫
         (h.2.app b.1).toFunctor.map
          ((g.2.naturality f.1).inv.toNatTrans.app ((f.2.app a.1).toFunctor.obj Z)))) ≫
      (d.2.mapComp g.1 h.1).inv.toNatTrans.app
        ((h.2.app b.1).toFunctor.obj
          ((g.2.app b.1).toFunctor.obj
            ((b.2.map f.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z)))) ≫
      (d.2.map (g.1 ≫ h.1)).toFunctor.map
        ((h.2.app b.1).toFunctor.map
          ((g.2.naturality f.1).hom.toNatTrans.app ((f.2.app a.1).toFunctor.obj Z)) ≫
         (h.2.naturality f.1).hom.toNatTrans.app
          ((g.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z))) ≫
      (d.2.mapComp f.1 (g.1 ≫ h.1)).inv.toNatTrans.app
        ((h.2.app a.1).toFunctor.obj
          ((g.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z))) =
      (d.2.mapComp g.1 h.1).inv.toNatTrans.app
        ((d.2.map f.1).toFunctor.obj
          ((h.2.app a.1).toFunctor.obj
            ((g.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z)))) ≫
      (d.2.mapComp f.1 (g.1 ≫ h.1)).inv.toNatTrans.app
        ((h.2.app a.1).toFunctor.obj
          ((g.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z))) := by
    have hn2 : (d.2.map h.1).toFunctor.map ((d.2.map g.1).toFunctor.map
          ((h.2.naturality f.1).inv.toNatTrans.app
            ((g.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z)) ≫
           (h.2.app b.1).toFunctor.map
            ((g.2.naturality f.1).inv.toNatTrans.app ((f.2.app a.1).toFunctor.obj Z)))) ≫
        (d.2.mapComp g.1 h.1).inv.toNatTrans.app
          ((h.2.app b.1).toFunctor.obj
            ((g.2.app b.1).toFunctor.obj
              ((b.2.map f.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z)))) =
        (d.2.mapComp g.1 h.1).inv.toNatTrans.app
          ((d.2.map f.1).toFunctor.obj
            ((h.2.app a.1).toFunctor.obj
              ((g.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z)))) ≫
        (d.2.map (g.1 ≫ h.1)).toFunctor.map
          ((h.2.naturality f.1).inv.toNatTrans.app
            ((g.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z)) ≫
           (h.2.app b.1).toFunctor.map
            ((g.2.naturality f.1).inv.toNatTrans.app ((f.2.app a.1).toFunctor.obj Z))) :=
      (d.2.mapComp g.1 h.1).inv.toNatTrans.naturality
        ((h.2.naturality f.1).inv.toNatTrans.app
          ((g.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z)) ≫
         (h.2.app b.1).toFunctor.map
          ((g.2.naturality f.1).inv.toNatTrans.app ((f.2.app a.1).toFunctor.obj Z)))
    rw [← Category.assoc]
    erw [hn2]
    first | rw [Category.assoc] | erw [Category.assoc]
    erw [← Functor.map_comp_assoc]
    simp only [Category.assoc]
    erw [← Functor.map_comp_assoc]
    erw [Cat.Hom.inv_hom_id_toNatTrans_app]
    first | rw [Functor.map_id] | erw [Functor.map_id]
    erw [Category.id_comp]
    erw [Cat.Hom.inv_hom_id_toNatTrans_app]
    first | rw [Functor.map_id] | erw [Functor.map_id]
    erw [Category.id_comp]
    rfl
  erw [key2]
  rfl

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
-- the `skip` alternatives in the erosion loops are structural: `iterate` aborts at the
-- first wholly-failing round without them, and are unreachable on the successful path
set_option maxHeartbeats 800000 in
-- the coherence fields close by `exact`-plugs of core lemmas whose defeq checks
-- bridge composite/nested point spellings at default transparency
/--
The *evaluation pseudofunctor* `Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat) ⥤ᵖ Cat.{w, v}`.

This is the right-hand side of the Yoneda equivalence (before universe promotion):

* **On objects**: `(b, F) ↦ F.obj b` — evaluate the pseudofunctor `F` at the object `b`.
* **On 1-morphisms**: `(f : b' ⟶ b, α : F ⟶ G) ↦ α.app b' ≫ G.map f`, i.e., apply the
  component of the natural transformation `α` at `b'`, then map along `f` using `G`.
* **On 2-morphisms**: `(σ, τ) ↦ (σ.as.app b' ▷ G.map f) ≫ (_ ◁ G.map₂ τ)`.
* **Coherence iso `mapId`**: `F.mapId b`, the identity coherence of `F`.
* **Coherence iso `mapComp`**: built from the associator and `G.mapComp` and `G.naturality`.

Note: this pseudofunctor lands in the smaller universe `Cat.{w, v}`.  Use `yonedaEvaluation`
(which post-composes with `catPseudoULift`) for the universe-matched version.
-/
def yonedaEvaluation' : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v}) ⥤ᵖ Cat.{w, v} where
  obj x := x.snd.obj x.fst
  map {x y} f := f.2.app x.1 ≫ (y.2.map f.1)
  map₂ {x y f g} η := (η.2.as.app x.1 ▷ y.2.map f.1) ≫ (_ ◁ y.2.map₂ η.1)
  mapId x := x.2.mapId x.1
  mapComp {a b c} f g := by
    refine (f.2.app a.1 ≫ g.2.app a.1) ◁ᵢ (c.2.mapComp f.1 g.1) ≪≫ ?_
    refine (α_ (f.2.app a.1) (g.2.app a.1) (c.2.map f.1 ≫ c.2.map g.1)) ≪≫ ?_
    refine (f.2.app a.1) ◁ᵢ ?_ ≪≫
      (α_ (f.2.app a.1) (b.2.map f.1) (g.2.app b.1 ≫ c.2.map g.1)).symm
    refine (α_ (g.2.app a.1) (c.2.map f.1) (c.2.map g.1)).symm ≪≫
      ((g.2.naturality f.1).symm ▷ᵢ (c.2.map g.1)) ≪≫
      (α_ (b.2.map f.1) (g.2.app b.1) (c.2.map g.1))
  map₂_whisker_left {a b c} f {g h} {η} := by
    apply Cat.Hom₂.ext_app
    intro Z
    simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, whiskerLeftIso_hom,
      whiskerLeftIso_inv, whiskerRightIso_hom, whiskerRightIso_inv, Cat.Hom.toNatTrans_comp,
      NatTrans.comp_app, Cat.whiskerLeft_toNatTrans, Cat.whiskerRight_toNatTrans,
      whiskerLeft_app, whiskerRight_app,
      Cat.associator_hom_toNatTrans_app, Cat.associator_inv_toNatTrans_app,
      Cat.Hom.comp_toFunctor, Functor.comp_obj, Category.id_comp, Category.comp_id]
    simp only [prod_whiskerLeft_fst, prod_whiskerLeft_snd, whiskerLeft_as_app]
    erw [Cat.whiskerLeft_app]
    have hw := Cat.Hom₂.congr_app (c.2.map₂_whisker_left f.1 η.1)
      (((f ≫ h).2.app a.1).toFunctor.obj Z)
    dsimp at hw
    erw [hw]
    have h1 : (c.2.map (f ≫ g).1).toFunctor.map
          ((η.2.as.app a.1).toNatTrans.app ((f.2.app a.1).toFunctor.obj Z)) ≫
        (c.2.mapComp f.1 g.1).hom.toNatTrans.app
          ((h.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z)) =
        (c.2.mapComp f.1 g.1).hom.toNatTrans.app
          ((g.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z)) ≫
        (c.2.map g.1).toFunctor.map ((c.2.map f.1).toFunctor.map
          ((η.2.as.app a.1).toNatTrans.app ((f.2.app a.1).toFunctor.obj Z))) :=
      (c.2.mapComp f.1 g.1).hom.toNatTrans.naturality
        ((η.2.as.app a.1).toNatTrans.app ((f.2.app a.1).toFunctor.obj Z))
    erw [reassoc_of% h1]
    simpa only [Cat.Hom.comp_toFunctor, Functor.comp_obj, Functor.comp_map, Category.assoc]
      using evaluation_whisker_left_core f η Z
  map₂_whisker_right {a b c f g h} η := by
    apply Cat.Hom₂.ext_app
    intro Z
    simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, whiskerLeftIso_hom,
      whiskerLeftIso_inv, whiskerRightIso_hom, whiskerRightIso_inv, Cat.Hom.toNatTrans_comp,
      NatTrans.comp_app, Cat.whiskerLeft_toNatTrans, Cat.whiskerRight_toNatTrans,
      whiskerLeft_app, whiskerRight_app,
      Cat.associator_hom_toNatTrans_app, Cat.associator_inv_toNatTrans_app,
      Cat.Hom.comp_toFunctor, Functor.comp_obj, Category.id_comp, Category.comp_id]
    simp only [prod_whiskerRight_fst, prod_whiskerRight_snd, whiskerRight_as_app]
    have hw := Cat.Hom₂.congr_app (c.2.map₂_whisker_right h.1 η.1)
      (((g ≫ η).2.app a.1).toFunctor.obj Z)
    dsimp at hw
    erw [hw]
    have hnn := Cat.Hom₂.congr_app (η.2.naturality_naturality h.1)
      ((g.2.app a.1).toFunctor.obj Z)
    dsimp at hnn
    have h1 : (c.2.map (f ≫ η).1).toFunctor.map
          ((h.2.as.app a.1 ▷ η.2.app a.1).toNatTrans.app Z) ≫
        (c.2.mapComp f.1 η.1).hom.toNatTrans.app
          ((η.2.app a.1).toFunctor.obj ((g.2.app a.1).toFunctor.obj Z)) =
        (c.2.mapComp f.1 η.1).hom.toNatTrans.app
          ((η.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z)) ≫
        (c.2.map η.1).toFunctor.map ((c.2.map f.1).toFunctor.map
          ((h.2.as.app a.1 ▷ η.2.app a.1).toNatTrans.app Z)) :=
      (c.2.mapComp f.1 η.1).hom.toNatTrans.naturality
        ((h.2.as.app a.1 ▷ η.2.app a.1).toNatTrans.app Z)
    erw [reassoc_of% h1]
    simpa only [Cat.Hom.comp_toFunctor, Functor.comp_obj, Functor.comp_map, Category.assoc]
      using evaluation_whisker_right_core h η Z
  map₂_associator {a b c d} f g h := by
    apply Cat.Hom₂.ext_app
    intro Z
    simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, whiskerLeftIso_hom,
      whiskerLeftIso_inv, whiskerRightIso_hom, whiskerRightIso_inv, Cat.Hom.toNatTrans_comp,
      NatTrans.comp_app, Cat.whiskerLeft_toNatTrans, Cat.whiskerRight_toNatTrans,
      whiskerLeft_app, whiskerRight_app,
      Cat.associator_hom_toNatTrans_app, Cat.associator_inv_toNatTrans_app,
      Cat.Hom.comp_toFunctor, Functor.comp_obj, Category.id_comp, Category.comp_id,
      Bicategory.prod_comp_fst, Bicategory.prod_comp_snd, Bicategory.prod_associator_hom_fst,
      Pseudofunctor.StrongTrans.comp_app]
    simpa only [Cat.Hom.comp_toFunctor, Functor.comp_obj, Functor.comp_map, Functor.map_id,
      Functor.map_comp, Category.id_comp, Category.comp_id, Category.assoc,
      Pseudofunctor.StrongTrans.comp_app]
      using evaluation_associator_core f g h Z
  map₂_left_unitor {a b} f := by
    apply Cat.Hom₂.ext_app
    intro Z
    simp only [Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom, whiskerRightIso_hom,
      Cat.Hom.toNatTrans_comp, NatTrans.comp_app, Cat.whiskerLeft_toNatTrans,
      Cat.whiskerRight_toNatTrans, whiskerLeft_app, whiskerRight_app,
      Cat.associator_hom_toNatTrans_app, Cat.associator_inv_toNatTrans_app,
      Cat.leftUnitor_hom_toNatTrans_app,
      Cat.Hom.comp_toFunctor, Functor.comp_obj, Category.id_comp, Category.comp_id,
      Bicategory.prod_comp_fst, Bicategory.prod_comp_snd, Bicategory.prod_leftUnitor_hom_fst,
      Bicategory.prod_id_fst, Bicategory.prod_id_snd,
      Pseudofunctor.StrongTrans.categoryStruct_id_app, Cat.Hom.id_toFunctor, Functor.id_obj,
      Pseudofunctor.StrongTrans.comp_app]
    simpa only [Cat.Hom.comp_toFunctor, Functor.comp_obj, Functor.comp_map, Functor.map_id,
      Functor.map_comp, Category.id_comp, Category.comp_id, Category.assoc,
      Bicategory.prod_id_fst, Bicategory.prod_id_snd,
      Pseudofunctor.StrongTrans.categoryStruct_id_app, Cat.Hom.id_toFunctor, Functor.id_obj,
      Pseudofunctor.StrongTrans.comp_app]
      using evaluation_left_unitor_core f Z
  map₂_right_unitor {a b} f := by
    apply Cat.Hom₂.ext_app
    intro Z
    simp only [Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom, whiskerRightIso_hom,
      Cat.Hom.toNatTrans_comp, NatTrans.comp_app, Cat.whiskerLeft_toNatTrans,
      Cat.whiskerRight_toNatTrans, whiskerLeft_app, whiskerRight_app,
      Cat.associator_hom_toNatTrans_app, Cat.associator_inv_toNatTrans_app,
      Cat.rightUnitor_hom_toNatTrans_app,
      Cat.Hom.comp_toFunctor, Functor.comp_obj, Category.id_comp, Category.comp_id,
      Bicategory.prod_comp_fst, Bicategory.prod_comp_snd, Bicategory.prod_rightUnitor_hom_fst,
      Bicategory.prod_id_fst, Bicategory.prod_id_snd,
      Pseudofunctor.StrongTrans.categoryStruct_id_app, Cat.Hom.id_toFunctor, Functor.id_obj,
      Pseudofunctor.StrongTrans.comp_app]
    simpa only [Cat.Hom.comp_toFunctor, Functor.comp_obj, Functor.comp_map, Functor.map_id,
      Functor.map_comp, Category.id_comp, Category.comp_id, Category.assoc,
      Bicategory.prod_id_fst, Bicategory.prod_id_snd,
      Pseudofunctor.StrongTrans.categoryStruct_id_app, Cat.Hom.id_toFunctor, Functor.id_obj,
      Pseudofunctor.StrongTrans.comp_app]
      using evaluation_right_unitor_core f Z

/--
The *evaluation pseudofunctor* at the correct universe level,
`Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat) ⥤ᵖ Cat.{max u (max v w), max u (max v w)}`.

Defined as the composite `yonedaEvaluation' ⋙ catPseudoULift`, which promotes the smaller
pseudofunctor `yonedaEvaluation'` (landing in `Cat.{w, v}`) to match the universe of
`yonedaPairing`.
-/
def yonedaEvaluation : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v}) ⥤ᵖ Cat.{max u (max v w), max u (max v w)} :=
  Pseudofunctor.comp yonedaEvaluation' catPseudoULift

/--
At a fixed pair `x = (b, F)`, the *evaluate-at-identity functor*
`StrongTrans (yoneda₀ b) F ⥤ F.obj b`.

This is the core of the Yoneda equivalence at the level of individual categories:
* **On objects**: a strong transformation `η : yoneda₀ b ⟶ F` maps to
  `η.app b (𝟙 b) : F.obj b` — apply the component at `b`, then evaluate at `𝟙 b`.
* **On morphisms**: a modification `m : η ⟶ θ` maps to
  `m.as.app b (𝟙 b) : η.app b (𝟙 b) ⟶ θ.app b (𝟙 b)`.
-/
@[simp]
def yonedaLemmaForwardsFunctor (x : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat)) :
    yonedaPairing.obj x ⥤ yonedaEvaluation.obj x where
  obj pair := { down := (pair.app x.1).toFunctor.obj (𝟙 (unop x.1)) }
  map {a b} f := { down := (f.as.app x.1).toNatTrans.app (𝟙 (unop x.1)) }

/-- The component form of the naturality square for `yonedaLemmaForwards`. -/
lemma forwards_naturality_component {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b)
    {X Y : yoneda₀ (unop a.1) ⟶ a.2} (h : X ⟶ Y) :
    (f.2.app b.1).toFunctor.map ((h.as.app b.1).toNatTrans.app (𝟙 (unop b.1) ≫ f.1.unop)) ≫
      (f.2.app b.1).toFunctor.map ((Y.app b.1).toFunctor.map (λ_ f.1.unop).hom) ≫
        (f.2.app b.1).toFunctor.map ((Y.app b.1).toFunctor.map (ρ_ f.1.unop).inv) ≫
          (f.2.app b.1).toFunctor.map ((Y.naturality f.1).hom.toNatTrans.app (𝟙 (unop a.1))) ≫
            (f.2.naturality f.1).hom.toNatTrans.app ((Y.app a.1).toFunctor.obj (𝟙 (unop a.1))) =
    ((f.2.app b.1).toFunctor.map ((X.app b.1).toFunctor.map (λ_ f.1.unop).hom) ≫
        (f.2.app b.1).toFunctor.map ((X.app b.1).toFunctor.map (ρ_ f.1.unop).inv) ≫
          (f.2.app b.1).toFunctor.map ((X.naturality f.1).hom.toNatTrans.app (𝟙 (unop a.1))) ≫
            (f.2.naturality f.1).hom.toNatTrans.app
              ((X.app a.1).toFunctor.obj (𝟙 (unop a.1)))) ≫
      (b.2.map f.1).toFunctor.map ((f.2.app a.1).toFunctor.map
        ((h.as.app a.1).toNatTrans.app (𝟙 (unop a.1)))) := by
  have h1 := (h.as.app b.1).toNatTrans.naturality ((λ_ f.1.unop).hom ≫ (ρ_ f.1.unop).inv)
  have h2 := modification_naturality_app h f.1 (𝟙 (unop a.1))
  have h3 := (f.2.naturality f.1).hom.toNatTrans.naturality
    ((h.as.app a.1).toNatTrans.app (𝟙 (unop a.1)))
  dsimp at h1 h2 h3
  have h1' := congrArg (fun m ↦ (f.2.app b.1).toFunctor.map m) h1
  have h2' := congrArg (fun m ↦ (f.2.app b.1).toFunctor.map m) h2
  simp only [Functor.map_comp] at h1' h2'
  rw [← reassoc_of% h1']
  erw [reassoc_of% h2', h3]
  simp only [Category.assoc]
  rfl

/-- Reduction: the identity coherence of the lifted evaluation pseudofunctor, evaluated at a
lifted point, is the unlifted `yonedaEvaluation'.mapId` component.  `catPseudoULift` is strict,
so the lift is transparent up to a trivial `≫ 𝟙`. -/
lemma yonedaEvaluation_mapId_app_down {a : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})}
    (x : ↑(yonedaEvaluation'.obj a)) :
    (yonedaEvaluation.mapId a).hom.toNatTrans.app { down := x }
      = { down := (yonedaEvaluation'.mapId a).hom.toNatTrans.app x } := by
  dsimp [yonedaEvaluation, Pseudofunctor.comp, catPseudoULift, catLift, ULiftHom.up]
  erw [Category.comp_id]; rfl

/-- Reduction: the 2-morphism image of the lifted evaluation pseudofunctor at a lifted point is
the unlifted `yonedaEvaluation'.map₂` component. -/
lemma yonedaEvaluation_map₂_app_down {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} {f g : a ⟶ b}
    (η : f ⟶ g) (x : ↑(yonedaEvaluation'.obj a)) :
    (yonedaEvaluation.map₂ η).toNatTrans.app { down := x }
      = { down := (yonedaEvaluation'.map₂ η).toNatTrans.app x } := by
  dsimp [yonedaEvaluation, Pseudofunctor.comp, catPseudoULift, catLift, ULiftHom.up]
  rfl

/-- Reduction: the composition coherence of the lifted evaluation pseudofunctor, evaluated at a
lifted point, is the unlifted `yonedaEvaluation'.mapComp` component. -/
lemma yonedaEvaluation_mapComp_app_down {a b c : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b)
    (g : b ⟶ c) (x : ↑(yonedaEvaluation'.obj a)) :
    (yonedaEvaluation.mapComp f g).hom.toNatTrans.app { down := x }
      = { down := (yonedaEvaluation'.mapComp f g).hom.toNatTrans.app x } := by
  dsimp [yonedaEvaluation, Pseudofunctor.comp, catPseudoULift, catLift, ULiftHom.up]
  erw [Category.comp_id]; rfl

/--
The `Z`-side identity underlying `naturality_naturality` for `yonedaLemmaForwards`.

Transporting the evaluation point `𝟙` along `η.1` and then through `Z.naturality g.1` agrees
with going through `Z.naturality f.1` and then applying `a.2.map₂ η.1`.  It is exactly the
2-naturality of `Z.naturality` in the 2-cell `η.1` (`Z.naturality_naturality`), combined with
right-unitor naturality to reconcile the two unitor spellings.
-/
lemma forwards_naturality_naturality_Z {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} {f g : a ⟶ b}
    (η : f ⟶ g) (Z : ↑(yonedaPairing.obj a)) :
    (Z.app b.1).toFunctor.map ((λ_ f.1.unop).hom ≫ η.1.unop2 ≫ (λ_ g.1.unop).inv) ≫
      (Z.app b.1).toFunctor.map ((λ_ g.1.unop).hom ≫ (ρ_ g.1.unop).inv) ≫
        (Z.naturality g.1).hom.toNatTrans.app (𝟙 (unop a.1)) =
    ((Z.app b.1).toFunctor.map ((λ_ f.1.unop).hom ≫ (ρ_ f.1.unop).inv) ≫
        (Z.naturality f.1).hom.toNatTrans.app (𝟙 (unop a.1))) ≫
      (a.2.map₂ η.1).toNatTrans.app ((Z.app a.1).toFunctor.obj (𝟙 (unop a.1))) := by
  rw [Category.assoc]
  have h3 := Cat.Hom₂.congr_app (Z.naturality_naturality η.1) (𝟙 (unop a.1))
  simp only [Cat.Hom.toNatTrans_comp, NatTrans.comp_app, Cat.whiskerLeft_toNatTrans,
    Cat.whiskerRight_toNatTrans, whiskerLeft_app, whiskerRight_app] at h3
  dsimp [yoneda₀, precomposing, precomposingCat] at h3
  erw [← h3]
  conv_lhs => rw [← Category.assoc, ← Functor.map_comp]
  conv_rhs => rw [← Category.assoc, ← Functor.map_comp]
  congr 2
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_assoc, Bicategory.rightUnitor_inv_naturality]
  rfl

/--
The component core of the `naturality_naturality` obligation of `yonedaLemmaForwards`, stated
in the unlifted fibre (the `.down` of the lifted 2-cells).

It says the forward naturality isomorphism is natural in the 2-cell `η = (η.1, η.2)`.  The
proof splits `η` into its two components: the modification part `η.2` contributes
`modification_naturality_app`, the base 2-cell `η.1` contributes `g.2.naturality_naturality`,
and the evaluation point is handled by `forwards_naturality_naturality_Z`.
-/
lemma forwards_naturality_naturality_core {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} {f g : a ⟶ b}
    (η : f ⟶ g) (Z : ↑(yonedaPairing.obj a)) :
    (((yonedaPairing.map₂ η).toNatTrans.app Z).as.app b.1).toNatTrans.app (𝟙 (unop b.1)) ≫
        ((g.2.app b.1).toFunctor.map
            ((Z.app b.1).toFunctor.map ((λ_ g.1.unop).hom ≫ (ρ_ g.1.unop).inv) ≫
              ((Cat.Hom.toNatIso (Z.naturality g.1)).app (𝟙 (unop a.1))).hom) ≫
          ((Cat.Hom.toNatIso (g.2.naturality g.1)).app
              ((Z.app a.1).toFunctor.obj (𝟙 (unop a.1)))).hom) =
    ((f.2.app b.1).toFunctor.map
            ((Z.app b.1).toFunctor.map ((λ_ f.1.unop).hom ≫ (ρ_ f.1.unop).inv) ≫
              ((Cat.Hom.toNatIso (Z.naturality f.1)).app (𝟙 (unop a.1))).hom) ≫
          ((Cat.Hom.toNatIso (f.2.naturality f.1)).app
              ((Z.app a.1).toFunctor.obj (𝟙 (unop a.1)))).hom) ≫
      (yonedaEvaluation'.map₂ η).toNatTrans.app ((Z.app a.1).toFunctor.obj (𝟙 (unop a.1))) := by
  dsimp only [yonedaPairing, Cat.toCatHom₂_toNatTrans, yonedaPairingMap₂, yonedaEvaluation',
    postcomposing₂, postcomposingCat]
  simp only [NatTrans.comp_app, precomposing_map_app, postcomposing_map_app,
    precomposing_obj, postcomposing_obj, precomp_map,
    Cat.toCatHom₂_toNatTrans, whiskerLeft_as_app, whiskerRight_as_app,
    homCategory_comp_as_app,
    Cat.Hom.toNatTrans_comp, Cat.whiskerLeft_toNatTrans, Cat.whiskerRight_toNatTrans,
    whiskerLeft_app, whiskerRight_app, Iso.app_hom, Cat.Hom.toNatIso]
  simp only [Pseudofunctor.StrongTrans.comp_app, Functor.comp_map,
    postcomp₂, postcomposingCat, postcomp_obj, Cat.Hom.comp_toFunctor,
    Bicategory.id_whiskerLeft]
  have h1 := modification_naturality_app η.2 f.1 ((Z.app a.1).toFunctor.obj (𝟙 (unop a.1)))
  have h2 := Cat.Hom₂.congr_app (g.2.naturality_naturality η.1)
    ((Z.app a.1).toFunctor.obj (𝟙 (unop a.1)))
  dsimp at h1 h2
  simp only [Category.assoc]
  erw [← reassoc_of% h1, ← h2]
  erw [(η.2.as.app b.1).toNatTrans.naturality,
    (η.2.as.app b.1).toNatTrans.naturality_assoc]
  erw [Category.assoc]
  refine congrArg (fun m ↦ (η.2.as.app b.1).toNatTrans.app _ ≫ m) ?_
  erw [← Functor.map_comp_assoc]
  erw [forwards_naturality_naturality_Z η Z]
  erw [Functor.map_comp_assoc]
  rfl

/--
The component core of the `naturality_id` obligation of `yonedaLemmaForwards`, stated in the
unlifted fibre.

This is the genuine unit coherence: it relates `yonedaPairing.mapId` to `a.2.mapId`.  The proof
is driven by `Z.naturality_id` — the unit coherence of the strong transformation `Z` itself —
after which both sides are pure unitor data and the remaining content is
`Bicategory.unitors_equal` (`(λ_ (𝟙 x)).hom = (ρ_ (𝟙 x)).hom`).
-/
lemma forwards_naturality_id_core (a : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v}))
    (Z : ↑(yonedaPairing.obj a)) :
    ((Z.app a.1).toFunctor.map ((λ_ (𝟙 a.1).unop).hom ≫ (ρ_ (𝟙 a.1).unop).inv) ≫
        (Z.naturality (𝟙 a.1)).hom.toNatTrans.app (𝟙 (unop a.1))) ≫
      (yonedaEvaluation'.mapId a).hom.toNatTrans.app ((Z.app a.1).toFunctor.obj (𝟙 (unop a.1))) =
    (((yonedaPairing.mapId a).hom.toNatTrans.app Z).as.app a.1).toNatTrans.app (𝟙 (unop a.1)) := by
  dsimp only [yonedaPairing, yonedaEvaluation']
  simp only [Cat.Hom.isoMk_hom, Cat.toCatHom₂_toNatTrans, NatIso.ofComponents_hom_app,
    Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom, homCategory_comp_as_app,
    whiskerRight_as_app, Cat.Hom.toNatTrans_comp, NatTrans.comp_app,
    Cat.whiskerRight_toNatTrans, whiskerRight_app]
  have hZ := Cat.Hom₂.congr_app (Z.naturality_id a.1) (𝟙 (unop a.1))
  simp only [Cat.Hom.toNatTrans_comp, NatTrans.comp_app, Cat.whiskerLeft_toNatTrans,
    Cat.whiskerRight_toNatTrans, whiskerLeft_app, whiskerRight_app] at hZ
  simp only [Category.assoc]
  erw [hZ]
  simp only [Pseudofunctor.StrongTrans.comp_app,
    Pseudofunctor.StrongTrans.categoryStruct_id_app,
    Cat.Hom.comp_toFunctor, Cat.Hom.id_toFunctor, Functor.comp_map, Functor.id_map,
    Cat.leftUnitor_hom_app, Cat.rightUnitor_inv_app, eqToHom_trans]
  dsimp [postcompId₂, bicategoricalIso]
  simp only [Bicategory.unitors_equal]
  dsimp [Functor.leftUnitor, Functor.rightUnitor]
  erw [NatTrans.comp_app, NatTrans.comp_app, NatTrans.id_app, Category.id_comp]
  simp

/-- Reduction: the lifted evaluation pseudofunctor's action on a lifted morphism. -/
lemma yonedaEvaluation_map_map_down {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b)
    {x y : ↑(yonedaEvaluation'.obj a)} (m : x ⟶ y) :
    (yonedaEvaluation.map f).toFunctor.map { down := m }
      = { down := (yonedaEvaluation'.map f).toFunctor.map m } := by
  dsimp [yonedaEvaluation, Pseudofunctor.comp, catPseudoULift, catLift, ULiftHom.up]
  rfl

/-- Component form of the naturality constraint of a composite strong transformation. -/
lemma strongTrans_comp_naturality_hom_app {F G H : Bᵒᵖ ⥤ᵖ Cat.{w, v}} (η : F ⟶ G) (θ : G ⟶ H)
    {X Y : Bᵒᵖ} (k : X ⟶ Y) (x : ↑(F.obj X)) :
    ((η ≫ θ).naturality k).hom.toNatTrans.app x =
      (θ.app Y).toFunctor.map ((η.naturality k).hom.toNatTrans.app x) ≫
        (θ.naturality k).hom.toNatTrans.app ((η.app X).toFunctor.obj x) := by
  simp only [Pseudofunctor.StrongTrans.categoryStruct_comp_naturality_hom]
  iterate (first | erw [eqToHom_refl] | erw [Category.id_comp] | erw [Category.comp_id])
  rfl

/-- The head unit-coherence in `B`'s hom-categories underlying `naturality_comp`: `u_{f≫g}`
composed with the yoneda `mapComp` equals the postcomp₂ reorganisation with `u_g`, `u_f`.  Both
sides are pure associator/unitor data — `bicategory` after unfolding to `α_`/`λ_`/`ρ_`. -/
lemma forwards_naturality_comp_head {a b c : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b) (g : b ⟶ c) :
    ((λ_ (f.1 ≫ g.1).unop).hom ≫ (ρ_ (f.1 ≫ g.1).unop).inv) ≫
        ((yoneda₀ (unop a.1)).mapComp f.1 g.1).hom.toNatTrans.app (𝟙 (unop a.1)) =
    (((postcompComp₂ g.1.unop f.1.unop).hom.as.app c.1).toNatTrans.app (𝟙 (unop c.1)) ≫
        ((postcomp₂ f.1.unop).app c.1).toFunctor.map ((λ_ g.1.unop).hom ≫ (ρ_ g.1.unop).inv) ≫
        ((postcomp₂ f.1.unop).naturality g.1).hom.toNatTrans.app (𝟙 (unop b.1))) ≫
      ((yoneda₀ (unop a.1)).map g.1).toFunctor.map ((λ_ f.1.unop).hom ≫ (ρ_ f.1.unop).inv) := by
  erw [show ((yoneda₀ (unop a.1)).map g.1).toFunctor.map ((λ_ f.1.unop).hom ≫ (ρ_ f.1.unop).inv)
        = g.1.unop ◁ ((λ_ f.1.unop).hom ≫ (ρ_ f.1.unop).inv) from rfl,
     show ((postcomp₂ f.1.unop).app c.1).toFunctor.map ((λ_ g.1.unop).hom ≫ (ρ_ g.1.unop).inv)
        = ((λ_ g.1.unop).hom ≫ (ρ_ g.1.unop).inv) ▷ f.1.unop from rfl]
  dsimp only [postcompComp₂, yoneda, postcomp₂, yoneda₀,
    associatorNatIsoRightCat, associatorNatIsoMiddleCat, associatorNatIsoLeftCat]
  simp only [Cat.Hom.isoMk_hom, Cat.Hom.isoMk_inv, Cat.toCatHom₂_toNatTrans, Iso.symm_hom,
    NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app, isoMk_inv_as_app]
  bicategory

set_option maxHeartbeats 500000 in
-- the long descent + `naturality_comp_hom_app` telescoping + three `u_f`-transport squares
-- exceed the default budget (measured floor ≈ 350k, so ~1.4× margin); does not fit in 200k
/-- Core of `naturality_comp` for `yonedaLemmaForwards` (unlifted fibre form). -/
lemma forwards_naturality_comp_core {a b c : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b) (g : b ⟶ c)
    (Z : ↑(yonedaPairing.obj a)) :
    (((f.2 ≫ g.2).app c.1).toFunctor.map
          ((Z.app c.1).toFunctor.map
              ((λ_ (f.1 ≫ g.1).unop).hom ≫ (ρ_ (f.1 ≫ g.1).unop).inv) ≫
            (Z.naturality (f.1 ≫ g.1)).hom.toNatTrans.app (𝟙 (unop a.1))) ≫
        ((f.2 ≫ g.2).naturality (f.1 ≫ g.1)).hom.toNatTrans.app
          ((Z.app a.1).toFunctor.obj (𝟙 (unop a.1)))) ≫
      (yonedaEvaluation'.mapComp f g).hom.toNatTrans.app
        ((Z.app a.1).toFunctor.obj (𝟙 (unop a.1))) =
    (((yonedaPairing.mapComp f g).hom.toNatTrans.app Z).as.app c.1).toNatTrans.app
        (𝟙 (unop c.1)) ≫
      ((g.2.app c.1).toFunctor.map
            ((((yonedaPairing.map f).toFunctor.obj Z).app c.1).toFunctor.map
                ((λ_ g.1.unop).hom ≫ (ρ_ g.1.unop).inv) ≫
              (((yonedaPairing.map f).toFunctor.obj Z).naturality g.1).hom.toNatTrans.app
                (𝟙 (unop b.1))) ≫
          (g.2.naturality g.1).hom.toNatTrans.app
            ((((yonedaPairing.map f).toFunctor.obj Z).app b.1).toFunctor.obj (𝟙 (unop b.1)))) ≫
        (yonedaEvaluation'.map g).toFunctor.map
          ((f.2.app b.1).toFunctor.map
              ((Z.app b.1).toFunctor.map ((λ_ f.1.unop).hom ≫ (ρ_ f.1.unop).inv) ≫
                (Z.naturality f.1).hom.toNatTrans.app (𝟙 (unop a.1))) ≫
            (f.2.naturality f.1).hom.toNatTrans.app
              ((Z.app a.1).toFunctor.obj (𝟙 (unop a.1)))) := by
  rw [strongTrans_comp_naturality_hom_app]
  simp only [Pseudofunctor.StrongTrans.comp_app, Cat.Hom.comp_toFunctor,
    Functor.comp_map, Functor.comp_obj]
  dsimp only [yonedaPairing, yonedaEvaluation']
  simp only [Cat.Hom.isoMk_hom, Cat.toCatHom₂_toNatTrans, NatIso.ofComponents_hom_app,
    Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom, whiskerLeftIso_hom,
    homCategory_comp_as_app, whiskerRight_as_app,
    associator_hom_as_app, associator_inv_as_app,
    Cat.Hom.toNatTrans_comp, NatTrans.comp_app,
    Cat.whiskerLeft_toNatTrans, Cat.whiskerRight_toNatTrans, whiskerLeft_app, whiskerRight_app,
    Cat.associator_hom_app, Cat.associator_inv_app]
  dsimp only [Functor.toCatHom]
  rw [strongTrans_comp_naturality_hom_app, strongTrans_comp_naturality_hom_app]
  simp only [Pseudofunctor.StrongTrans.comp_app, Cat.Hom.comp_toFunctor,
    Functor.comp_map, Functor.comp_obj, eqToHom_refl, Category.id_comp, Category.comp_id,
    Category.assoc]
  simp only [Pseudofunctor.StrongTrans.naturality_comp_hom_app]
  simp only [Category.assoc, ← Functor.map_comp_assoc]
  iterate 6
    (first
      | erw [Cat.Hom.inv_hom_id_toNatTrans_app_assoc]
      | erw [Cat.Hom.inv_hom_id_toNatTrans_app]
      | erw [Category.assoc])
  simp only [← Functor.map_comp]
  simp only [Cat.Hom.comp_toFunctor, Functor.comp_obj]
  iterate erw [Category.comp_id]
  iterate (first
      | erw [Cat.Hom.hom_inv_id_toNatTrans_app]
      | erw [Cat.Hom.inv_hom_id_toNatTrans_app])
  erw [Functor.map_id, Category.comp_id]
  simp only [Functor.map_comp, Category.assoc]
  erw [(g.2.naturality g.1).hom.toNatTrans.naturality]
  have hpush2 := congrArg (g.2.app c.1).toFunctor.map
    ((f.2.naturality g.1).hom.toNatTrans.naturality
      ((Z.naturality f.1).hom.toNatTrans.app (𝟙 (unop a.1))))
  simp only [Cat.Hom.comp_toFunctor, Functor.comp_map, Functor.comp_obj,
    Functor.map_comp] at hpush2
  erw [reassoc_of% hpush2]
  erw [(g.2.naturality g.1).hom.toNatTrans.naturality_assoc]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp]
  have hHead_t : (Z.app c.1).toFunctor.map ((λ_ (f.1 ≫ g.1).unop).hom ≫ (ρ_ (f.1 ≫ g.1).unop).inv) ≫
        (Z.app c.1).toFunctor.map
            (((yoneda₀ (unop a.1)).mapComp f.1 g.1).hom.toNatTrans.app (𝟙 (unop a.1))) ≫
          (Z.naturality g.1).hom.toNatTrans.app
            (((yoneda₀ (unop a.1)).map f.1).toFunctor.obj (𝟙 (unop a.1)))
      = (Z.app c.1).toFunctor.map (
          ((postcompComp₂ g.1.unop f.1.unop).hom.as.app c.1).toNatTrans.app (𝟙 (unop c.1)) ≫
          ((postcomp₂ f.1.unop).app c.1).toFunctor.map
              ((λ_ g.1.unop).hom ≫ (ρ_ g.1.unop).inv) ≫
          ((postcomp₂ f.1.unop).naturality g.1).hom.toNatTrans.app (𝟙 (unop b.1))) ≫
        (Z.app c.1).toFunctor.map
            (((yoneda₀ (unop a.1)).map g.1).toFunctor.map
              ((λ_ f.1.unop).hom ≫ (ρ_ f.1.unop).inv)) ≫
          (Z.naturality g.1).hom.toNatTrans.app
            (((yoneda₀ (unop a.1)).map f.1).toFunctor.obj (𝟙 (unop a.1))) := by
    erw [← Functor.map_comp_assoc]; erw [forwards_naturality_comp_head]
    erw [Functor.map_comp_assoc]; rfl
  erw [hHead_t]
  -- LHS now has `Zc.map(ymgu) ≫ (Z.naturality g.1)` adjacent; transport it through Z.nat g.1.
  erw [(Z.naturality g.1).hom.toNatTrans.naturality
    ((λ_ f.1.unop).hom ≫ (ρ_ f.1.unop).inv)]
  -- step 2: transport the factor through `f.2.naturality g.1` (inside `G.map`).
  have hT2 : ∀ {M : ↑(a.2.obj c.1)}
      (A : (Z.app c.1).toFunctor.obj
          (((postcomp₂ (g.1.unop ≫ f.1.unop)).app c.1).toFunctor.obj (𝟙 (unop c.1))) ⟶ M)
      (Bb : M ⟶ (Z.app b.1 ≫ a.2.map g.1).toFunctor.obj (𝟙 (unop b.1) ≫ f.1.unop)),
      (f.2.app c.1).toFunctor.map
          (A ≫ Bb ≫ (Z.app b.1 ≫ a.2.map g.1).toFunctor.map
            ((λ_ f.1.unop).hom ≫ (ρ_ f.1.unop).inv)) ≫
        (f.2.naturality g.1).hom.toNatTrans.app
          ((Z.app b.1).toFunctor.obj
            (((yoneda₀ (unop a.1)).map f.1).toFunctor.obj (𝟙 (unop a.1))))
      = (f.2.app c.1).toFunctor.map (A ≫ Bb) ≫
          (f.2.naturality g.1).hom.toNatTrans.app
            ((Z.app b.1).toFunctor.obj (𝟙 (unop b.1) ≫ f.1.unop)) ≫
            (b.2.map g.1).toFunctor.map
              ((f.2.app b.1).toFunctor.map
                ((Z.app b.1).toFunctor.map ((λ_ f.1.unop).hom ≫ (ρ_ f.1.unop).inv))) := by
    intro M A Bb
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc]
    erw [(f.2.naturality g.1).hom.toNatTrans.naturality
      ((Z.app b.1).toFunctor.map ((λ_ f.1.unop).hom ≫ (ρ_ f.1.unop).inv))]
    erw [← Functor.map_comp_assoc]; rfl
  erw [hT2]
  -- step 3: transport through `g.2.naturality g.1` (top level; has a trailing tail → reassoc).
  have hT3 : ∀ {M : ↑(b.2.obj c.1)}
      (A' : (f.2.app c.1).toFunctor.obj ((Z.app c.1).toFunctor.obj
          (((postcomp₂ (g.1.unop ≫ f.1.unop)).app c.1).toFunctor.obj (𝟙 (unop c.1)))) ⟶ M)
      (Bb' : M ⟶ (b.2.map g.1).toFunctor.obj ((f.2.app b.1).toFunctor.obj
          ((Z.app b.1).toFunctor.obj (𝟙 (unop b.1) ≫ f.1.unop)))),
      (g.2.app c.1).toFunctor.map
          (A' ≫ Bb' ≫ (b.2.map g.1).toFunctor.map
            ((f.2.app b.1).toFunctor.map
              ((Z.app b.1).toFunctor.map ((λ_ f.1.unop).hom ≫ (ρ_ f.1.unop).inv)))) ≫
        (g.2.naturality g.1).hom.toNatTrans.app
          ((f.2.app b.1).toFunctor.obj ((Z.app b.1).toFunctor.obj
            (((yoneda₀ (unop a.1)).map f.1).toFunctor.obj (𝟙 (unop a.1)))))
      = (g.2.app c.1).toFunctor.map (A' ≫ Bb') ≫
          (g.2.naturality g.1).hom.toNatTrans.app
            ((f.2.app b.1).toFunctor.obj ((Z.app b.1).toFunctor.obj (𝟙 (unop b.1) ≫ f.1.unop))) ≫
            (c.2.map g.1).toFunctor.map
              ((g.2.app b.1).toFunctor.map
                ((f.2.app b.1).toFunctor.map
                  ((Z.app b.1).toFunctor.map ((λ_ f.1.unop).hom ≫ (ρ_ f.1.unop).inv)))) := by
    intro M A' Bb'
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc]
    erw [(g.2.naturality g.1).hom.toNatTrans.naturality
      ((f.2.app b.1).toFunctor.map
        ((Z.app b.1).toFunctor.map ((λ_ f.1.unop).hom ≫ (ρ_ f.1.unop).inv)))]
    erw [← Functor.map_comp_assoc]; rfl
  erw [reassoc_of% hT3]
  erw [Category.id_comp]
  simp only [Cat.Hom.comp_toFunctor, Functor.comp_map]
  iterate (first | erw [← Functor.map_comp_assoc] | erw [← Functor.map_comp])
  iterate erw [Category.assoc]
  iterate erw [← Functor.map_comp]
  dsimp only [postcomp₂, postcomposingCat, postcomp, Functor.toCatHom]
  iterate (first | erw [← Functor.map_comp_assoc] | erw [← Functor.map_comp])
  rfl

/--
The *forward strong transformation* `yonedaPairing ⟶ yonedaEvaluation` for the Yoneda lemma.

At each pair `x = (b, F)`, the component functor is `yonedaLemmaForwardsFunctor x`, which
sends a strong transformation `η : yoneda₀ b ⟶ F` to the element `η.app b (𝟙 b) : F.obj b`.

Mathematically, this is the "evaluate at identity" direction of the equivalence
  `StrongTrans(yoneda₀ b, F)  ≃  F.obj b`.
-/
def yonedaLemmaForwards : StrongTrans (@yonedaPairing B _) (@yonedaEvaluation B _) where
  app x := {toFunctor := yonedaLemmaForwardsFunctor x}
  naturality {a b} f := by
    refine Cat.Hom.isoMk (NatIso.ofComponents ?_ ?_)
    · intro X
      dsimp [yonedaEvaluation, catPseudoULift]
      have lem : (((yonedaPairing.map f).toFunctor.obj X).app b.1).toFunctor.obj (𝟙 (unop b.1)) ≅
          (yonedaEvaluation'.map f).toFunctor.obj ((X.app a.1).toFunctor.obj (𝟙 (unop a.1))) := by
        refine ?_ ≪≫
          (Cat.Hom.toNatIso (f.2.naturality f.1)).app ((X.app a.1).toFunctor.obj (𝟙 (unop a.1)))
        refine (f.2.app b.1).toFunctor.mapIso ?_
        exact ((X.app b.1).toFunctor.mapIso (λ_ f.1.unop ≪≫ (ρ_ f.1.unop).symm)) ≪≫
          (Cat.Hom.toNatIso (X.naturality f.1)).app (𝟙 (unop a.1))
      exact ULiftHom.up.mapIso (ULift.upFunctor.mapIso lem)
    · intro X Y h
      dsimp [yonedaPairing, ULiftHom.up, yonedaEvaluation, catPseudoULift, catLift, Functor.comp]
      simp only [map_comp, Category.assoc]
      exact Quiver.homOfEq_injective rfl rfl
        (congrArg (ULiftHom.up.map) (forwards_naturality_component f h))
  naturality_naturality {a b f g} η := by
    apply catLift_hom₂_ext; intro Z
    dsimp only [yonedaLemmaForwardsFunctor]
    simp only [Cat.Hom.toNatTrans_comp, NatTrans.comp_app, Cat.whiskerLeft_toNatTrans,
      Cat.whiskerRight_toNatTrans, whiskerLeft_app, whiskerRight_app,
      yonedaEvaluation_map₂_app_down,
      Cat.Hom.isoMk_hom, Cat.toCatHom₂_toNatTrans, NatIso.ofComponents_hom_app, id_eq,
      Functor.mapIso_hom, Iso.trans_hom, Iso.symm_hom]
    exact forwards_naturality_naturality_core η Z
  naturality_id a := by
    apply catLift_hom₂_ext; intro Z
    dsimp only [yonedaLemmaForwardsFunctor]
    simp only [Cat.Hom.toNatTrans_comp, NatTrans.comp_app, Cat.whiskerLeft_toNatTrans,
      Cat.whiskerRight_toNatTrans, whiskerLeft_app, whiskerRight_app,
      yonedaEvaluation_mapId_app_down,
      Cat.Hom.isoMk_hom, Cat.toCatHom₂_toNatTrans, NatIso.ofComponents_hom_app, id_eq,
      Functor.mapIso_hom, Iso.trans_hom, Iso.symm_hom, Cat.leftUnitor_hom_toNatTrans_app,
      Cat.rightUnitor_inv_toNatTrans_app]
    dsimp only [ULiftHom.up, ULift.upFunctor, ULiftHom.objDown, Functor.comp]
    simp only [Bicategory.prod_id_fst, Bicategory.prod_id_snd,
      Pseudofunctor.StrongTrans.categoryStruct_id_app, Cat.Hom.id_map,
      Iso.app_hom, Cat.Hom.toNatIso,
      Pseudofunctor.StrongTrans.categoryStruct_id_naturality_hom]
    simp only [Cat.Hom.toNatTrans_comp, NatTrans.comp_app, Cat.rightUnitor_hom_toNatTrans_app,
      Cat.leftUnitor_inv_toNatTrans_app]
    simp only [Category.comp_id, Cat.Hom.comp_toFunctor,
      Cat.Hom.id_toFunctor, Functor.comp_obj, Functor.id_obj]
    erw [Category.comp_id]
    exact forwards_naturality_id_core a Z
  naturality_comp {a b c} f g := by
    apply catLift_hom₂_ext; intro Z
    dsimp only [yonedaLemmaForwardsFunctor]
    simp only [Cat.Hom.toNatTrans_comp, NatTrans.comp_app, Cat.whiskerLeft_toNatTrans,
      Cat.whiskerRight_toNatTrans, whiskerLeft_app, whiskerRight_app,
      yonedaEvaluation_mapComp_app_down,
      Cat.Hom.isoMk_hom, Cat.toCatHom₂_toNatTrans, NatIso.ofComponents_hom_app, id_eq,
      Functor.mapIso_hom, Iso.trans_hom, Iso.symm_hom,
      Cat.associator_hom_toNatTrans_app, Cat.associator_inv_toNatTrans_app]
    dsimp only [ULiftHom.up, ULift.upFunctor, ULiftHom.objDown, Functor.comp]
    simp only [Bicategory.prod_comp_fst, Bicategory.prod_comp_snd, Iso.app_hom, Cat.Hom.toNatIso]
    simp only [Category.comp_id, Category.id_comp, Cat.Hom.comp_toFunctor, Functor.comp_obj]
    erw [yonedaEvaluation_map_map_down]
    exact forwards_naturality_comp_core f g Z

/--
At a fixed pair `x = (b₀, F)`, an evaluation point `eval : F.obj b₀`, and a component
`a : Bᵒᵖ`, the functor `(unop a ⟶ b₀) ⥤ F.obj a` sending `f ↦ (F.map f).obj eval`.

In terms of `yoneda₀ b₀`, the source category at `a` is the hom-category `(unop a ⟶ b₀)`:
* **On objects**: `f : unop a ⟶ b₀` maps to `(F.map (Quiver.Hom.op f)).obj eval : F.obj a`.
* **On morphisms**: a 2-cell `α : f ⟶ g` (a morphism in `Bᵒᵖ`) maps to
  `(F.map₂ (op2 α)).toNatTrans.app eval`.
* **Functoriality**: follows from `F.map₂_id` and `F.map₂_comp` via `erw` through the
  universe-level coercion introduced by `Cat.of`.

This is the functor underlying the `a`-component of `yonedaLemmaBackwardsFunctorObj`.
-/
@[simp]
def yonedaLemmaBackwardsFunctorObjFunctor (x : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat))
    (eval : yonedaEvaluation.obj x) (a : Bᵒᵖ) :
    ↑((yoneda₀ (unop x.1)).obj a) ⥤ ↑(x.2.obj a) where
  obj b := (x.2.map (Quiver.Hom.op b)).toFunctor.obj (ULift.down eval)
  map {X Y} f := (x.2.map₂ (op2 f)).toNatTrans.app (ULift.down eval)
  map_id _ := by erw [op2_id, PrelaxFunctor.map₂_id]; rfl
  map_comp _ _ := by erw [op2_comp, PrelaxFunctor.map₂_comp]; rfl

/-- Component form of `mapComp_id_right_hom`, matching the `naturality_id` obligation of
`yonedaLemmaBackwardsFunctorObj`: composing the `mapComp` coherence with the `mapId` coherence
is the image of the (opposite of the) left unitor. -/
lemma mapComp_id_component (F : Bᵒᵖ ⥤ᵖ Cat.{w, v}) {b₀ a : Bᵒᵖ}
    (X : unop a ⟶ unop b₀) (eval : ↑(F.obj b₀)) :
    (F.mapComp (Quiver.Hom.op X) (𝟙 a)).hom.toNatTrans.app eval ≫
      (F.mapId a).hom.toNatTrans.app ((F.map (Quiver.Hom.op X)).toFunctor.obj eval) =
    (F.map₂ (op2 (λ_ X).hom)).toNatTrans.app eval ≫
      𝟙 ((F.map (Quiver.Hom.op X)).toFunctor.obj eval) ≫
        𝟙 ((F.map (Quiver.Hom.op X)).toFunctor.obj eval) := by
  rw [Pseudofunctor.mapComp_id_right_hom]
  simp [op2_leftUnitor_hom]

/-- Component form of `mapComp_assoc_right_hom`, matching the `naturality_comp` obligation of
`yonedaLemmaBackwardsFunctorObj`. -/
lemma mapComp_assoc_component (F : Bᵒᵖ ⥤ᵖ Cat.{w, v}) {b₀ a b c : Bᵒᵖ}
    (f : a ⟶ b) (g : b ⟶ c) (X : unop a ⟶ unop b₀) (eval : ↑(F.obj b₀)) :
    (F.mapComp (Quiver.Hom.op X) (f ≫ g)).hom.toNatTrans.app eval ≫
      (F.mapComp f g).hom.toNatTrans.app ((F.map (Quiver.Hom.op X)).toFunctor.obj eval) =
    (F.map₂ (op2 (α_ g.unop f.unop X).hom)).toNatTrans.app eval ≫
      𝟙 ((F.map ((Quiver.Hom.op X ≫ f) ≫ g)).toFunctor.obj eval) ≫
        (F.mapComp (Quiver.Hom.op X ≫ f) g).hom.toNatTrans.app eval ≫
          𝟙 ((F.map g).toFunctor.obj ((F.map (Quiver.Hom.op X ≫ f)).toFunctor.obj eval)) ≫
            (F.map g).toFunctor.map
              ((F.mapComp (Quiver.Hom.op X) f).hom.toNatTrans.app eval) ≫
              𝟙 ((F.map g).toFunctor.obj ((F.map f).toFunctor.obj
                ((F.map (Quiver.Hom.op X)).toFunctor.obj eval))) := by
  simp only [op2_associator_hom]
  simpa using Cat.Hom₂.congr_app
    (F.mapComp_assoc_right_hom (Quiver.Hom.op X) f g) eval

/--
At a fixed pair `x = (b₀, F)` and an evaluation point `eval : F.obj b₀`, the strong
transformation `yoneda₀ b₀ ⟶ F` corresponding to `eval` under the Yoneda embedding.

* **Component at `a`**: the functor `yonedaLemmaBackwardsFunctorObjFunctor x eval a`, which
  sends `f : unop a ⟶ b₀` to `(F.map f).obj eval`.
* **Naturality at `f : a ⟶ b`**: an isomorphism built from the associativity coherence
  `F.mapComp`, whose hom component at `X` is `(F.mapComp (op X) f).hom.app eval` and whose
  inv component at `X` is `(F.mapComp (op X) f).inv.app eval`.  The inv-hom round-trip uses
  `Cat.Hom₂.comp_app` to convert composition of 2-cells into composition in the fibre.

This is the "Yoneda element" — the object in `yonedaPairing.obj x` that
`yonedaLemmaBackwardsFunctor` sends `eval` to.
-/
@[simp]
def yonedaLemmaBackwardsFunctorObj (x : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat))
    (eval : yonedaEvaluation.obj x) : yonedaPairing.obj x where
  app a := {toFunctor := yonedaLemmaBackwardsFunctorObjFunctor x eval a}
  naturality {a b} f := by
    refine Cat.Hom.isoMk (NatIso.ofComponents ?_ ?_)
    · intro X
      exact (Cat.Hom.toNatIso (x.2.mapComp (Quiver.Hom.op X) f)).app
        (ULift.casesOn eval fun eval ↦ eval)
    · intro X Y g
      rcases eval with ⟨eval⟩
      simp only [yoneda₀_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj_α,
        yonedaLemmaBackwardsFunctorObjFunctor, op_unop, Cat.Hom.comp_toFunctor, comp_obj,
        yoneda₀_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map_toFunctor_obj, op_comp,
        Quiver.Hom.op_unop, Functor.comp_map,
        yoneda₀_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map_toFunctor_map,
        op2_whiskerLeft, map₂_whisker_right, Cat.Hom.toNatTrans_comp, Cat.whiskerRight_toNatTrans,
        NatTrans.comp_app, whiskerRight_app,
        Category.assoc]
      congr 1
      rcases x.2.mapComp (Quiver.Hom.op Y) f with ⟨hom, inv, _, inv_hom⟩
      dsimp [yonedaEvaluation'] at eval
      have : inv.toNatTrans.app eval ≫ hom.toNatTrans.app eval =
          (inv ≫ hom).toNatTrans.app eval := by
        simp
      erw [this, inv_hom]
      simp
  naturality_naturality {a b c} f g := by
    rcases eval with ⟨eval⟩
    exact Cat.Hom₂.ext_app fun X ↦
      Cat.Hom₂.congr_app (x.2.toOplax.mapComp_naturality_right (Quiver.Hom.op X) g) eval
  naturality_id a := by
    rcases eval with ⟨eval⟩
    exact Cat.Hom₂.ext_app fun X ↦ mapComp_id_component x.2 X eval
  naturality_comp {a b c} f g := by
    rcases eval with ⟨eval⟩
    exact Cat.Hom₂.ext_app fun X ↦ mapComp_assoc_component x.2 f g X eval

/--
At a fixed pair `x = (b₀, F)`, the *Yoneda embedding functor*
`F.obj b₀ ⥤ StrongTrans (yoneda₀ b₀) F`.

* **On objects**: sends an element `eval : F.obj b₀` to the strong transformation
  `yonedaLemmaBackwardsFunctorObj x eval`, whose `a`-component sends
  `f : unop a ⟶ b₀` to `(F.map f).obj eval`.
* **On morphisms**: sends a morphism `g : eval ⟶ eval'` (lowered through `catLiftEquiv`) to the
  modification whose `c`-component has, at each `X`, the morphism
  `(F.map (op X)).map ((catLiftEquiv (F.obj b₀)).inverse.map g)`.

This is the component functor of the strong transformation `yonedaLemmaBackwards`.
-/
@[simp]
def yonedaLemmaBackwardsFunctor (x : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat)) :
    yonedaEvaluation.obj x ⥤ yonedaPairing.obj x where
  obj a := yonedaLemmaBackwardsFunctorObj x a
  map {a b} f := by
    rcases a with ⟨a⟩
    rcases b with ⟨b⟩
    refine { as := { app := ?_, naturality := ?_ } }
    · intro c
      refine { toNatTrans := { app := ?_, naturality := ?_ } }
      · exact fun X ↦ (x.2.map (Quiver.Hom.op X)).toFunctor.map
          ((catLiftEquiv.{w, max u v, v, max u (max v w)} ↑(yonedaEvaluation'.obj x)).inverse.map f)
      · intro X Y g
        simp only [yoneda₀_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj_α,
          yonedaLemmaBackwardsFunctorObj, yonedaLemmaBackwardsFunctorObjFunctor, op_unop,
          Cat.Hom.comp_toFunctor, Cat.coe_of, NatTrans.naturality]
    · intro t u g
      refine Cat.Hom₂.ext_iff.mpr ?_
      ext c
      rw [Cat.Hom.toNatTrans_comp, Cat.Hom.toNatTrans_comp]
      simp only [yoneda₀_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj_α,
        yonedaLemmaBackwardsFunctorObj, yonedaLemmaBackwardsFunctorObjFunctor, op_unop,
        Cat.Hom.comp_toFunctor, comp_obj,
        yoneda₀_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map_toFunctor_obj, op_comp,
        Quiver.Hom.op_unop, Cat.coe_of, Cat.whiskerLeft_toNatTrans, Cat.Hom.isoMk_hom,
        NatTrans.toCatHom₂_toNatTrans, Cat.whiskerRight_toNatTrans]
      exact (x.2.mapComp (Quiver.Hom.op c) g).hom.toNatTrans.naturality
        ((catLiftEquiv.{w, max u v, v, max u (max v w)} ↑(yonedaEvaluation'.obj x)).inverse.map f)
  map_id X := by
    obtain ⟨a⟩ := X
    apply homCategory.ext
    intro c
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext W
    exact (congrArg (x.2.map (Quiver.Hom.op W)).toFunctor.map
        ((catLiftEquiv.{w, max u v, v, max u (max v w)}
          ↑(yonedaEvaluation'.obj x)).inverse.map_id _)).trans
      ((x.2.map (Quiver.Hom.op W)).toFunctor.map_id _)
  map_comp {X Y Z} f g := by
    obtain ⟨a⟩ := X
    obtain ⟨b⟩ := Y
    obtain ⟨c'⟩ := Z
    apply homCategory.ext
    intro c
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext W
    exact (congrArg (x.2.map (Quiver.Hom.op W)).toFunctor.map
        ((catLiftEquiv.{w, max u v, v, max u (max v w)}
          ↑(yonedaEvaluation'.obj x)).inverse.map_comp f g)).trans
      ((x.2.map (Quiver.Hom.op W)).toFunctor.map_comp _ _)

/-- The inner naturality square for `yonedaLemmaBackwards`: sliding a 2-cell of the
represented object past the `mapComp` and `naturality` coherence isos.  Assembled from the
inverse forms of `mapComp_naturality_right` (for both pseudofunctors) and
`naturality_naturality` of the strong transformation. -/
lemma backwards_inner_component {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b) {α : Bᵒᵖ}
    {XX YY : ↑((yoneda₀ (unop b.1)).obj α)} (h : XX ⟶ YY) (X : ↑(yonedaEvaluation'.obj a)) :
    (b.2.map₂ (op2 h)).toNatTrans.app
        ((b.2.map f.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj X)) ≫
      (b.2.mapComp f.1 (Quiver.Hom.op YY)).inv.toNatTrans.app
        ((f.2.app a.1).toFunctor.obj X) ≫
        (f.2.naturality (f.1 ≫ Quiver.Hom.op YY)).inv.toNatTrans.app X =
    ((b.2.mapComp f.1 (Quiver.Hom.op XX)).inv.toNatTrans.app
        ((f.2.app a.1).toFunctor.obj X) ≫
        (f.2.naturality (f.1 ≫ Quiver.Hom.op XX)).inv.toNatTrans.app X) ≫
      (f.2.app α).toFunctor.map
        (((a.2.mapComp f.1 (Quiver.Hom.op XX)).hom ≫
            a.2.map f.1 ◁ a.2.map₂ (op2 h) ≫
              (a.2.mapComp f.1 (Quiver.Hom.op YY)).inv).toNatTrans.app X) := by
  have h1 := Cat.Hom₂.congr_app
    (b.2.toOplax.mapComp_naturality_right f.1 (op2 h)) ((f.2.app a.1).toFunctor.obj X)
  have h2 := Cat.Hom₂.congr_app (f.2.naturality_naturality (f.1 ◁ op2 h)) X
  have h3 := Cat.Hom₂.congr_app
    (a.2.toOplax.mapComp_naturality_right f.1 (op2 h)) X
  dsimp at h1 h2 h3
  -- s1: slide map₂(op2 h) past the b.2.mapComp iso (inverse form of h1)
  have s1 : (b.2.map₂ (op2 h)).toNatTrans.app
        ((b.2.map f.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj X)) ≫
      (b.2.mapComp f.1 (Quiver.Hom.op YY)).inv.toNatTrans.app
        ((f.2.app a.1).toFunctor.obj X) =
      (b.2.mapComp f.1 (Quiver.Hom.op XX)).inv.toNatTrans.app
        ((f.2.app a.1).toFunctor.obj X) ≫
      (b.2.map₂ (f.1 ◁ op2 h)).toNatTrans.app ((f.2.app a.1).toFunctor.obj X) := by
    apply (Iso.comp_inv_eq ((Cat.Hom.toNatIso
      (b.2.mapComp f.1 (Quiver.Hom.op YY))).app ((f.2.app a.1).toFunctor.obj X))).mpr
    erw [Category.assoc]
    apply (Iso.eq_inv_comp ((Cat.Hom.toNatIso
      (b.2.mapComp f.1 (Quiver.Hom.op XX))).app ((f.2.app a.1).toFunctor.obj X))).mpr
    exact h1.symm
  -- s2: slide b.2.map₂ (f.1 ◁ op2 h) past f.2.naturality (inverse form of h2)
  have s2 : (b.2.map₂ (f.1 ◁ op2 h)).toNatTrans.app ((f.2.app a.1).toFunctor.obj X) ≫
      (f.2.naturality (f.1 ≫ Quiver.Hom.op YY)).inv.toNatTrans.app X =
      (f.2.naturality (f.1 ≫ Quiver.Hom.op XX)).inv.toNatTrans.app X ≫
      (f.2.app α).toFunctor.map ((a.2.map₂ (f.1 ◁ op2 h)).toNatTrans.app X) := by
    apply (Iso.comp_inv_eq ((Cat.Hom.toNatIso
      (f.2.naturality (f.1 ≫ Quiver.Hom.op YY))).app X)).mpr
    erw [Category.assoc]
    apply (Iso.eq_inv_comp ((Cat.Hom.toNatIso
      (f.2.naturality (f.1 ≫ Quiver.Hom.op XX))).app X)).mpr
    exact h2.symm
  -- s3: the conjugated 2-cell collapses (component form of h3)
  have s3 : ((a.2.mapComp f.1 (Quiver.Hom.op XX)).hom ≫
        a.2.map f.1 ◁ a.2.map₂ (op2 h) ≫
          (a.2.mapComp f.1 (Quiver.Hom.op YY)).inv).toNatTrans.app X =
      (a.2.map₂ (f.1 ◁ op2 h)).toNatTrans.app X := by
    simp only [Cat.Hom.toNatTrans_comp, NatTrans.comp_app]
    rw [← Category.assoc]
    apply (Iso.comp_inv_eq ((Cat.Hom.toNatIso
      (a.2.mapComp f.1 (Quiver.Hom.op YY))).app X)).mpr
    exact h3.symm
  rw [← Category.assoc, s1]
  erw [Category.assoc, s2]
  rw [← s3]
  erw [← Category.assoc]
  rfl

/-- Component (at `α`) of the naturality iso of `yonedaLemmaBackwards` at `f : a ⟶ b`. -/
def backwardsNaturalityIsoApp {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b)
    (X : ↑(yonedaEvaluation.obj a)) (α : Bᵒᵖ) :
    (((yonedaEvaluation.map f).toFunctor ⋙ yonedaLemmaBackwardsFunctor b).obj X).app α ≅
      ((yonedaLemmaBackwardsFunctor a ⋙ (yonedaPairing.map f).toFunctor).obj X).app α :=
  Cat.Hom.isoMk (NatIso.ofComponents
    (fun XX ↦
      (Cat.Hom.toNatIso (b.2.mapComp f.1 XX.op).symm).app
        ((f.2.app a.1).toFunctor.obj (ULift.down X)) ≪≫
        (Cat.Hom.toNatIso (f.2.naturality (f.1 ≫ XX.op))).symm.app (ULift.down X))
    (fun {XX YY} h ↦ by
      dsimp [yonedaEvaluation, catPseudoULift, catLift, Functor.comp,
        ULiftHomULiftCategory.equivCongrLeft, ULiftHom.objUp, ULift.upFunctor,
        ULiftHom.objDown, yonedaEvaluation']
      erw [Pseudofunctor.map₂_whisker_left]
      exact backwards_inner_component f h (ULift.down X)))

/-- The cancellation core of the backwards naturality square: all atoms in canonical
spelling, `X` unlifted. -/
lemma backwards_square_core {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b)
    (X : ↑(yonedaEvaluation'.obj a)) {a₁ b₁ : Bᵒᵖ} (f₁ : a₁ ⟶ b₁)
    (ZZ : ↑((yoneda₀ (unop b.1)).obj a₁)) :
    (f.2.app b₁).toFunctor.map
        ((a.2.map₂ (α_ f.1 (Quiver.Hom.op ZZ) f₁).inv).toNatTrans.app X) ≫
      (f.2.app b₁).toFunctor.map
        ((a.2.mapComp (f.1 ≫ Quiver.Hom.op ZZ) f₁).hom.toNatTrans.app X) ≫
      (f.2.naturality f₁).hom.toNatTrans.app
        ((a.2.map (f.1 ≫ Quiver.Hom.op ZZ)).toFunctor.obj X) =
    (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ ≫ f₁)).hom.toNatTrans.app X ≫
      (b.2.mapComp f.1 (Quiver.Hom.op ZZ ≫ f₁)).hom.toNatTrans.app
        ((f.2.app a.1).toFunctor.obj X) ≫
      (b.2.mapComp (Quiver.Hom.op ZZ) f₁).hom.toNatTrans.app
        ((b.2.map f.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj X)) ≫
      (b.2.map f₁).toFunctor.map
        ((b.2.mapComp f.1 (Quiver.Hom.op ZZ)).inv.toNatTrans.app
            ((f.2.app a.1).toFunctor.obj X) ≫
          (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app X) := by
  have h3 := Pseudofunctor.mapComp_assoc_right_hom_app b.2 f.1 (Quiver.Hom.op ZZ) f₁
    ((f.2.app a.1).toFunctor.obj X)
  rw [Pseudofunctor.StrongTrans.naturality_naturality_hom_app f.2
      (α_ f.1 (Quiver.Hom.op ZZ) f₁) X,
    Pseudofunctor.StrongTrans.naturality_comp_hom_app f.2 (f.1 ≫ Quiver.Hom.op ZZ) f₁ X]
  simp only [Category.assoc]
  erw [reassoc_of% h3]
  have h1 := Pseudofunctor.StrongTrans.naturality_naturality_hom_app f.2
    (α_ f.1 (Quiver.Hom.op ZZ) f₁) X
  have h2 := Pseudofunctor.StrongTrans.naturality_comp_hom_app f.2
    (f.1 ≫ Quiver.Hom.op ZZ) f₁ X
  have c1 : (b.2.map₂ (α_ f.1 (Quiver.Hom.op ZZ) f₁).hom).toNatTrans.app
        ((f.2.app a.1).toFunctor.obj X) ≫
      (b.2.map₂ (α_ f.1 (Quiver.Hom.op ZZ) f₁).inv).toNatTrans.app
        ((f.2.app a.1).toFunctor.obj X) = 𝟙 _ := by
    rw [← Cat.Hom₂.comp_app, ← PrelaxFunctor.map₂_comp, Iso.hom_inv_id,
      PrelaxFunctor.map₂_id, Cat.Hom₂.id_app]
  have c2 := Cat.Hom.inv_hom_id_toNatTrans_app (b.2.mapComp (f.1 ≫ Quiver.Hom.op ZZ) f₁)
    ((f.2.app a.1).toFunctor.obj X)
  have c3 := Cat.Hom.hom_inv_id_toNatTrans_app (b.2.mapComp f.1 (Quiver.Hom.op ZZ))
    ((f.2.app a.1).toFunctor.obj X)
  have c4 := Cat.Hom.hom_inv_id_toNatTrans_app (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ)) X
  have hN := h1
  rw [h2] at hN
  simp only [Category.assoc] at hN
  erw [← hN]
  erw [reassoc_of% h1]
  erw [reassoc_of% c1]
  erw [reassoc_of% h2]
  erw [reassoc_of% c2]
  rw [← Functor.map_comp, ← Functor.map_comp]
  erw [reassoc_of% c3]
  erw [c4]
  erw [Functor.map_id]
  erw [Category.comp_id]
  rfl

/-- Point form of the naturality square, spelled through the composite strong
transformation (defeq to `yonedaPairing.map`'s literal pasting).

The proof distributes the strong-transformation component through the whiskered/associated
composite from `categoryStruct_comp_naturality_hom`. This is an ordered `erw` chain rather
than a `simp only`: the `≫`/`α_`/`▷` come from the `postcomp₂` bicategory and are only *defeq*
to `Cat`'s operations (an instance diamond), so the `Cat.*_app` distribution lemmas match at
default transparency but not reducible. The order is fixed by the composite's shape. -/
lemma backwards_square_component {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b)
    (X : ↑(yonedaEvaluation.obj a)) {a₁ b₁ : Bᵒᵖ} (f₁ : a₁ ⟶ b₁)
    (ZZ : ↑((yoneda₀ (unop b.1)).obj a₁)) :
    ((b.2.mapComp f.1 (Quiver.Hom.op ZZ ≫ f₁)).inv.toNatTrans.app
        ((f.2.app a.1).toFunctor.obj (ULift.down X)) ≫
      (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ ≫ f₁)).inv.toNatTrans.app (ULift.down X)) ≫
      ((postcomp₂ f.1.unop ≫ (yonedaLemmaBackwardsFunctorObj a X ≫ f.2)).naturality
        f₁).hom.toNatTrans.app ZZ =
    (b.2.mapComp (Quiver.Hom.op ZZ) f₁).hom.toNatTrans.app
        ((b.2.map f.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj (ULift.down X))) ≫
      (b.2.map f₁).toFunctor.map
        ((b.2.mapComp f.1 (Quiver.Hom.op ZZ)).inv.toNatTrans.app
            ((f.2.app a.1).toFunctor.obj (ULift.down X)) ≫
          (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app (ULift.down X)) := by
  obtain ⟨X⟩ := X
  simp only [categoryStruct_comp_naturality_hom]
  iterate 4 erw [Cat.Hom₂.comp_app]
  erw [Cat.associator_inv_app]
  erw [Cat.whiskerRight_app]
  erw [Cat.associator_hom_app]
  erw [Cat.whiskerLeft_app]
  iterate 4 erw [Cat.Hom₂.comp_app]
  erw [Cat.associator_inv_app]
  erw [Cat.whiskerRight_app]
  erw [Cat.associator_hom_app]
  erw [Cat.whiskerLeft_app]
  erw [Cat.whiskerLeft_app]
  iterate 3 erw [eqToHom_refl]
  iterate 3 erw [Category.id_comp]
  erw [Cat.associator_inv_app]
  iterate 4 (first | erw [eqToHom_refl] | erw [Category.id_comp] | erw [Category.comp_id])
  dsimp only [postcomp₂, postcomposingCat]
  simp only [Category.assoc]
  apply (Iso.inv_comp_eq ((Cat.Hom.toNatIso (b.2.mapComp f.1 (Quiver.Hom.op ZZ ≫ f₁))).app
    ((f.2.app a.1).toFunctor.obj X))).mpr
  apply (Iso.inv_comp_eq ((Cat.Hom.toNatIso (f.2.naturality
    (f.1 ≫ Quiver.Hom.op ZZ ≫ f₁))).app X)).mpr
  exact backwards_square_core f X f₁ ZZ

/-- The strong-transformation naturality square for `backwardsNaturalityIsoApp`. -/
lemma backwards_naturality_square {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b)
    (X : ↑(yonedaEvaluation.obj a)) {a₁ b₁ : Bᵒᵖ} (f₁ : a₁ ⟶ b₁) :
    (yoneda₀ (unop b.1)).map f₁ ◁ (backwardsNaturalityIsoApp f X b₁).hom ≫
      (((yonedaLemmaBackwardsFunctor a ⋙ (yonedaPairing.map f).toFunctor).obj X).naturality
        f₁).hom =
    ((((yonedaEvaluation.map f).toFunctor ⋙ yonedaLemmaBackwardsFunctor b).obj X).naturality
        f₁).hom ≫ (backwardsNaturalityIsoApp f X a₁).hom ▷ b.2.map f₁ := by
  apply Cat.Hom₂.ext_app
  intro ZZ
  simp only [Cat.Hom.toNatTrans_comp, NatTrans.comp_app, Cat.whiskerLeft_toNatTrans,
    Cat.whiskerRight_toNatTrans, whiskerLeft_app, whiskerRight_app]
  exact backwards_square_component f X f₁ ZZ

/-- The naturality iso of `yonedaLemmaBackwards` at `f : a ⟶ b`, componentwise. -/
def backwardsNaturalityIso {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b)
    (X : ↑(yonedaEvaluation.obj a)) :
    ((yonedaEvaluation.map f).toFunctor ⋙ yonedaLemmaBackwardsFunctor b).obj X ≅
      (yonedaLemmaBackwardsFunctor a ⋙ (yonedaPairing.map f).toFunctor).obj X :=
  StrongTrans.isoMk (fun α ↦ backwardsNaturalityIsoApp f X α)
    (fun f₁ ↦ backwards_naturality_square f X f₁)

/-- The cancellation core of `backwards_naturality_iso_natural`: two `NatTrans.naturality`
squares of the component isos, in canonical spellings. -/
lemma backwards_natural_core {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b)
    {X Y : ↑(yonedaEvaluation'.obj a)} (f₁ : X ⟶ Y) {γ : Bᵒᵖ}
    (ZZ : ↑((yoneda₀ (unop b.1)).obj γ)) :
    (b.2.map f.1 ≫ b.2.map (Quiver.Hom.op ZZ)).toFunctor.map
        ((f.2.app a.1).toFunctor.map f₁) ≫
      (b.2.mapComp f.1 (Quiver.Hom.op ZZ)).inv.toNatTrans.app
        ((f.2.app a.1).toFunctor.obj Y) ≫
      (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app Y =
    ((b.2.mapComp f.1 (Quiver.Hom.op ZZ)).inv.toNatTrans.app
        ((f.2.app a.1).toFunctor.obj X) ≫
      (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app X) ≫
      (f.2.app γ).toFunctor.map ((a.2.map (f.1 ≫ Quiver.Hom.op ZZ)).toFunctor.map f₁) := by
  have s1 := (b.2.mapComp f.1 (Quiver.Hom.op ZZ)).inv.toNatTrans.naturality
    ((f.2.app a.1).toFunctor.map f₁)
  have s2 : (b.2.map (f.1 ≫ Quiver.Hom.op ZZ)).toFunctor.map
        ((f.2.app a.1).toFunctor.map f₁) ≫
      (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app Y =
      (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app X ≫
      (f.2.app γ).toFunctor.map ((a.2.map (f.1 ≫ Quiver.Hom.op ZZ)).toFunctor.map f₁) :=
    (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.naturality f₁
  rw [reassoc_of% s1, s2]
  exact (Category.assoc _ _ _).symm

/-- Naturality (in `X`) of `backwardsNaturalityIso`. -/
lemma backwards_naturality_iso_natural {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b)
    {X Y : ↑(yonedaEvaluation.obj a)} (f₁ : X ⟶ Y) :
    ((yonedaEvaluation.map f).toFunctor ⋙ yonedaLemmaBackwardsFunctor b).map f₁ ≫
      (backwardsNaturalityIso f Y).hom =
    (backwardsNaturalityIso f X).hom ≫
      (yonedaLemmaBackwardsFunctor a ⋙ (yonedaPairing.map f).toFunctor).map f₁ := by
  obtain ⟨X⟩ := X
  obtain ⟨Y⟩ := Y
  obtain ⟨f₁⟩ := f₁
  apply homCategory.ext
  intro γ
  apply Cat.Hom₂.ext_app
  intro ZZ
  erw [homCategory_comp_as_app, homCategory_comp_as_app]
  dsimp only [backwardsNaturalityIso]
  simp only [isoMk_hom_as_app]
  exact backwards_natural_core f f₁ ZZ

/-- Lift-plumbing reduction: the backwards functor's `.map` component, stated with the
morphism generic so the def's internal `rcases` fires, so it holds by `rfl`.  Must be applied
with `erw` (the `StrongTrans` `homCategory` diamond). -/
lemma back_map_comp (x : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})) {A₀ B₀ : ↑(yonedaEvaluation'.obj x)}
    (m : A₀ ⟶ B₀) (c : Bᵒᵖ) (W : ↑((yoneda₀ (unop x.1)).obj c)) :
    (((((yonedaLemmaBackwardsFunctor x).map { down := m }).as.app c).toNatTrans).app W)
      = (x.2.map (Quiver.Hom.op W)).toFunctor.map m := rfl

/-- The reduced fibre-morphism core of `naturality_naturality` for `yonedaLemmaBackwards`:
the 2-cell coherence descended to a single fibre `↑(b.2.obj γ)`.  Using the composite 2-cell
`θ = η.1 ▷ ZZ.op` linearizes the proof into three inverse slides — the `b.2.mapComp`
naturality (`hmc`), the strong-transformation `naturality_naturality` (`hnn`), and the
modification naturality of `η.2` (`hmod`) — plus the `mapComp`-inverse point transport. -/
lemma backwards_naturality_naturality_core {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} {f g : a ⟶ b}
    (η : f ⟶ g) (x : ↑(yonedaEvaluation'.obj a)) {γ : Bᵒᵖ}
    (ZZ : ↑((yoneda₀ (unop b.1)).obj γ)) :
    (b.2.map (Quiver.Hom.op ZZ)).toFunctor.map
        ((b.2.map f.1).toFunctor.map ((η.2.as.app a.1).toNatTrans.app x) ≫
          (b.2.map₂ η.1).toNatTrans.app ((g.2.app a.1).toFunctor.obj x)) ≫
      (b.2.mapComp g.1 (Quiver.Hom.op ZZ)).inv.toNatTrans.app ((g.2.app a.1).toFunctor.obj x) ≫
        (g.2.naturality (g.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app x =
    ((b.2.mapComp f.1 (Quiver.Hom.op ZZ)).inv.toNatTrans.app ((f.2.app a.1).toFunctor.obj x) ≫
        (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app x) ≫
      (f.2.app γ).toFunctor.map ((a.2.map₂ (op2 (ZZ ◁ η.1.unop2))).toNatTrans.app x) ≫
        (η.2.as.app γ).toNatTrans.app
          ((a.2.map (Quiver.Hom.op
            ((postcomp (unop γ) g.1.unop).toCatHom.toFunctor.obj ZZ))).toFunctor.obj x) := by
  -- The three coherences, component-distributed (θ = η.1 ▷ ZZ.op linearizes the chain)
  have hmc := Cat.Hom₂.congr_app
    (b.2.toOplax.mapComp_naturality_left η.1 (Quiver.Hom.op ZZ)) ((g.2.app a.1).toFunctor.obj x)
  have hnn := Cat.Hom₂.congr_app
    (g.2.naturality_naturality (η.1 ▷ Quiver.Hom.op ZZ)) x
  have hmod := modification_naturality_app η.2 (f.1 ≫ Quiver.Hom.op ZZ) x
  simp only [Cat.Hom.toNatTrans_comp, NatTrans.comp_app, Cat.whiskerLeft_toNatTrans,
    Cat.whiskerRight_toNatTrans, whiskerLeft_app, whiskerRight_app] at hmc hnn hmod
  -- hmc_inv: slide map₂ η.1 past the b.2.mapComp iso (inverse form), point G_ax
  have hmc_inv : (b.2.map (Quiver.Hom.op ZZ)).toFunctor.map
        ((b.2.map₂ η.1).toNatTrans.app ((g.2.app a.1).toFunctor.obj x)) ≫
      (b.2.mapComp g.1 (Quiver.Hom.op ZZ)).inv.toNatTrans.app ((g.2.app a.1).toFunctor.obj x) =
      (b.2.mapComp f.1 (Quiver.Hom.op ZZ)).inv.toNatTrans.app ((g.2.app a.1).toFunctor.obj x) ≫
        (b.2.map₂ (η.1 ▷ Quiver.Hom.op ZZ)).toNatTrans.app ((g.2.app a.1).toFunctor.obj x) := by
    apply (Iso.comp_inv_eq ((Cat.Hom.toNatIso (b.2.mapComp g.1 (Quiver.Hom.op ZZ))).app
      ((g.2.app a.1).toFunctor.obj x))).mpr
    erw [Category.assoc]
    apply (Iso.eq_inv_comp ((Cat.Hom.toNatIso (b.2.mapComp f.1 (Quiver.Hom.op ZZ))).app
      ((g.2.app a.1).toFunctor.obj x))).mpr
    exact hmc.symm
  -- hnn_inv: slide map₂ (η.1 ▷ ZZ.op) past g.2.naturality (inverse form), point x
  have hnn_inv : (b.2.map₂ (η.1 ▷ Quiver.Hom.op ZZ)).toNatTrans.app
        ((g.2.app a.1).toFunctor.obj x) ≫
      (g.2.naturality (g.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app x =
      (g.2.naturality (f.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app x ≫
        (g.2.app γ).toFunctor.map ((a.2.map₂ (η.1 ▷ Quiver.Hom.op ZZ)).toNatTrans.app x) := by
    apply (Iso.comp_inv_eq ((Cat.Hom.toNatIso (g.2.naturality (g.1 ≫ Quiver.Hom.op ZZ))).app x)).mpr
    erw [Category.assoc]
    apply (Iso.eq_inv_comp ((Cat.Hom.toNatIso
      (g.2.naturality (f.1 ≫ Quiver.Hom.op ZZ))).app x)).mpr
    exact hnn.symm
  rw [Functor.map_comp]
  erw [Category.assoc]
  erw [reassoc_of% hmc_inv]
  erw [Category.assoc]
  erw [hnn_inv]
  -- remaining η.2 coherences
  have hη2 := (η.2.as.app γ).toNatTrans.naturality
    ((a.2.map₂ (op2 (ZZ ◁ η.1.unop2))).toNatTrans.app x)
  have hMCinv := (b.2.mapComp f.1 (Quiver.Hom.op ZZ)).inv.toNatTrans.naturality
    ((η.2.as.app a.1).toNatTrans.app x)
  dsimp at hmod hη2 hMCinv
  -- hmod_inv: slide mfZZ.map P past g.2.naturality → f.2.naturality (modification), point x
  have hmod_inv : (b.2.map (f.1 ≫ Quiver.Hom.op ZZ)).toFunctor.map
        ((η.2.as.app a.1).toNatTrans.app x) ≫
      (g.2.naturality (f.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app x =
      (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app x ≫
        (η.2.as.app γ).toNatTrans.app ((a.2.map (f.1 ≫ Quiver.Hom.op ZZ)).toFunctor.obj x) := by
    apply (Iso.comp_inv_eq ((Cat.Hom.toNatIso (g.2.naturality (f.1 ≫ Quiver.Hom.op ZZ))).app x)).mpr
    erw [Category.assoc]
    apply (Iso.eq_inv_comp ((Cat.Hom.toNatIso
      (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ))).app x)).mpr
    exact hmod.symm
  erw [reassoc_of% hMCinv, reassoc_of% hmod_inv]
  erw [Category.assoc, ← hη2, ← Category.assoc]
  rfl

/--
The *backward strong transformation* `yonedaEvaluation ⟶ yonedaPairing` for the Yoneda lemma.

At each pair `x = (b₀, F)`, the component functor is `yonedaLemmaBackwardsFunctor x`, the
Yoneda embedding functor sending `s : F.obj b₀` to the strong transformation
`(a, f) ↦ (F.map f).obj s`.

This is the inverse direction of the Yoneda equivalence.  Together with `yonedaLemmaForwards`
and the unit/counit isos (`yonedaHomInvId`, `yonedaInvHomId`), it forms `yonedaLemma`.
-/
def yonedaLemmaBackwards : StrongTrans (@yonedaEvaluation B _)  (@yonedaPairing B _) where
  app x := {toFunctor := yonedaLemmaBackwardsFunctor x}
  naturality {a b} f :=
    Cat.Hom.isoMk (NatIso.ofComponents (fun X ↦ backwardsNaturalityIso f X)
      (fun {X Y} f₁ ↦ backwards_naturality_iso_natural f f₁))
  naturality_naturality {a b f g} η := by
    apply Cat.Hom₂.ext_app
    intro X
    obtain ⟨x⟩ := X
    simp only [Cat.Hom.toNatTrans_comp, NatTrans.comp_app, Cat.whiskerLeft_toNatTrans,
      Cat.whiskerRight_toNatTrans, whiskerLeft_app, whiskerRight_app, yonedaEvaluation_map₂_app_down,
      Cat.Hom.isoMk_hom, Cat.toCatHom₂_toNatTrans, NatIso.ofComponents_hom_app]
    apply homCategory.ext
    intro γ
    erw [homCategory_comp_as_app, homCategory_comp_as_app]
    apply Cat.Hom₂.ext_app
    intro ZZ
    dsimp only [backwardsNaturalityIso, backwardsNaturalityIsoApp]
    simp only [Cat.Hom.toNatTrans_comp, NatTrans.comp_app, isoMk_hom_as_app, Cat.Hom.isoMk_hom,
      Cat.toCatHom₂_toNatTrans, NatIso.ofComponents_hom_app, Iso.trans_hom, Iso.symm_hom,
      Iso.app_hom, Cat.Hom.toNatIso]
    erw [back_map_comp]
    dsimp only [yonedaPairing]
    simp only [NatTrans.toCatHom₂_toNatTrans]
    dsimp only [yonedaPairingMap₂, yonedaPairingMapFunctor, Functor.whiskerLeft,
      Functor.whiskerRight, precomposing, postcomposing, precomposingCat, postcomposingCat,
      postcomposing₂]
    erw [homCategory_comp_as_app]
    simp only [Cat.Hom.toNatTrans_comp, NatTrans.comp_app, Cat.whiskerRight_toNatTrans,
      whiskerRight_app, whiskerRight_as_app, Cat.toCatHom₂_toNatTrans]
    simp only [precomp_map, postcomp₂, postcomposingCat, postcomp_obj,
      Pseudofunctor.StrongTrans.comp_app, Functor.comp_map, Cat.Hom.comp_toFunctor]
    dsimp only [yonedaLemmaBackwardsFunctor, yonedaLemmaBackwardsFunctorObj,
      yonedaLemmaBackwardsFunctorObjFunctor, yonedaEvaluation']
    simp only [Cat.Hom.toNatTrans_comp, NatTrans.comp_app, Cat.whiskerLeft_toNatTrans,
      Cat.whiskerRight_toNatTrans, whiskerLeft_app, whiskerRight_app, whiskerLeft_as_app]
    exact backwards_naturality_naturality_core η x ZZ
  naturality_id a := by sorry
  naturality_comp {a b c} f g := by sorry

/--
The data of an internal equivalence in a bicategory `B` between objects `x` and `y`.

* `map : x ⟶ y` — the forward 1-morphism.
* `inv : y ⟶ x` — the backward 1-morphism.
* `homInvId : map ≫ inv ≅ 𝟙 x` — a 2-isomorphism witnessing that `inv` is a left inverse
  of `map` up to isomorphism.
* `invHomId : inv ≫ map ≅ 𝟙 y` — a 2-isomorphism witnessing that `inv` is a right inverse
  of `map` up to isomorphism.

Note: this is weaker than an adjoint equivalence (no triangle identities are required), but
sufficient to state the Yoneda lemma as a bicategorical equivalence.
-/
structure BiEquiv (x y : B) where
  map : x ⟶ y
  inv : y ⟶ x
  homInvId : map ≫ inv ≅ 𝟙 x
  invHomId : inv ≫ map ≅ 𝟙 y

/--
The canonical isomorphism used to build the unit of the Yoneda equivalence.

Given:
* `a = (b₀, F)` — a pair in `Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat)`,
* `b : Bᵒᵖ` — the component,
* `x : yonedaPairing.obj a` — a strong transformation `yoneda₀ b₀ ⟶ F`,
* `f : unop b ⟶ b₀` — an object of `(yoneda₀ b₀).obj b`,

this is the isomorphism
  `(yonedaLemmaBackwards.app a ∘ yonedaLemmaForwards.app a)(x).app b f  ≅  x.app b f`

built as the composite:
  `(x.naturality (op f)).inv.app (𝟙 b₀)  ≫  (x.app b).map (ρ_ f).hom`

where `ρ_ f : f ≫ 𝟙 b₀ ≅ f` is the right unitor in `B`.
-/
def yonedaUnitAppIso (a : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat)) (b : Bᵒᵖ) (x : ↑(yonedaPairing.obj a))
    (f : ↑((yoneda₀ (unop a.1)).obj b)) :=
  (Iso.trans
    (Iso.symm (Iso.app (Cat.Hom.toNatIso (x.naturality (Quiver.Hom.op f))) (𝟙 (unop a.1))))
    ((x.app b).toFunctor.mapIso (rightUnitor f)))

set_option linter.flexible false in
/--
For a pair `a = (b₀, F)`, a component `b : Bᵒᵖ`, and a strong transformation
`x : yoneda₀ b₀ ⟶ F`, the natural transformation from the `b`-component of the roundtrip
`(yonedaLemmaBackwards ∘ yonedaLemmaForwards)(x)` back to the `b`-component of `x`.

Each component at `f : unop b ⟶ b₀` is `(yonedaUnitAppIso a b x f).hom`.

This is the innermost layer of the unit coherence; it is assembled into a full modification
by `yonedaHomInvIdNatIso` and then into the unit iso by `yonedaHomInvId`.
-/
def yonedaHomInvIdFunctorIso {a : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat)} (b : Bᵒᵖ) (x : ↑(yonedaPairing.obj a)) :
    (((yonedaLemmaBackwards.app a).toFunctor.obj
        ((yonedaLemmaForwards.app a).toFunctor.obj x)).app b).toFunctor ≅
    (x.app b).toFunctor := by
    refine NatIso.ofComponents (fun y ↦ yonedaUnitAppIso a b x y) ?_
    intro X Y h
    apply ((yonedaUnitAppIso a b x Y).comp_inv_eq.mp ?_).symm
    simp [yonedaUnitAppIso]
    have lem1 : (ρ_ X).hom ≫ h ≫ (ρ_ Y).inv = h ▷ (𝟙 (unop a.1)) :=
      Eq.symm (Bicategory.whiskerRight_id h)
    erw [← Category.assoc ((x.app b).toFunctor.map h), ← (x.app b).toFunctor.map_comp,
      Category.assoc, ← Category.assoc ((x.app b).toFunctor.map (ρ_ X).hom),
      ← (x.app b).toFunctor.map_comp, lem1]
    have hy'' := Cat.Hom₂.congr_app (x.naturality_naturality (op2 h)) (𝟙 (unop a.1))
    have lem2 : (Functor.whiskerRight ((yoneda₀ (unop a.1)).map₂ (op2 h)).toNatTrans
          (x.app b).toFunctor ≫ (x.naturality Y.op).hom.toNatTrans).app (𝟙 (unop a.1)) =
        (x.app b).toFunctor.map (h ▷ 𝟙 (unop a.1)) ≫
          (x.naturality Y.op).hom.toNatTrans.app (𝟙 (unop a.1)) :=
      eq_of_comp_right_eq fun {Z} ↦ congrFun rfl
    dsimp at hy''
    erw [← lem2, hy'', ← NatTrans.comp_app, ← Category.assoc, ← Cat.Hom.toNatTrans_comp,
      (x.naturality X.op).inv_hom_id, ← Cat.Hom.toNatTrans_comp, Category.id_comp]
    simp [yonedaLemmaBackwards, yonedaLemmaForwards]

/--
At a fixed pair `a = (b₀, F)` and a strong transformation `x : yoneda₀ b₀ ⟶ F`, the
isomorphism
  `(yonedaLemmaForwards.app a ≫ yonedaLemmaBackwards.app a).toFunctor.obj x ≅ x`
in `yonedaPairing.obj a`.

This is the component of the unit natural isomorphism `yonedaHomInvIdNatIso` at the object
`x`, assembled by applying `yonedaHomInvIdFunctorIso` at each component `b : Bᵒᵖ`.
-/
def yonedaHomInvIdObjIso (a : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat)) (x : ↑(yonedaPairing.obj a)) :
    (yonedaLemmaForwards.app a ≫ yonedaLemmaBackwards.app a).toFunctor.obj x ≅
    (𝟭 ↑(yonedaPairing.obj a)).obj x := by
    refine StrongTrans.isoMk (fun b ↦ (Cat.Hom.isoMk (yonedaHomInvIdFunctorIso b x))) ?_
    intro q r f
    refine Cat.Hom₂.ext_iff.mpr ?_
    ext s
    simp at s x
    simp[Functor.whiskerLeft,CategoryStruct.comp,NatTrans.vcomp]
    simp [yonedaLemmaBackwards,yonedaLemmaForwards,yonedaHomInvIdFunctorIso, yonedaUnitAppIso]
    sorry

set_option linter.flexible false in
/--
For a pair `a = (b₀, F)`, the modification
`(yonedaLemmaForwards.app a ≫ yonedaLemmaBackwards.app a)(x) ⟶ x`
in `yonedaPairing.obj a`, for each `x : yonedaPairing.obj a`.

This is the component of the unit morphism `yonedaHomInvId.hom` at the object `a`, assembled
component-wise using `yonedaHomInvIdObjIso` for each `b : Bᵒᵖ`.
-/
def yonedaHomInvIdNatIso (a : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat)) :
    (yonedaLemmaForwards.app a ≫ yonedaLemmaBackwards.app a).toFunctor ≅
    (𝟭 ↑(yonedaPairing.obj a)) := by
  refine NatIso.ofComponents (fun x ↦ yonedaHomInvIdObjIso a x) ?_
  intro X Y f
  have rw1 : (fun x ↦ yonedaHomInvIdObjIso a x) X = yonedaHomInvIdObjIso a X := rfl
  have rw2 : (fun x ↦ yonedaHomInvIdObjIso a x) Y = yonedaHomInvIdObjIso a Y := rfl
  have rw3 : (yonedaLemmaForwards.app a ≫ yonedaLemmaBackwards.app a).toFunctor.map f =
      (yonedaLemmaBackwards.app a).toFunctor.map ((yonedaLemmaForwards.app a).toFunctor.map f) :=
    rfl
  erw [rw1, rw2, rw3]
  clear rw1 rw2 rw3
  apply homCategory.ext
  intro b
  ext x
  have res : (X.naturality (Quiver.Hom.op x)).inv ≫
        (yoneda₀ (unop a.1)).map (Quiver.Hom.op x) ◁ f.as.app (op (unop b)) =
      f.as.app (op (unop a.1)) ▷ a.2.map (Quiver.Hom.op x) ≫
        (Y.naturality (Quiver.Hom.op x)).inv := by
    apply (Iso.eq_comp_inv (Y.naturality (Quiver.Hom.op x))).mpr
    rw [Category.assoc]
    apply (Iso.inv_comp_eq (X.naturality (Quiver.Hom.op x))).mpr
    exact f.as.naturality (Quiver.Hom.op x)
  have res2 := congrArg (fun nt ↦ nt.toNatTrans.app (𝟙 (unop a.1))) res
  dsimp at res2
  erw [NatTrans.comp_app]
  simp [yonedaLemmaBackwards, yonedaLemmaForwards, yonedaHomInvIdObjIso,
    yonedaHomInvIdFunctorIso, yonedaEvaluation', isoMk, NatIso.ofComponents,
    NatTrans.toCatHom₂]
  erw [NatTrans.comp_app]
  simp [catLiftEquiv, yonedaUnitAppIso, ULiftHom.equiv]
  erw [← Category.assoc, ← res2]
  simp

/--
The *unit isomorphism* `yonedaLemmaForwards ≫ yonedaLemmaBackwards ≅ 𝟙 yonedaPairing`.

This witnesses that composing the "evaluate at identity" map with the Yoneda embedding returns
the original strong transformation, up to a canonical isomorphism.  It is the `homInvId` field
of `yonedaLemma`.
-/
def yonedaHomInvId : yonedaLemmaForwards ≫ yonedaLemmaBackwards ≅ 𝟙 (@yonedaPairing B _) := by
  refine StrongTrans.isoMk (fun a ↦ Cat.Hom.isoMk (yonedaHomInvIdNatIso a)) ?_
  intro a b f
  have rw1 : (fun a ↦ Cat.Hom.isoMk (yonedaHomInvIdNatIso a)) b =
      Cat.Hom.isoMk (yonedaHomInvIdNatIso b) := rfl
  have rw2 : (Cat.Hom.isoMk (yonedaHomInvIdNatIso b)).hom =
      NatTrans.toCatHom₂ ((yonedaHomInvIdNatIso b).hom) := rfl
  have rw3 : (fun a ↦ Cat.Hom.isoMk (yonedaHomInvIdNatIso a)) a =
      Cat.Hom.isoMk (yonedaHomInvIdNatIso a) := rfl
  erw [rw1, rw2, rw3]
  clear rw1 rw2 rw3
  refine Cat.Hom₂.ext_iff.mpr ?_
  sorry
  -- erw [Cat.Hom.toNatTrans_comp]
  -- dsimp only [yonedaHomInvIdNatIso, Bicategory.whiskerRight, Functor.whiskerRight,
  --   Bicategory.whiskerLeft, Functor.whiskerLeft]
  -- ext x
  -- simp [Functor.leftUnitor, Functor.rightUnitor, yonedaLemmaForwards, yonedaHomInvIdObjIso,
  --   Bicategory.associator, Functor.associator, yonedaPairing]

/--
At a fixed pair `a = (b₀, F)`, the natural isomorphism from the roundtrip functor
`(yonedaLemmaBackwards.app a ≫ yonedaLemmaForwards.app a)` to the identity on
`yonedaEvaluation.obj a`.

This is the component of the counit `yonedaInvHomId` at the object `a`, witnessing that
`yonedaLemmaForwards(yonedaLemmaBackwards(s)) ≅ s` for `s : F.obj b₀`.
-/
def yonedaInvHomIdNatIso (a : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat)) :
    (yonedaLemmaBackwards.app a ≫ yonedaLemmaForwards.app a).toFunctor ≅
    (𝟭 ↑(yonedaEvaluation.obj a)) := by
  refine NatIso.ofComponents ?_ ?_
  · intro ⟨x⟩
    dsimp [yonedaLemmaForwards, ULiftHom.objDown, yonedaLemmaBackwards, Quiver.Hom]
    let I1 := (Cat.Hom.toNatIso (a.2.mapId a.1)).app x
    exact ULiftHom.up.mapIso
      ((@ULift.upFunctor.{_, _, max (max u v) w} (↑(yonedaEvaluation'.obj a)) _).mapIso I1)
  · rintro ⟨x⟩ ⟨y⟩ ⟨f⟩
    dsimp [yonedaLemmaForwards, ULiftHom.up]
    have h := (a.2.mapId a.1).hom.toNatTrans.naturality f
    dsimp at h
    exact Quiver.homOfEq_injective rfl rfl (congrArg (ULiftHom.up.map) h)

/--
The *counit isomorphism* `yonedaLemmaBackwards ≫ yonedaLemmaForwards ≅ 𝟙 yonedaEvaluation`.

This witnesses that composing the Yoneda embedding with "evaluate at identity" returns the
original element of `F.obj b`, up to a canonical isomorphism.  It is the `invHomId` field
of `yonedaLemma`.
-/
def yonedaInvHomId : yonedaLemmaBackwards ≫ yonedaLemmaForwards ≅ 𝟙 (@yonedaEvaluation B _) := by
  refine StrongTrans.isoMk (fun a ↦ Cat.Hom.isoMk (yonedaInvHomIdNatIso a)) ?_
  sorry

/--
The *bicategorical Yoneda lemma*: an internal equivalence in the bicategory of pseudofunctors

  `yonedaPairing  ≃  yonedaEvaluation`

which unpacks to the natural equivalence of categories

  `StrongTrans (yoneda₀ b) F  ≃  F.obj b`

for all `b : Bᵒᵖ` and `F : Bᵒᵖ ⥤ᵖ Cat`.

The equivalence is witnessed by:
* `map` (`yonedaLemmaForwards`): evaluate a strong transformation at the identity morphism.
* `inv` (`yonedaLemmaBackwards`): send an element `s : F.obj b` to the strong transformation
  `(a, f) ↦ (F.map f).obj s`.
* `homInvId` (`yonedaHomInvId`): the unit iso, `backwards ∘ forwards ≅ id` on the pairing side.
* `invHomId` (`yonedaInvHomId`): the counit iso, `forwards ∘ backwards ≅ id` on evaluation.
-/
def yonedaLemma : BiEquiv (@yonedaPairing B _) (@yonedaEvaluation B _) where
  map := yonedaLemmaForwards
  inv := yonedaLemmaBackwards
  homInvId := yonedaHomInvId
  invHomId := yonedaInvHomId
