import Mathlib.CategoryTheory.Bicategory.Product
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Bicategory.Yoneda
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.Tactic.CategoryTheory.Bicategory.Basic

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
`Cat.{max u (max v w), max u (max v w)}`.  The auxiliary pseudofunctor `CatPseudoULift` is
used to promote `yonedaEvaluation'` to the correct universe level, yielding `yonedaEvaluation`.
-/

open CategoryTheory Bicategory Bicategory.Opposite Opposite Pseudofunctor StrongTrans Functor
open scoped Pseudofunctor.StrongTrans

universe u v w v₁ v₂ u₁ u₂

/--
The `Category` instance on `ULiftHom.{v₂} (ULift.{u₂} C)`, which simultaneously lifts the
object universe from `u₁` to `max u₁ u₂` and the morphism universe from `v₁` to `max v₁ v₂`.

This is the category structure that `CatLift` produces on objects; it is assembled by first
applying `uliftCategory` to get a `Category (ULift C)` and then `ULiftHom.category`.
-/
instance catPseudoULiftObjCategory (C : Type u₁) [Category.{v₁} C] :
    Category.{max v₁ v₂} (ULiftHom.{v₂} (ULift.{u₂, u₁} C)) := by
  letI : Category (ULift.{u₂, u₁} C) := uliftCategory C
  exact ULiftHom.category (C := ULift.{u₂, u₁} C)

/--
The strict 1-functor `Cat.{v₁, u₁} ⥤ Cat.{max v₁ v₂, max u₁ u₂}` that promotes a small
category to a larger universe.

* **On objects**: `C ↦ ULiftHom (ULift C)`, lifting both the object type and the hom-sets.
* **On 1-morphisms**: given `F : C ⥤ D`, the lifted functor sends `⟨⟨x⟩⟩ ↦ ⟨F x⟩` and maps
  morphisms via `ULiftHom.up ∘ F.map ∘ ULiftHom.down`.

Because `ULift` and `ULiftHom` are both strictly functorial, no coherence isos are needed.
The pseudofunctor extension (with trivial coherence isos) is `CatPseudoULift`.
-/
def CatLift : Cat.{v₁, u₁} ⥤ Cat.{max v₁ v₂, max u₁ u₂} where
  obj C := Cat.of (ULiftHom.{v₂} (ULift.{u₂, u₁} C.α))
  map {C D} F := by
    refine Functor.toCatHom ?_
    apply ULiftHomULiftCategory.equivCongrLeft.toFun
    letI : Category (ULift.{u₂, u₁} C) := uliftCategory C
    exact ULiftHom.down ⋙ ULift.downFunctor ⋙ F.toFunctor

/--
The equivalence of categories `C ≃ CatLift.obj (Cat.of C)`.

This witnesses that universe-lifting is lossless: the original category `C` is equivalent to
its image under `CatLift`, via the composite equivalence
  `C  ≃  ULift C  ≃  ULiftHom (ULift C)`
built from `ULift.equivalence` and `ULiftHom.equiv`.

Used in `yonedaLemmaBackwardsFunctor` to lower morphisms through the universe lift.
-/
def CatLiftIso (C : Type u₁) [Category.{v₁} C] :
    Equivalence C (CatLift.{v₁, v₂, u₁, u₂}.obj (Cat.of C)) := by
  let uLiftEquiv := @ULift.equivalence.{v₁, u₁, u₂} C _
  letI : Category (ULift.{u₂, u₁} C) := uliftCategory C
  exact uLiftEquiv.trans ULiftHom.equiv

/--
The pseudofunctor `Cat.{v₁, u₁} ⥤ᵖ Cat.{max v₁ v₂, max u₁ u₂}` that promotes every small
category to a larger universe.

* **On objects and 1-morphisms**: agrees with the strict functor `CatLift`.
* **On 2-morphisms**: a natural transformation `η : F ⟶ G` is lifted by applying `ULiftHom.up`
  component-wise.
* **Coherence isos** (`mapId`, `mapComp`): both are `Iso.refl`, since `CatLift` is strictly
  functorial and requires no non-trivial coherence.

This pseudofunctor is used to bring `yonedaEvaluation'` (which lands in `Cat.{w, v}`) up to
the universe `Cat.{max u (max v w), max u (max v w)}` required by `yonedaPairing`.
-/
def CatPseudoULift : Cat.{v₁, u₁} ⥤ᵖ Cat.{max v₁ v₂, max u₁ u₂} where
  obj C := CatLift.obj C
  map {C D} F := CatLift.map F
  map₂ { C D } f { g } { η } := by
    fconstructor
    fconstructor
    · intro x
      unfold CatLift ULiftHom at x
      let ηapp := (ULiftHom.up.map (η.toNatTrans.app x.down))
      exact ηapp
    · intros X Y h
      rcases X with ⟨X⟩
      rcases Y with ⟨Y⟩
      apply (Quiver.homOfEq_injective rfl rfl (congrArg (ULiftHom.up.map) (η.toNatTrans.naturality h.down)))
  mapId C := Iso.refl (CatLift.map (𝟙 C))
  mapComp F G := Iso.refl (CatLift.map (F ≫ G))
  map₂_id f := by
    congr
  map₂_whisker_left { a b c } f g h η := by
    congr
    ext x
    rcases x with ⟨x⟩
    simp
    dsimp [CategoryStruct.comp,Category.comp_id,Functor.id_comp]
    simp [toCatHom,CatLift,ULiftHomULiftCategory.equivCongrLeft,ULift.upFunctor,ULiftHom.objDown,ULiftHom.objUp]
    erw [Category.id_comp,Category.comp_id]
  map₂_whisker_right η h:= by
    congr
    ext x
    rcases x with ⟨x⟩
    simp only [Cat.Hom.comp_toFunctor, comp_obj, ULiftHom.up_obj, Cat.whiskerRight_toNatTrans, whiskerRight_app,
    Cat.coe_of, Iso.refl_hom, Cat.Hom.toNatTrans_id, NatTrans.id_app, Iso.refl_inv, Cat.Hom.toNatTrans_comp,
    NatTrans.comp_app]
    dsimp only [CategoryStruct.comp]
    simp only [ULiftHom.objUp, CatLift, ULiftHomULiftCategory.equivCongrLeft, ULift.upFunctor, Equiv.toFun_as_coe,
    Equiv.coe_fn_mk, toCatHom, Cat.of_α, Cat.coe_of, comp_obj, ULiftHom.down_obj, ULiftHom.objDown,
    ULift.downFunctor_obj, ULiftHom.up_obj, Functor.comp_map, ULiftHom.down_map, ULiftHom.up_map_down,
    ULift.downFunctor_map]
    erw [Category.id_comp,Category.comp_id]
    rfl
  map₂_associator f g h := by
    ext ⟨x⟩
    simp [Functor.map_id,toCatHom,CatLift,ULiftHomULiftCategory.equivCongrLeft,ULift.upFunctor,ULiftHom.objDown,ULiftHom.objUp]
    sorry
  map₂_left_unitor f := by
    ext ⟨x⟩
    simp [Functor.map_id,toCatHom,CatLift,ULiftHomULiftCategory.equivCongrLeft,ULift.upFunctor,ULiftHom.objDown,ULiftHom.objUp]
    sorry
  map₂_right_unitor f := by
    ext ⟨x⟩
    simp [Functor.map_id,toCatHom,CatLift,ULiftHomULiftCategory.equivCongrLeft,ULift.upFunctor,ULiftHom.objDown,ULiftHom.objUp]
    sorry

variable {B : Type u} [Bicategory.{w, v} B]

/--
To prove two morphisms `m1 m2 : η ⟶ θ` in the hom-category of strong transformations are
equal, it suffices to show their underlying modifications agree: `m1.as = m2.as`.

In the `Pseudofunctor.StrongTrans` bicategory, a 2-morphism `η ⟶ θ` is a `StrongTrans.Hom`,
a one-field structure wrapping a `Modification`.  This lemma peels off that wrapper.
-/
lemma Modification.extHelp {X : Type u₁} {Y : Type u₂} [Bicategory.{w₁, v₁} X] [Bicategory.{w₂, v₂} Y] {F G : X ⥤ᵖ Y} {η θ : F ⟶ G} {m1 m2 : η ⟶ θ} (h : m1.as = m2.as) : m1 = m2 := by
  cases m1
  cases m2
  congr

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
    apply Functor.toCatHom { obj η := Bicategory.postcomp₂ f.1.unop ≫ (η ≫ f.2), map m := StrongTrans.whiskerLeft (Bicategory.postcomp₂ f.1.unop) (StrongTrans.whiskerRight m f.2)}
  map₂ { x y f g } η := by
    fconstructor
    fconstructor
    · intro a
      -- left-whisker the 2-cell component of η with the current strong transformation
      let leftWhiskerComp : postcomp₂ f.1.unop ≫ a ≫ f.2 ⟶ postcomp₂ f.1.unop ≫ a ≫ g.2 :=
        postcomp₂ f.1.unop ◁ (a ◁ η.2)
      -- right-whisker the image of the 1-cell component of η under postcomposing₂
      let rightWhiskerComp := (postcomposing₂ y.1.unop x.1.unop).map (Hom2.unop2 η.1) ▷ (a ≫ g.2)
      exact leftWhiskerComp ≫ rightWhiskerComp
    · intros X Y h
      apply Modification.extHelp
      ext t u
      dsimp[StrongTrans.whiskerLeft,postcomp₂,postcomp,Bicategory.whiskerLeft,postcomposing₂,Bicategory.whiskerRight,StrongTrans.whiskerRight,CategoryStruct.comp]
      congr 4
      dsimp [CategoryStruct.comp]
      sorry
  mapId x := by sorry
  mapComp f g := sorry
  map₂_id {a b} X := by
    ext x
    simp
    exact Category.id_comp (𝟙 ((postcomposing₂ (unop b.1) (unop a.1)).obj X.1.unop ≫ x ≫ X.2))

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
(which post-composes with `CatPseudoULift`) for the universe-matched version.
-/
def yonedaEvaluation' : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v}) ⥤ᵖ Cat.{w, v} where
  obj x := x.snd.obj x.fst
  map {x y} f := f.2.app x.1 ≫ (y.2.map f.1)
  map₂ { x y f g } η := (η.2.as.app x.1 ▷ y.2.map f.1) ≫ (_ ◁ y.2.map₂ η.1)
  mapId x := (_root_.id (x.2.mapId x.1))
  mapComp {a b c} f g := by
    refine Iso.trans (α_ (f.2.app a.1) (g.2.app a.1) (c.2.map (f.1 ≫ g.1))) (Iso.trans ?_ (α_ (f.2.app a.1) (b.2.map f.1) (g.2.app b.1 ≫ c.2.map g.1)).symm)
    · fconstructor
      · refine (f.2.app a.1) ◁ ((g.2.app a.1 ◁ (c.2.mapComp f.1 g.1).hom) ≫ ?_)
        refine (associator (g.2.app a.1) (c.2.map f.1) (c.2.map g.1)).inv ≫ ?_ ≫ (associator (b.2.map f.1) (g.2.app b.1) (c.2.map g.1)).hom
        exact (g.2.naturality f.1).inv ▷ (c.2.map g.1)
      · refine (f.2.app a.1) ◁ (?_ ≫ (g.2.app a.1 ◁ (c.2.mapComp f.1 g.1).inv))
        refine  (associator (b.2.map f.1) (g.2.app b.1) (c.2.map g.1)).inv ≫ ?_ ≫ (associator (g.2.app a.1) (c.2.map f.1) (c.2.map g.1)).hom
        exact (g.2.naturality f.1).hom ▷ (c.2.map g.1)
      · simp
      · simp
  map₂_whisker_left {a b c} f { g h } { η }:= by
    simp
    bicategory
    sorry
  map₂_whisker_right := by sorry
  map₂_associator := by sorry
  map₂_left_unitor a := by sorry
  map₂_right_unitor := by sorry

/--
The *evaluation pseudofunctor* at the correct universe level,
`Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat) ⥤ᵖ Cat.{max u (max v w), max u (max v w)}`.

Defined as the composite `yonedaEvaluation' ⋙ CatPseudoULift`, which promotes the smaller
pseudofunctor `yonedaEvaluation'` (landing in `Cat.{w, v}`) to match the universe of
`yonedaPairing`.
-/
def yonedaEvaluation : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v}) ⥤ᵖ Cat.{max u (max v w), max u (max v w)} := by
  refine (Pseudofunctor.comp yonedaEvaluation' CatPseudoULift)

/--
At a fixed pair `x = (b, F)`, the *evaluate-at-identity functor*
`StrongTrans (yoneda₀ b) F ⥤ F.obj b`.

This is the core of the Yoneda equivalence at the level of individual categories:
* **On objects**: a strong transformation `η : yoneda₀ b ⟶ F` maps to
  `η.app b (𝟙 b) : F.obj b` — apply the component at `b`, then evaluate at `𝟙 b`.
* **On morphisms**: a modification `m : η ⟶ θ` maps to
  `m.as.app b (𝟙 b) : η.app b (𝟙 b) ⟶ θ.app b (𝟙 b)`.
-/
def yonedaLemmaForwardsFunctor (x : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat)) : (yonedaPairing.obj x) ⥤ (yonedaEvaluation.obj x) where
  obj pair := by
    fconstructor
    exact (pair.app x.1).toFunctor.obj (𝟙 (unop x.1))
  map {a b} f := by
    fconstructor
    exact (f.as.app x.1).toNatTrans.app (𝟙 (unop x.1))

/--
The *forward strong transformation* `yonedaPairing ⟶ yonedaEvaluation` for the Yoneda lemma.

At each pair `x = (b, F)`, the component functor is `yonedaLemmaForwardsFunctor x`, which
sends a strong transformation `η : yoneda₀ b ⟶ F` to the element `η.app b (𝟙 b) : F.obj b`.

Mathematically, this is the "evaluate at identity" direction of the equivalence
  `StrongTrans(yoneda₀ b, F)  ≃  F.obj b`.
-/
def yonedaLemmaForwards : StrongTrans (@yonedaPairing B _) (@yonedaEvaluation B _) where
  app x := by
    fconstructor
    exact yonedaLemmaForwardsFunctor x
  naturality {a b} f := by sorry

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
def yonedaLemmaBackwardsFunctorObjFunctor (x : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat)) (eval : (yonedaEvaluation.obj x)) (a : Bᵒᵖ) : ↑((yoneda₀ (unop x.1)).obj a) ⥤ ↑(x.2.obj a) where
  obj b := by
    refine (x.2.map (Quiver.Hom.op b)).toFunctor.obj ?_
    rcases eval with ⟨eval⟩
    exact eval
  map { X Y } f := by
    rcases eval with ⟨eval⟩
    exact (x.2.map₂ (op2 f)).toNatTrans.app (eval)
  map_id _ := by cases eval; erw [op2_id, PrelaxFunctor.map₂_id]; rfl
  map_comp _ _ := by cases eval; erw [op2_comp, PrelaxFunctor.map₂_comp]; rfl

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
def yonedaLemmaBackwardsFunctorObj (x : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat))
  (eval : (yonedaEvaluation.obj x)) : (yonedaPairing.obj x) where
  app a := {toFunctor := yonedaLemmaBackwardsFunctorObjFunctor x eval a}
  naturality {a b} f := by
    rcases eval with ⟨eval⟩
    fconstructor
    · fconstructor
      fconstructor
      · exact fun X => (x.2.mapComp (Quiver.Hom.op X) (f)).hom.toNatTrans.app eval
      · intro X Y g
        simp only [yoneda₀_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj_α,
        yonedaLemmaBackwardsFunctorObjFunctor, op_unop, Cat.Hom.comp_toFunctor, comp_obj,
        yoneda₀_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map_toFunctor_obj, op_comp,
        Quiver.Hom.op_unop, Functor.comp_map,
        yoneda₀_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map_toFunctor_map,
        op2_whiskerLeft, map₂_whisker_right, Cat.Hom.toNatTrans_comp, Cat.whiskerRight_toNatTrans,
        NatTrans.comp_app, whiskerRight_app,
        Category.assoc]
        congr 1
        -- show inv ≫ hom = id by computing the composite using Cat.Hom₂.comp_app
        set mapCompInv_Y := (x.2.mapComp (Quiver.Hom.op Y) f).inv.toNatTrans.app eval
        set mapCompHom_Y := (x.2.mapComp (Quiver.Hom.op Y) f).hom.toNatTrans.app eval
        let invHomComp_Y : mapCompInv_Y ≫ mapCompHom_Y =
            ((x.2.mapComp (Quiver.Hom.op Y) f).inv ≫ (x.2.mapComp (Quiver.Hom.op Y) f).hom).toNatTrans.app eval :=
          Eq.symm (Cat.Hom₂.comp_app (x.2.mapComp (Quiver.Hom.op Y) f).inv (x.2.mapComp (Quiver.Hom.op Y) f).hom eval)
        simp at invHomComp_Y
        simp [invHomComp_Y]
    · fconstructor
      fconstructor
      · exact fun X => (x.2.mapComp (Quiver.Hom.op X) (f)).inv.toNatTrans.app eval
      · intro X Y g
        simp only [yoneda₀_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj_α,
        yonedaLemmaBackwardsFunctorObjFunctor, op_unop, Cat.Hom.comp_toFunctor, comp_obj,
        yoneda₀_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map_toFunctor_obj, op_comp,
        Quiver.Hom.op_unop, Functor.comp_map,
        yoneda₀_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map_toFunctor_map,
        op2_whiskerLeft, map₂_whisker_right, ← Category.assoc, Cat.Hom.toNatTrans_comp,
        Cat.whiskerRight_toNatTrans, NatTrans.comp_app, whiskerRight_app]
        -- same inv-hom cancellation, now at object X
        set mapCompInv_X := ((x.2.mapComp (Quiver.Hom.op X) f).inv.toNatTrans.app eval)
        set mapCompHom_X := ((x.2.mapComp (Quiver.Hom.op X) f).hom.toNatTrans.app eval)
        let invHomComp_X : mapCompInv_X ≫ mapCompHom_X =
            ((x.2.mapComp (Quiver.Hom.op X) f).inv ≫ (x.2.mapComp (Quiver.Hom.op X) f).hom).toNatTrans.app eval :=
          Eq.symm (Cat.Hom₂.comp_app (x.2.mapComp (Quiver.Hom.op X) f).inv (x.2.mapComp (Quiver.Hom.op X) f).hom eval)
        simp at invHomComp_X
        simp [invHomComp_X]
    · ext X
      simp only [yoneda₀_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj_α, yonedaLemmaBackwardsFunctorObjFunctor,
      op_unop, Cat.Hom.comp_toFunctor, comp_obj,
      yoneda₀_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map_toFunctor_obj, op_comp, Quiver.Hom.op_unop,
      Cat.Hom.toNatTrans_comp, Cat.Hom.toNatTrans_id]
      sorry
    · ext X
      -- the inv_hom_id of mapComp, specialised to the evaluation point via congrArg
      let mapCompInvHomId := (x.2.mapComp (Quiver.Hom.op X) f).inv_hom_id
      let mapCompInvHomId_app := congrArg (fun g => g.toNatTrans.app eval) mapCompInvHomId
      dsimp at mapCompInvHomId_app
      erw [NatTrans.vcomp_app, mapCompInvHomId_app]
      congr

/--
At a fixed pair `x = (b₀, F)`, the *Yoneda embedding functor*
`F.obj b₀ ⥤ StrongTrans (yoneda₀ b₀) F`.

* **On objects**: sends an element `eval : F.obj b₀` to the strong transformation
  `yonedaLemmaBackwardsFunctorObj x eval`, whose `a`-component sends
  `f : unop a ⟶ b₀` to `(F.map f).obj eval`.
* **On morphisms**: sends a morphism `g : eval ⟶ eval'` (lowered through `CatLiftIso`) to the
  modification whose `c`-component has, at each `X`, the morphism
  `(F.map (op X)).map ((CatLiftIso (F.obj b₀)).inverse.map g)`.

This is the component functor of the strong transformation `yonedaLemmaBackwards`.
-/
def yonedaLemmaBackwardsFunctor (x : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat)) : (yonedaEvaluation.obj x) ⥤ (yonedaPairing.obj x) where
  obj a := yonedaLemmaBackwardsFunctorObj x a
  map { a b } f := by
    rcases a with ⟨a⟩
    rcases b with ⟨b⟩
    fconstructor
    fconstructor
    · intro c
      fconstructor
      fconstructor
      · exact fun X => (x.2.map (Quiver.Hom.op X)).toFunctor.map ((CatLiftIso ↑(yonedaEvaluation'.obj x)).inverse.map f)
      · intro X Y g
        simp only [yoneda₀_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj_α, yonedaLemmaBackwardsFunctorObj, yonedaLemmaBackwardsFunctorObjFunctor, op_unop, Cat.Hom.comp_toFunctor, Cat.coe_of, NatTrans.naturality]
    · intro t u g
      refine Cat.Hom₂.ext_iff.mpr ?_
      ext c
      rw [Cat.Hom.toNatTrans_comp,Cat.Hom.toNatTrans_comp]
      simp
      sorry

/--
The *backward strong transformation* `yonedaEvaluation ⟶ yonedaPairing` for the Yoneda lemma.

At each pair `x = (b₀, F)`, the component functor is `yonedaLemmaBackwardsFunctor x`, the
Yoneda embedding functor sending `s : F.obj b₀` to the strong transformation
`(a, f) ↦ (F.map f).obj s`.

This is the inverse direction of the Yoneda equivalence.  Together with `yonedaLemmaForwards`
and the unit/counit isos (`yonedahomInvId`, `yonedainvHomId`), it forms `yonedaLemma`.
-/
def yonedaLemmaBackwards : StrongTrans (@yonedaEvaluation B _)  (@yonedaPairing B _) where
  app x := by
    exact {toFunctor := yonedaLemmaBackwardsFunctor x}
  naturality f := by
    sorry

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

/--
For a pair `a = (b₀, F)`, a component `b : Bᵒᵖ`, and a strong transformation
`x : yoneda₀ b₀ ⟶ F`, the natural transformation from the `b`-component of the roundtrip
`(yonedaLemmaBackwards ∘ yonedaLemmaForwards)(x)` back to the `b`-component of `x`.

Each component at `f : unop b ⟶ b₀` is `(yonedaUnitAppIso a b x f).hom`.

This is the innermost layer of the unit coherence; it is assembled into a full modification
by `yonedahomInvIdHomNatTrans` and then into the unit iso by `yonedahomInvId`.
-/
def yonedahomInvIdHomNatTransNatTrans (a : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat)) (b : Bᵒᵖ) (x : ↑(yonedaPairing.obj a))
  : NatTrans (((yonedaLemmaBackwards.app a).toFunctor.obj ((yonedaLemmaForwards.app a).toFunctor.obj x)).app b).toFunctor (x.app b).toFunctor where
  app y := (yonedaUnitAppIso a b x y).hom
  naturality {x y} f := by
    sorry

/--
For a pair `a = (b₀, F)`, the modification
`(yonedaLemmaForwards.app a ≫ yonedaLemmaBackwards.app a)(x) ⟶ x`
in `yonedaPairing.obj a`, for each `x : yonedaPairing.obj a`.

This is the component of the unit morphism `yonedahomInvId.hom` at the object `a`, assembled
component-wise using `yonedahomInvIdHomNatTransNatTrans` for each `b : Bᵒᵖ`.
-/
def yonedahomInvIdHomNatTrans (a : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat)) : NatTrans (yonedaLemmaForwards.app a ≫ yonedaLemmaBackwards.app a).toFunctor  (𝟭 ↑(yonedaPairing.obj a)) where
  app x := by
    refine {as := {app := ?_, naturality := ?_}}
    · intro a
      fconstructor
      apply yonedahomInvIdHomNatTransNatTrans
    · intro c d f
      sorry
  naturality {x y} f := by
    sorry

/--
The *unit isomorphism* `yonedaLemmaForwards ≫ yonedaLemmaBackwards ≅ 𝟙 yonedaPairing`.

This witnesses that composing the "evaluate at identity" map with the Yoneda embedding returns
the original strong transformation, up to a canonical isomorphism.  It is the `homInvId` field
of `yonedaLemma`.
-/
def yonedahomInvId : yonedaLemmaForwards ≫ yonedaLemmaBackwards ≅ 𝟙 (@yonedaPairing B _) where
  hom := by
    refine {as := {app := ?_, naturality := ?_}}
    · intro a
      fconstructor
      exact yonedahomInvIdHomNatTrans a
    · sorry
  inv := by sorry

/--
For a pair `a = (b₀, F)`, the natural transformation from the roundtrip functor
`(yonedaLemmaBackwards.app a ≫ yonedaLemmaForwards.app a)` to the identity on
`yonedaEvaluation.obj a`.

This is the component of the counit morphism `yonedainvHomId.hom` at the object `a`,
witnessing that `yonedaLemmaForwards(yonedaLemmaBackwards(s)) ≅ s` for `s : F.obj b₀`.
-/
def yonedaInvhomIdHomNatTrans (a : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat)) : NatTrans (yonedaLemmaBackwards.app a ≫ yonedaLemmaForwards.app a).toFunctor  (𝟭 ↑(yonedaEvaluation.obj a)) where
  app x := by
    fconstructor
    dsimp
    sorry
  naturality {x y} f := by
    sorry

/--
The *counit isomorphism* `yonedaLemmaBackwards ≫ yonedaLemmaForwards ≅ 𝟙 yonedaEvaluation`.

This witnesses that composing the Yoneda embedding with "evaluate at identity" returns the
original element of `F.obj b`, up to a canonical isomorphism.  It is the `invHomId` field
of `yonedaLemma`.
-/
def yonedainvHomId : yonedaLemmaBackwards ≫ yonedaLemmaForwards ≅ 𝟙 (@yonedaEvaluation B _)  where
  hom := by
    refine {as := {app := ?_, naturality := ?_}}
    · intro a
      fconstructor
      exact yonedaInvhomIdHomNatTrans a
    · sorry
  inv := by sorry

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
* `homInvId` (`yonedahomInvId`): the unit iso, `backwards ∘ forwards ≅ id` on the pairing side.
* `invHomId` (`yonedainvHomId`): the counit iso, `forwards ∘ backwards ≅ id` on evaluation.
-/
def yonedaLemma : BiEquiv (@yonedaPairing B _) (@yonedaEvaluation B _) where
  map := yonedaLemmaForwards
  inv := yonedaLemmaBackwards
  homInvId := yonedahomInvId
  invHomId := yonedainvHomId
