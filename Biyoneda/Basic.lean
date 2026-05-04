import Mathlib.CategoryTheory.Bicategory.Product
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Bicategory.Yoneda
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.Tactic.CategoryTheory.Bicategory.Basic

/-
Sorry Count : 22
-/

open CategoryTheory Bicategory Bicategory.Opposite Opposite Pseudofunctor StrongTrans Functor
open scoped Pseudofunctor.StrongTrans

universe u v w v₁ v₂ u₁ u₂

instance catPseudoULiftObjCategory (C : Type u₁) [Category.{v₁} C] :
    Category.{max v₁ v₂} (ULiftHom.{v₂} (ULift.{u₂, u₁} C)) := by
  letI : Category (ULift.{u₂, u₁} C) := uliftCategory C
  exact ULiftHom.category (C := ULift.{u₂, u₁} C)

/--
`CatLift` is the inclusion functor from `Cat` in a smaller universe to a larger one.
It sends a category to its `ULift`/`ULiftHom`-lifted version.
-/
def CatLift : Cat.{v₁, u₁} ⥤ Cat.{max v₁ v₂, max u₁ u₂} where
  obj C := Cat.of (ULiftHom.{v₂} (ULift.{u₂, u₁} C.α))
  map {C D} F := by
    refine Functor.toCatHom ?_
    apply ULiftHomULiftCategory.equivCongrLeft.toFun
    letI : Category (ULift.{u₂, u₁} C) := uliftCategory C
    exact ULiftHom.down ⋙ ULift.downFunctor ⋙ F.toFunctor

/--
`CatLiftIso` exhibits a category as equivalent to its image under `CatLift`.
Uses the `ULift` and `ULiftHom` equivalences to build the equivalence.
-/
def CatLiftIso (C : Type u₁) [Category.{v₁} C] :
    Equivalence C (CatLift.{v₁, v₂, u₁, u₂}.obj (Cat.of C)) := by
  let E1 := @ULift.equivalence.{v₁, u₁, u₂} C _
  letI : Category (ULift.{u₂, u₁} C) := uliftCategory C
  exact E1.trans ULiftHom.equiv


/--
`CatPseudoULift` lifts `Cat` across universes as a pseudofunctor.
This is the bicategorical version of `CatLift` with coherence data.
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
    simp
    congr
  map₂_whisker_left { a b c } f g h η := by
    congr 1
    ext x
    rcases x with ⟨x⟩
    simp
    dsimp [CategoryStruct.comp,Category.comp_id,Functor.id_comp]
    simp [toCatHom,CatLift,ULiftHomULiftCategory.equivCongrLeft,ULift.upFunctor,ULiftHom.objDown,ULiftHom.objUp]
    sorry
  map₂_whisker_right η h:= by
    simp [Bicategory.whiskerRight,NatTrans.toCatHom₂,NatTrans.id,Category.id_comp]
    sorry
  map₂_associator f g h := by sorry
  map₂_left_unitor := sorry
  map₂_right_unitor := sorry

variable {B : Type u} [Bicategory.{w, v} B]

/--
Extensionality for modifications: equality of `as` components suffices.
Useful for `simp`-friendly proof steps when unfolding modifications.
-/
lemma Modification.extHelp {X : Type u₁} {Y : Type u₂} [Bicategory.{w₁, v₁} X] [Bicategory.{w₂, v₂} Y] {F G : X ⥤ᵖ Y} {η θ : F ⟶ G} {m1 m2 : η ⟶ θ} (h : m1.as = m2.as) : m1 = m2 := by
  cases m1
  cases m2
  congr

/--
`yonedaPairing` is a pseudofunctor sending `(b, F)` to strong transforms
from the Yoneda embedding at `b` to `F`.
-/
def yonedaPairing : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v}) ⥤ᵖ Cat.{max u (max v w), max u (max v w)} where
  obj x := @Cat.of (Pseudofunctor.StrongTrans (yoneda₀ x.fst.unop) x.snd) (Pseudofunctor.StrongTrans.homCategory)
  map {x y} f := by
    apply Functor.toCatHom { obj η := Bicategory.postcomp₂ f.1.unop ≫ (η ≫ f.2), map m := StrongTrans.whiskerLeft (Bicategory.postcomp₂ f.1.unop) (StrongTrans.whiskerRight m f.2) }
  map₂ { x y f g } η := by
    fconstructor
    fconstructor
    · intro a
      let ηa : postcomp₂ f.1.unop ≫ a ≫ f.2 ⟶ postcomp₂ f.1.unop ≫ a ≫ g.2 := (postcomp₂ f.1.unop ◁ (a ◁ η.2))
      let γ := (postcomposing₂ y.1.unop x.1.unop ).map (Hom2.unop2 η.1) ▷ (a ≫ g.2)
      exact ηa ≫ γ
    · intros X Y h
      apply Modification.extHelp
      ext t u
      dsimp[StrongTrans.whiskerLeft,postcomp₂,postcomp,Bicategory.whiskerLeft,postcomposing₂,Bicategory.whiskerRight,StrongTrans.whiskerRight,CategoryStruct.comp]
      congr 4
      dsimp [CategoryStruct.comp]
      sorry
  mapId x := by sorry
    -- fconstructor
    -- · fconstructor
    --   fconstructor
    --   · intro X
    --     fconstructor
    --     · simp
  mapComp f g := sorry
  map₂_id {a b} X := by
    ext x
    simp
    exact Category.id_comp (𝟙 ((postcomposing₂ (unop b.1) (unop a.1)).obj X.1.unop ≫ x ≫ X.2))

/--
`yonedaEvaluation'` evaluates a pair `(b, F)` to the category `F.obj b`.
This is the universe-unlifted evaluation pseudofunctor.
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
`yonedaEvaluation` is `yonedaEvaluation'` composed with `CatPseudoULift`.
This matches the universe levels of `yonedaPairing`.
-/
def yonedaEvaluation : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v}) ⥤ᵖ Cat.{max u (max v w), max u (max v w)} := by
  refine (Pseudofunctor.comp yonedaEvaluation' CatPseudoULift)

/--
The forward functor on objects for the Yoneda lemma, at a fixed pair `x`.
Sends a strong transformation to its component at `𝟙 (unop x.1)`.
-/
def yonedaLemmaForwardsFunctor (x : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat)) : (yonedaPairing.obj x) ⥤ (yonedaEvaluation.obj x) where
  obj pair := by
    fconstructor
    exact (pair.app x.1).toFunctor.obj (𝟙 (unop x.1))
  map {a b} f := by
    fconstructor
    exact (f.as.app x.1).toNatTrans.app (𝟙 (unop x.1))

/--
The forward strong transformation for the Yoneda lemma, from pairing to evaluation.
This packages `yonedaLemmaForwardsFunctor` as a strong transformation.
-/
def yonedaLemmaForwards : StrongTrans (@yonedaPairing B _) (@yonedaEvaluation B _) where
  app x := by
    fconstructor
    exact yonedaLemmaForwardsFunctor x
  naturality {a b} f := by sorry

/--
For fixed `x` and `eval`, build a functor `yoneda₀` at `a` into `x.2.obj a`.
This is the object-level data for the backward direction of Yoneda.
-/
def yonedaLemmaBackwardsFunctorObjFunctor (x : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat)) (eval : (yonedaEvaluation.obj x)) (a : Bᵒᵖ) : ↑((yoneda₀ (unop x.1)).obj a) ⥤ ↑(x.2.obj a) where
  obj b := by
    refine (x.2.map (Quiver.Hom.op b)).toFunctor.obj ?_
    rcases eval with ⟨eval⟩
    exact eval
  map { X Y } f := by
    rcases eval with ⟨eval⟩
    exact (x.2.map₂ (op2 f)).toNatTrans.app (eval)
  map_id x := by sorry
  map_comp f g := by sorry

#check NatIso.cancel_natIso_hom_left
#check NatIso.isIso_app_of_isIso

/--
Assemble the object-level backward data into a strong transformation at `x`.
Each component uses `yonedaLemmaBackwardsFunctorObjFunctor`.
-/
def yonedaLemmaBackwardsFunctorObj (x : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat)) (eval : (yonedaEvaluation.obj x)) : (yonedaPairing.obj x) where
  app a := {toFunctor := yonedaLemmaBackwardsFunctorObjFunctor x eval a}
  naturality {a b} f := by
    rcases eval with ⟨eval⟩
    fconstructor
    · fconstructor
      fconstructor
      · exact fun X => (x.2.mapComp (Quiver.Hom.op X) (f)).hom.toNatTrans.app eval
      · intro X Y g
        simp [yonedaLemmaBackwardsFunctorObjFunctor]
        congr 1
        set f1 := (x.2.mapComp (Quiver.Hom.op Y) f).inv.toNatTrans.app eval
        set f2 := (x.2.mapComp (Quiver.Hom.op Y) f).hom.toNatTrans.app eval
        let lem : f1 ≫ f2 = ((x.2.mapComp (Quiver.Hom.op Y) f).inv ≫ (x.2.mapComp (Quiver.Hom.op Y) f).hom).toNatTrans.app eval := by
          exact Eq.symm (Cat.Hom₂.comp_app (x.2.mapComp (Quiver.Hom.op Y) f).inv (x.2.mapComp (Quiver.Hom.op Y) f).hom eval)
        simp at lem
        simp [lem]
    · fconstructor
      fconstructor
      · exact fun X => (x.2.mapComp (Quiver.Hom.op X) (f)).inv.toNatTrans.app eval
      · intro X Y g
        simp [yonedaLemmaBackwardsFunctorObjFunctor, <- Category.assoc]
        set f1 := ((x.2.mapComp (Quiver.Hom.op X) f).inv.toNatTrans.app eval)
        set f2 := ((x.2.mapComp (Quiver.Hom.op X) f).hom.toNatTrans.app eval)
        let lem : f1 ≫ f2 = ((x.2.mapComp (Quiver.Hom.op X) f).inv ≫ (x.2.mapComp (Quiver.Hom.op X) f).hom).toNatTrans.app eval := by
          exact Eq.symm (Cat.Hom₂.comp_app (x.2.mapComp (Quiver.Hom.op X) f).inv (x.2.mapComp (Quiver.Hom.op X) f).hom eval)
        simp at lem
        simp [lem]
    · ext X
      set f1 := (x.2.mapComp (Quiver.Hom.op X) f).hom.toNatTrans.app eval
      set f2 := (x.2.mapComp (Quiver.Hom.op X) f).inv.toNatTrans.app eval
      have key : f1 ≫ f2 = ((x.2.mapComp (Quiver.Hom.op X) f).hom ≫ (x.2.mapComp (Quiver.Hom.op X) f).inv).toNatTrans.app eval :=
        Eq.symm (Cat.Hom₂.comp_app _ _ eval)
      simp at key
      simp [key]
      sorry
    · ext X
      set f1 := (x.2.mapComp (Quiver.Hom.op X) f).inv.toNatTrans.app eval
      set f2 := (x.2.mapComp (Quiver.Hom.op X) f).hom.toNatTrans.app eval
      have key : f1 ≫ f2 = ((x.2.mapComp (Quiver.Hom.op X) f).inv ≫ (x.2.mapComp (Quiver.Hom.op X) f).hom).toNatTrans.app eval :=
        Eq.symm (Cat.Hom₂.comp_app _ _ eval)
      simp at key
      simp [key]
      sorry

/--
The backward functor on objects for the Yoneda lemma, at a fixed pair `x`.
It turns evaluation objects into strong transformations in the pairing.
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
      sorry

/--
The backward strong transformation for the Yoneda lemma, from evaluation to pairing.
This packages `yonedaLemmaBackwardsFunctor` as a strong transformation.
-/
def yonedaLemmaBackwards : StrongTrans (@yonedaEvaluation B _)  (@yonedaPairing B _) where
  app x := by
    fconstructor
    exact yonedaLemmaBackwardsFunctor x
  naturality f := by
    sorry

/--
`BiEquiv` is the data of a bicategorical equivalence between objects of `B`.
It consists of a pair of 1-morphisms and the unit/counit isomorphisms.
-/
structure BiEquiv (x y : B) where
  map : x ⟶ y
  inv : y ⟶ x
  homInvId : map ≫ inv ≅ 𝟙 x
  invHomId : inv ≫ map ≅ 𝟙 y

def yonedahomInvId : yonedaLemmaForwards ≫ yonedaLemmaBackwards ≅ 𝟙 (@yonedaPairing B _) where
  hom := by sorry
  inv := by sorry

def yonedainvHomId : yonedaLemmaBackwards ≫ yonedaLemmaForwards ≅ 𝟙 (@yonedaEvaluation B _)  where
  hom := by sorry
  inv := by sorry

/--
The Yoneda lemma as a bicategorical equivalence between pairing and evaluation.
Combines the forward and backward strong transformations with coherence isos.
-/
def yonedaLemma : BiEquiv (@yonedaPairing B _) (@yonedaEvaluation B _) where
  map := yonedaLemmaForwards
  inv := yonedaLemmaBackwards
  homInvId := yonedahomInvId
  invHomId := yonedainvHomId
