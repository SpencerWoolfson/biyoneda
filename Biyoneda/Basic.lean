import Mathlib.CategoryTheory.Bicategory.Product
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Bicategory.Yoneda
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.Tactic.CategoryTheory.Bicategory.Basic


open CategoryTheory Bicategory Bicategory.Opposite Opposite Pseudofunctor StrongTrans Functor
open scoped Pseudofunctor.StrongTrans

universe u v w v₁ v₂ u₁ u₂

instance catPsudoULiftObjCategory (C : Type u₁) [Category.{v₁} C] :
    Category.{max v₁ v₂} (ULiftHom.{v₂} (ULift.{u₂, u₁} C)) := by
  letI : Category (ULift.{u₂, u₁} C) := uliftCategory C
  exact ULiftHom.category (C := ULift.{u₂, u₁} C)

def CatLift : Cat.{v₁, u₁} ⥤ Cat.{max v₁ v₂, max u₁ u₂} where
  obj C := Cat.of (ULiftHom.{v₂} (ULift.{u₂, u₁} C.α))
  map {C D} F := by
    refine Functor.toCatHom ?_
    apply ULiftHomULiftCategory.equivCongrLeft.toFun
    letI : Category (ULift.{u₂, u₁} C) := uliftCategory C
    exact ULiftHom.down ⋙ ULift.downFunctor ⋙ F.toFunctor

def CatPsudoULift : Cat.{v₁, u₁} ⥤ᵖ Cat.{max v₁ v₂, max u₁ u₂} where
  obj C := CatLift.obj C
  map {C D} F := CatLift.map F
  map₂ { C D } f { g } { η } := by
    fconstructor
    fconstructor
    · intro x
      unfold CatLift ULiftHom at x
      dsimp at x
      let ηapp := (ULiftHom.up.map (η.toNatTrans.app x.down))
      exact ηapp
    · intros X Y h
      rcases X with ⟨X⟩
      rcases Y with ⟨Y⟩
      let h := congrArg (ULiftHom.up.map) (η.toNatTrans.naturality h.down)
      dsimp [CatLift, ULiftHomULiftCategory.equivCongrLeft]
      apply (Quiver.homOfEq_injective rfl rfl h)
  mapId C := Iso.refl (CatLift.map (𝟙 C))
  mapComp F G := Iso.refl (CatLift.map (F ≫ G))
  map₂_id f := by
    simp
    congr
  map₂_whisker_left {a b c} f g h η := by
    sorry
  map₂_whisker_right := sorry
  map₂_associator := sorry
  map₂_left_unitor := sorry
  map₂_right_unitor := sorry

variable {B : Type u} [Bicategory.{w, v} B]

lemma Modification.extHelp {X : Type u₁} {Y : Type u₂} [Bicategory.{w₁, v₁} X] [Bicategory.{w₂, v₂} Y] {F G : X ⥤ᵖ Y} {η θ : F ⟶ G} {m1 m2 : η ⟶ θ} (h : m1.as = m2.as) : m1 = m2 := by
  cases m1
  cases m2
  congr

-- set_option trace.Meta.synthInstance true
def yonedaPairing : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v}) ⥤ᵖ Cat.{max u (max v w), max u (max v w)} where
  obj x := @Cat.of (Pseudofunctor.StrongTrans (yoneda₀ x.fst.unop) x.snd) (Pseudofunctor.StrongTrans.homCategory)
  map {x y} f := by
    apply Functor.toCatHom { obj η := Bicategory.postcomp₂ f.1.unop ≫ (η ≫ f.2), map m := StrongTrans.whiskerLeft (Bicategory.postcomp₂ f.1.unop) (StrongTrans.whiskerRight m f.2) }
  map₂ { x y f g } η := by
    fconstructor
    fconstructor
    · intro a
      fconstructor
      · let ηa : postcomp₂ f.1.unop ≫ a ≫ f.2 ⟶ postcomp₂ f.1.unop ≫ a ≫ g.2 := (postcomp₂ f.1.unop ◁ (a ◁ η.2))
        let γ := (postcomposing₂ y.1.unop x.1.unop ).map (Hom2.unop2 η.1) ▷ (a ≫ g.2)
        exact Modification.vcomp ηa.as γ.as
    · intros _ _ h
      dsimp [StrongTrans.whiskerLeft]
      sorry
  mapId x := sorry
  mapComp f g := sorry
  map₂_id := sorry

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
    dsimp
    sorry
  map₂_whisker_right := sorry
  map₂_associator := sorry
  map₂_left_unitor := sorry
  map₂_right_unitor := sorry

def yonedaEvaluation : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v}) ⥤ᵖ Cat.{max u (max v w), max u (max v w)} := by
  refine (Pseudofunctor.comp yonedaEvaluation' CatPsudoULift)


def yonedaLemmaForwardsFunctor (x : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat)) : (yonedaPairing.obj x) ⥤ (yonedaEvaluation.obj x) where
  obj pair := by
    fconstructor
    exact (pair.app x.1).toFunctor.obj (𝟙 (unop x.1))
  map {a b} f := by
    fconstructor
    exact (f.as.app x.1).toNatTrans.app (𝟙 (unop x.1))

def yonedaLemmaForwards : StrongTrans (@yonedaPairing B _) (@yonedaEvaluation B _) where
  app x := by
    fconstructor
    exact yonedaLemmaForwardsFunctor x
  naturality {a b} f := sorry


def yonedaLemmaBackwardsFunctorObjFunctor (x : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat)) (eval : (yonedaEvaluation.obj x)) (a : Bᵒᵖ) : ↑((yoneda₀ (unop x.1)).obj a) ⥤ ↑(x.2.obj a) where
  obj b := sorry
  map := sorry

def yonedaLemmaBackwardsFunctorObj (x : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat)) (eval : (yonedaEvaluation.obj x)) : (yonedaPairing.obj x) where
  app a := {toFunctor := yonedaLemmaBackwardsFunctorObjFunctor x eval a}
  naturality := sorry

def yonedaLemmaBackwardsFunctor (x : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat)) : (yonedaEvaluation.obj x) ⥤ (yonedaPairing.obj x) where
  obj a := yonedaLemmaBackwardsFunctorObj x a
  map {a b} f := sorry

def yonedaLemmaBackwards : StrongTrans (@yonedaEvaluation B _)  (@yonedaPairing B _) where
  app x := by
    fconstructor
    exact yonedaLemmaBackwardsFunctor x
  naturality := sorry

structure BiEquiv (x y : B) where
  map : x ⟶ y
  inv : y ⟶ x
  homInvId : map ≫ inv ≅ 𝟙 x
  invHomId : inv ≫ map ≅ 𝟙 y

def yonedaLemma : BiEquiv (@yonedaPairing B _) (@yonedaEvaluation B _) where
  map := yonedaLemmaForwards
  inv := yonedaLemmaBackwards
  homInvId := sorry
  invHomId := sorry
