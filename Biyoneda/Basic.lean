import Mathlib.CategoryTheory.Bicategory.Product
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Bicategory.Yoneda
import Mathlib.CategoryTheory.Category.ULift


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
    -- ext x
    -- simp
    -- congr
    -- let rwh := ULiftHom.up.map_id (((CatLift.map (f ≫ g)).toFunctor.obj x))
  map₂_whisker_right := sorry
  map₂_associator := sorry
  map₂_left_unitor := sorry
  map₂_right_unitor := sorry

variable {B : Type u} [Bicategory.{w, v} B]

def yonedaPairing : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v}) ⥤ᵖ Cat.{max u (max v w), max u (max v w)} where
  obj x := @Cat.of (Pseudofunctor.StrongTrans (yoneda₀ x.fst.unop) x.snd) (Pseudofunctor.StrongTrans.homCategory)
  map {x y} f := sorry
  map₂ { x y f g } η := sorry
  mapId x := sorry
  mapComp f g := sorry
  map₂_id := sorry

def yonedaEvaluation' : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v}) ⥤ᵖ Cat.{w, v} where
  obj x := x.snd.obj x.fst
  map {x y} f := f.2.app x.1 ≫ (y.2.map f.1)
  map₂ { x y f g } η := (η.2.as.app x.1 ▷ y.2.map f.1) ≫ (_ ◁ y.2.map₂ η.1)
  mapId x := (_root_.id (x.2.mapId x.1))
  mapComp {a b c} f g := by
    simp only [prod_comp, comp_app, Category.assoc]
    fconstructor
    · refine (f.2.app a.1) ◁ ((g.2.app a.1 ◁ (c.2.mapComp f.1 g.1).hom) ≫ ?_)
      refine (associator (g.2.app a.1) (c.2.map f.1) (c.2.map g.1)).inv ≫ ?_ ≫ (associator (b.2.map f.1) (g.2.app b.1) (c.2.map g.1)).hom
      exact (g.2.naturality f.1).inv ▷ (c.2.map g.1)
    · refine (f.2.app a.1) ◁ (?_ ≫ (g.2.app a.1 ◁ (c.2.mapComp f.1 g.1).inv))
      refine  (associator (b.2.map f.1) (g.2.app b.1) (c.2.map g.1)).inv ≫ ?_ ≫ (associator (g.2.app a.1) (c.2.map f.1) (c.2.map g.1)).hom
      exact (g.2.naturality f.1).hom ▷ (c.2.map g.1)
    · simp
    · simp
  map₂_whisker_left {a b c} := by sorry
  map₂_whisker_right := sorry
  map₂_associator := sorry
  map₂_left_unitor := sorry
  map₂_right_unitor := sorry

def yonedaEvaluation : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v}) ⥤ᵖ Cat.{max u (max v w), max u (max v w)} := by
  refine (Pseudofunctor.comp yonedaEvaluation' CatPsudoULift)

def yonedaLemmaForward : (@yonedaEvaluation B _) ⟶ (@yonedaPairing B _) := sorry

def yonedaLemmaBackward : (@yonedaPairing B _) ⟶ (@yonedaEvaluation B _):= sorry

structure BiEquiv (x y : B) where
  map : x ⟶ y
  inv : y ⟶ x
  homInvId : map ≫ inv ≅ 𝟙 x
  invHomId : inv ≫ map ≅ 𝟙 y

def yonedaLemma : BiEquiv (@yonedaEvaluation B _) (@yonedaPairing B _) where
  map := yonedaLemmaForward
  inv := yonedaLemmaBackward
  homInvId := sorry
  invHomId := sorry
