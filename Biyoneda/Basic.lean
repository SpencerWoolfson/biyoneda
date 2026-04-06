import Mathlib.CategoryTheory.Bicategory.Product
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Bicategory.Yoneda
import Mathlib.CategoryTheory.Category.ULift


open CategoryTheory Bicategory Bicategory.Opposite Opposite Pseudofunctor StrongTrans
open scoped Pseudofunctor.StrongTrans

universe u v w v₁ v₂ u₁ u₂

#check ULiftHom.category.{v₁, v₂, (max u₁ u₂)}

def CatPsudoULift : Cat.{v₁, u₁} ⥤ᵖ Cat.{max v₁ v₂, max u₁ u₂} where
  obj C := by
    rcases C with ⟨C⟩
    fconstructor
    · apply ULift.{u₂, u₁} C
    · refine @ULiftHom.category.{v₁, v₂, (max u₁ u₂)} (ULift.{u₂, u₁} C) (uliftCategory C)
  map F := by
    fconstructor
    rcases F with ⟨F⟩
    refine  ?_ ⋙ ULiftHom.down ⋙ F ⋙ ULiftHom.up  ⋙ ?_
    · sorry
    · sorry
  map₂ { C D } α := sorry
  mapId C := sorry
  mapComp F G := sorry
  map₂_id := sorry

variable {B : Type u} [Bicategory.{w, v} B]

def yonedaPairing : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v}) ⥤ᵖ Cat.{max u (max v w), max u (max v w)} where
  obj x := @Cat.of (Pseudofunctor.StrongTrans (yoneda₀ x.fst.unop) x.snd) (Pseudofunctor.StrongTrans.homCategory)
  map f := by sorry
  map₂ { x y f g } η := sorry
  mapId x := sorry
  mapComp f g := sorry
  map₂_id := sorry

def yonedaEvaluation' : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v}) ⥤ᵖ Cat.{w, v} where
  obj x := x.snd.obj x.fst
  map {x y} f := f.2.app x.1 ≫ (y.2.map f.1)
  map₂ { x y f g } η := (η.2.as.app x.1 ▷ y.2.map f.1) ≫ (_ ◁ y.2.map₂ η.1)
  mapId x := (_root_.id (x.2.mapId x.1))
  mapComp f g := by
    simp only [prod_comp, comp_app, Category.assoc]
    rename_i a b c
    fconstructor
    · refine (f.2.app a.1) ◁ ?_
      refine (g.2.app a.1 ◁ (c.2.mapComp f.1 g.1).hom) ≫ ?_
      refine (associator (g.2.app a.1) (c.2.map f.1) (c.2.map g.1)).inv ≫ ?_ ≫ (associator (b.2.map f.1) (g.2.app b.1) (c.2.map g.1)).hom
      refine ?_ ▷ (c.2.map g.1)


    · sorry
    · sorry
    · sorry

def yonedaEvaluation : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v}) ⥤ᵖ Cat.{max u (max v w), max u (max v w)} := by
  refine (Pseudofunctor.comp yonedaEvaluation' CatPsudoULift)

def yonedaLemmaForward : (@yonedaEvaluation B _) ⟶ (@yonedaPairing B _) := sorry

def yonedaLemmaBackward : (@yonedaPairing B _) ⟶ (@yonedaEvaluation B _):= sorry
