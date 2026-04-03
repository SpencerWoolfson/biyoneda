import Mathlib.CategoryTheory.Bicategory.Product
import Mathlib.CategoryTheory.Bicategory.Yoneda

open CategoryTheory Bicategory Bicategory.Opposite Opposite Pseudofunctor StrongTrans

universe u v w

variable {B : Type u} [Bicategory.{w, v} B]

def yonedaPairing : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v}) ⥤ᵖ Cat.{max u (max v w), max u (max v w)} := sorry
  -- obj x := @Cat.of (Pseudofunctor.StrongTrans (yoneda₀ x.fst.unop) x.snd) (Pseudofunctor.StrongTrans.homCategory)
  -- map f := by sorry
  --   -- refine ?_ ◁ ?_ ⋙ ?_

def yonedaEvaluation' : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v}) ⥤ᵖ Cat.{w, v} where
  obj x := x.snd.obj x.fst
  map {x y} f := f.2.app x.1 ≫ (y.2.map f.1)
  map₂ { x y f g } η := (η.2.as.app x.1 ▷ y.2.map f.1) ≫ (_ ◁ y.2.map₂ η.1)
  mapId x := (_root_.id (x.2.mapId x.1))
  mapComp f g := sorry

def yonedaEvaluation : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v}) ⥤ᵖ Cat.{max u (max v w), max u (max v w)} := by
  refine (Pseudofunctor.comp yonedaEvaluation' ?_)
  sorry
