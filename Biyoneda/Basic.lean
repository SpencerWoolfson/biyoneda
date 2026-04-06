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

def CatPsudoULift : Cat.{v₁, u₁} ⥤ᵖ Cat.{max v₁ v₂, max u₁ u₂} where
  obj C := by
    rcases C with ⟨C⟩
    exact Cat.of (ULiftHom.{v₂} (ULift.{u₂, u₁} C))
  map F := by
    rename_i X Y
    rcases X with ⟨C⟩
    rcases Y with ⟨D⟩
    fconstructor
    rcases F with ⟨F⟩
    letI : Category (ULift.{u₂, u₁} C) := uliftCategory C
    letI : Category (ULift.{u₂, u₁} D) := uliftCategory D
    change ULiftHom.{v₂} (ULift.{u₂, u₁} C) ⥤ ULiftHom.{v₂} (ULift.{u₂, u₁} D)
    exact
      (ULiftHom.down ⋙ ULift.downFunctor ⋙ ULiftHom.up) ⋙ ULiftHom.down ⋙ F ⋙
        ULiftHom.up ⋙ (ULiftHom.down ⋙ ULift.upFunctor ⋙ ULiftHom.up)
  map₂ { C D } α := sorry
  mapId C := sorry
  mapComp F G := sorry
  map₂_id := sorry

variable {B : Type u} [Bicategory.{w, v} B]

def yonedaPairing : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v}) ⥤ᵖ Cat.{max u (max v w), max u (max v w)} where
  obj x := Cat.of ((yoneda₀ x.fst.unop) ⟶ x.snd)
  map f :=
    Functor.toCatHom
      { obj η := Bicategory.postcomp₂ f.1.unop ≫ (η ≫ f.2)
        map m :=
          StrongTrans.whiskerLeft (Bicategory.postcomp₂ f.1.unop) (StrongTrans.whiskerRight m f.2) }
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
    · refine (f.2.app a.1) ◁ ((g.2.app a.1 ◁ (c.2.mapComp f.1 g.1).hom) ≫ ?_)
      refine (associator (g.2.app a.1) (c.2.map f.1) (c.2.map g.1)).inv ≫ ?_ ≫ (associator (b.2.map f.1) (g.2.app b.1) (c.2.map g.1)).hom
      exact (g.2.naturality f.1).inv ▷ (c.2.map g.1)
    · refine (f.2.app a.1) ◁ (?_ ≫ (g.2.app a.1 ◁ (c.2.mapComp f.1 g.1).inv))
      refine  (associator (b.2.map f.1) (g.2.app b.1) (c.2.map g.1)).inv ≫ ?_ ≫ (associator (g.2.app a.1) (c.2.map f.1) (c.2.map g.1)).hom
      exact (g.2.naturality f.1).hom ▷ (c.2.map g.1)
    · simp
    · simp
  map₂_whisker_left := sorry
  map₂_whisker_right := sorry
  map₂_associator := sorry
  map₂_left_unitor := sorry
  map₂_right_unitor := sorry


def yonedaEvaluation : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v}) ⥤ᵖ Cat.{max u (max v w), max u (max v w)} := by
  refine (Pseudofunctor.comp yonedaEvaluation' CatPsudoULift)

def yonedaLemmaForward : (@yonedaEvaluation B _) ⟶ (@yonedaPairing B _) := sorry

def yonedaLemmaBackward : (@yonedaPairing B _) ⟶ (@yonedaEvaluation B _):= sorry
