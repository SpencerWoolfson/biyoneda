/-
Copyright (c) 2026 Spencer Woolfson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Spencer Woolfson
-/
import Mathlib.CategoryTheory.Bicategory.Product
import Mathlib.Tactic.CategoryTheory.Bicategory.Basic
import Mathlib.Tactic.CategoryTheory.Slice
import Biyoneda.ForMathlib

/-!
# Cancellation cores for the evaluation pseudofunctor

`evaluationPseudo`'s coherence fields are large pastings, but once descended into a fibre each
one is a short chain of `mapComp` naturality, `Modification` naturality, and
strong-transformation `naturality_naturality`.  These lemmas state that content at a point,
so the fields themselves reduce to a single `exact`.

The associator core is several times the size of the rest and lives on its own in
`Biyoneda/EvaluationAssociator.lean`.
-/

namespace CategoryTheory.Bicategory

open CategoryTheory Bicategory Pseudofunctor StrongTrans Functor
open scoped Pseudofunctor.StrongTrans

universe u v w

variable {C : Type u} [Bicategory.{w, v} C]


/-- The cancellation core of `evaluationPseudo.map₂_left_unitor`, at a point `Z`. -/
lemma evaluation_left_unitor_core {a b : C × (C ⥤ᵖ Cat.{w, v})} (f : a ⟶ b)
    (Z : ↑(a.2.obj a.1)) :
    (b.2.map (𝟙 a.1 ≫ f.1)).toFunctor.map
        (((λ_ f).hom.2.as.app a.1).toNatTrans.app Z) ≫
      (b.2.map₂ (λ_ f.1).hom).toNatTrans.app ((f.2.app a.1).toFunctor.obj Z) =
    ((b.2.mapComp (𝟙 a.1) f.1).hom.toNatTrans.app ((f.2.app a.1).toFunctor.obj Z) ≫
      (b.2.map f.1).toFunctor.map
        ((f.2.naturality (𝟙 a.1)).inv.toNatTrans.app Z)) ≫
      (b.2.map f.1).toFunctor.map
        ((f.2.app a.1).toFunctor.map ((a.2.mapId a.1).hom.toNatTrans.app Z)) := by
  have hw := Cat.Hom₂.congr_app (b.2.map₂_left_unitor f.1) ((f.2.app a.1).toFunctor.obj Z)
  dsimp at hw
  have hid := Pseudofunctor.StrongTrans.naturality_id_hom_app f.2 a.1 Z
  dsimp at hid
  have hl : ((λ_ f).hom.2.as.app a.1).toNatTrans.app Z =
      𝟙 ((f.2.app a.1).toFunctor.obj Z) := rfl
  have c1 := Cat.Hom.inv_hom_id_toNatTrans_app (b.2.mapId a.1) ((f.2.app a.1).toFunctor.obj Z)
  have key : (f.2.naturality (𝟙 a.1)).inv.toNatTrans.app Z ≫
      (f.2.app a.1).toFunctor.map ((a.2.mapId a.1).hom.toNatTrans.app Z) =
      (b.2.mapId a.1).hom.toNatTrans.app ((f.2.app a.1).toFunctor.obj Z) := by
    apply (Iso.inv_comp_eq ((Cat.Hom.toNatIso (f.2.naturality (𝟙 a.1))).app Z)).mpr
    change (f.2.app a.1).toFunctor.map ((a.2.mapId a.1).hom.toNatTrans.app Z) =
      (f.2.naturality (𝟙 a.1)).hom.toNatTrans.app Z ≫
      (b.2.mapId a.1).hom.toNatTrans.app ((f.2.app a.1).toFunctor.obj Z)
    rw [hid]
    erw [Category.assoc]
    erw [c1]
    erw [Category.comp_id]
  rw [hl]
  erw [Functor.map_id]
  erw [Category.id_comp]
  rw [hw]
  simp only [Category.assoc]
  erw [← Functor.map_comp]
  erw [key]
  rw [Category.comp_id]

/-- The cancellation core of `evaluationPseudo.map₂_right_unitor`, at a point `Z`. -/
lemma evaluation_right_unitor_core {a b : C × (C ⥤ᵖ Cat.{w, v})} (f : a ⟶ b)
    (Z : ↑(a.2.obj a.1)) :
    (b.2.map (f.1 ≫ 𝟙 b.1)).toFunctor.map
        (((ρ_ f).hom.2.as.app a.1).toNatTrans.app Z) ≫
      (b.2.map₂ (ρ_ f.1).hom).toNatTrans.app ((f.2.app a.1).toFunctor.obj Z) =
    ((b.2.mapComp f.1 (𝟙 b.1)).hom.toNatTrans.app ((f.2.app a.1).toFunctor.obj Z) ≫
      (b.2.map (𝟙 b.1)).toFunctor.map
        (((𝟙 b.2 : b.2 ⟶ b.2).naturality f.1).inv.toNatTrans.app
          ((f.2.app a.1).toFunctor.obj Z))) ≫
      (b.2.mapId b.1).hom.toNatTrans.app
        ((b.2.map f.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z)) := by
  have hw := Cat.Hom₂.congr_app (b.2.map₂_right_unitor f.1) ((f.2.app a.1).toFunctor.obj Z)
  dsimp at hw
  have hr : ((ρ_ f).hom.2.as.app a.1).toNatTrans.app Z =
      𝟙 ((f.2.app a.1).toFunctor.obj Z) := rfl
  have hidt : ((𝟙 b.2 : b.2 ⟶ b.2).naturality f.1).inv.toNatTrans.app
      ((f.2.app a.1).toFunctor.obj Z) =
      𝟙 ((b.2.map f.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z)) := by
    first
      | rfl
      | (simp; rfl)
      | simp
  rw [hr]
  erw [Functor.map_id]
  erw [Category.id_comp]
  rw [hw]
  rw [hidt]
  erw [Functor.map_id]
  simp only [Category.comp_id, Category.assoc]
  -- the residual `𝟙` sits at a different spelling of the fibre category, so `simp only` will not
  -- collapse it reducibly and `rw` reports a bad motive; `congrArg` sidesteps both by never
  -- forming a motive at all
  exact congrArg (· ≫ _) (Category.comp_id _).symm

/-- The cancellation core of `evaluationPseudo.map₂_whisker_right`, at a point `Z`. -/
lemma evaluation_whisker_right_core {a b c : C × (C ⥤ᵖ Cat.{w, v})} {f g : a ⟶ b}
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
  have hnn := η.2.naturality_naturality_app h.1
    ((g.2.app a.1).toFunctor.obj Z)
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
  -- `Functor.map_comp` above reintroduced a `(_ ≫ _) ≫ _` group after the earlier `assoc` pass,
  -- so renormalise before slicing; the factors `hnnG` matches sit at 4-5 once flattened
  simp only [Category.assoc]
  slice_rhs 4 5 => erw [hnnG]
  slice_rhs 2 3 => erw [hsG]
  -- stated flattened: the slices above leave the right-hand side associated to the left, so a
  -- `map (_ ≫ _) ≫ map (_ ≫ _)` phrasing no longer matches it
  have key : (c.2.map η.1).toFunctor.map
        ((c.2.map f.1).toFunctor.map
          ((η.2.app a.1).toFunctor.map ((h.2.as.app a.1).toNatTrans.app Z))) ≫
      (c.2.map η.1).toFunctor.map
        ((η.2.naturality f.1).inv.toNatTrans.app ((g.2.app a.1).toFunctor.obj Z)) ≫
      (c.2.map η.1).toFunctor.map
        ((η.2.naturality f.1).hom.toNatTrans.app ((g.2.app a.1).toFunctor.obj Z)) ≫
      (c.2.map η.1).toFunctor.map
        ((c.2.map₂ h.1).toNatTrans.app
          ((η.2.app a.1).toFunctor.obj ((g.2.app a.1).toFunctor.obj Z))) =
      (c.2.map η.1).toFunctor.map
        ((c.2.map f.1).toFunctor.map ((h.2.as.app a.1 ▷ η.2.app a.1).toNatTrans.app Z)) ≫
      (c.2.map η.1).toFunctor.map
        ((c.2.map₂ h.1).toNatTrans.app
          ((η.2.app a.1).toFunctor.obj ((g.2.app a.1).toFunctor.obj Z))) := by
    conv_lhs => rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
    conv_rhs => rw [← Functor.map_comp]
    refine congrArg _ ?_
    erw [c1']
    rfl
  simp only [Category.assoc]
  slice_rhs 2 5 => erw [key]
  simp only [Category.assoc]

/-- The cancellation core of `evaluationPseudo.map₂_whisker_left`, at a point `Z`. -/
lemma evaluation_whisker_left_core {a b c : C × (C ⥤ᵖ Cat.{w, v})} (f : a ⟶ b)
    {g h : b ⟶ c} (η : g ⟶ h) (W : ↑(b.2.obj a.1)) :
    ((c.2.mapComp f.1 g.1).hom.toNatTrans.app ((g.2.app a.1).toFunctor.obj W) ≫
      (c.2.map g.1).toFunctor.map
        ((c.2.map f.1).toFunctor.map ((η.2.as.app a.1).toNatTrans.app W))) ≫
      (c.2.map₂ η.1).toNatTrans.app
        ((c.2.map f.1).toFunctor.obj ((h.2.app a.1).toFunctor.obj W)) ≫
      (c.2.mapComp f.1 h.1).inv.toNatTrans.app ((h.2.app a.1).toFunctor.obj W) =
    (c.2.mapComp f.1 g.1).hom.toNatTrans.app ((g.2.app a.1).toFunctor.obj W) ≫
      (c.2.map g.1).toFunctor.map ((g.2.naturality f.1).inv.toNatTrans.app W) ≫
      ((c.2.map g.1).toFunctor.map
          ((η.2.as.app b.1).toNatTrans.app ((b.2.map f.1).toFunctor.obj W)) ≫
        (c.2.map₂ η.1).toNatTrans.app
          ((h.2.app b.1).toFunctor.obj ((b.2.map f.1).toFunctor.obj W))) ≫
      (c.2.map h.1).toFunctor.map ((h.2.naturality f.1).hom.toNatTrans.app W) ≫
      (c.2.mapComp f.1 h.1).inv.toNatTrans.app ((h.2.app a.1).toFunctor.obj W) := by
  have h2 := modification_naturality_app η.2 f.1 W
  have h3 : (c.2.map g.1).toFunctor.map
        ((h.2.naturality f.1).hom.toNatTrans.app W) ≫
      (c.2.map₂ η.1).toNatTrans.app
        ((c.2.map f.1).toFunctor.obj
          ((h.2.app a.1).toFunctor.obj W)) =
      (c.2.map₂ η.1).toNatTrans.app
        ((h.2.app b.1).toFunctor.obj
          ((b.2.map f.1).toFunctor.obj W)) ≫
      (c.2.map h.1).toFunctor.map
        ((h.2.naturality f.1).hom.toNatTrans.app W) :=
    (c.2.map₂ η.1).toNatTrans.naturality
      ((h.2.naturality f.1).hom.toNatTrans.app W)
  simp only [Category.assoc]
  slice_rhs 4 5 => rw [← h3]
  slice_rhs 3 4 => erw [← Functor.map_comp]
  erw [h2]
  slice_rhs 2 3 => erw [← Functor.map_comp]
  have c1' := Cat.Hom.inv_hom_id_toNatTrans_app_assoc (g.2.naturality f.1)
    W
    ((c.2.map f.1).toFunctor.map
      ((η.2.as.app a.1).toNatTrans.app W))
  erw [c1']
  simp only [Category.assoc]

/-- In the product bicategory `C × (C ⥤ᵖ Cat)`, the second component of the associator is a
modification whose components are identities — `Cat` is strict, so this holds by `rfl`.  Stating
it lets `simp` cancel the term instead of leaving it for a defeq-level `erw`. -/
lemma prod_associator_snd_as_app_app {a b c d : C × (C ⥤ᵖ Cat.{w, v})}
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (Z : ↑(a.2.obj a.1)) :
    ((α_ f g h).hom.2.as.app a.1).toNatTrans.app Z = 𝟙 _ := rfl

end CategoryTheory.Bicategory
