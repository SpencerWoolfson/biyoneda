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
# The evaluation pseudofunctor

For a bicategory `C`, this file constructs the **evaluation pseudofunctor**

  `evaluationPseudo : C × (C ⥤ᵖ Cat) ⥤ᵖ Cat`,   `(c, F) ↦ F.obj c`,

together with the five point-level coherence lemmas its structure fields need.

Nothing here is specific to the Yoneda lemma: `C` is an arbitrary bicategory.  The
bicategorical Yoneda development uses the instance `C := Bᵒᵖ` (see `Biyoneda.Basic`), but the
construction is the bicategorical analogue of Mathlib's `CategoryTheory.evaluation` for
1-categories, which is currently missing from the `Bicategory` library.

## Implementation notes

The target bicategory is fixed to `Cat` rather than an arbitrary bicategory `D`.  This is not
incidental: the `mapId` field is `x.2.mapId x.1`, which typechecks only because `Cat` is a
`Bicategory.Strict` and so the left unitor `𝟙 ≫ F.map (𝟙 _)` reduces definitionally.  Over a
general `D` the field needs an explicit `λ_`, which changes the term and is a separate
(non-definitional) construction.

The `*_core` lemmas are the cancellation cores of the corresponding coherence fields, stated
at a point `Z` of the fibre.  They are separated out because the fields' goals are large
pastings whose content, once descended into a fibre, is a short chain of `mapComp` naturality,
`Modification` naturality (`modification_naturality_app`), and strong-transformation
`naturality_naturality`.
-/

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

/-- The cancellation core of `evaluationPseudo.map₂_right_unitor`, at a point `Z`. -/
lemma evaluation_right_unitor_core {a b : C × (C ⥤ᵖ Cat.{w, v})} (f : a ⟶ b)
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

/-- The cancellation core of `evaluationPseudo.map₂_whisker_left`, at a point `Z`. -/
lemma evaluation_whisker_left_core {a b c : C × (C ⥤ᵖ Cat.{w, v})} (f : a ⟶ b)
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
/-- The cancellation core of `evaluationPseudo.map₂_associator`, at a point `Z`. -/
lemma evaluation_associator_core {a b c d : C × (C ⥤ᵖ Cat.{w, v})}
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
The *evaluation pseudofunctor* `C × (C ⥤ᵖ Cat) ⥤ᵖ Cat.{w, v}`.

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
def evaluationPseudo : C × (C ⥤ᵖ Cat.{w, v}) ⥤ᵖ Cat.{w, v} where
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
