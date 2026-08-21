/-
Copyright (c) 2026 Spencer Woolfson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Spencer Woolfson
-/
import Biyoneda.EvaluationCore

/-!
# The associator cancellation core

`evaluation_associator_core` is by a wide margin the largest of the coherence cores — the
associator field's pasting has three `mapComp`s and two `Modification` naturalities to cancel —
so it gets a file to itself.  Its siblings are in `Biyoneda/EvaluationCore.lean`.

It carries its own `maxHeartbeats` bump; the reason is recorded at the declaration.
-/

namespace CategoryTheory.Bicategory

open CategoryTheory Bicategory Pseudofunctor StrongTrans Functor
open scoped Pseudofunctor.StrongTrans

universe u v w

variable {C : Type u} [Bicategory.{w, v} C]


set_option maxHeartbeats 400000 in
-- the `show` re-spelling and the `exact`-plug both bridge composite/nested point
-- spellings by defeq at default transparency
/-- The cancellation core of `evaluationPseudo.map₂_associator`, at a point `Z`. -/
lemma evaluation_associator_core {a b c d : C × (C ⥤ᵖ Cat.{w, v})}
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (W : ↑(b.2.obj a.1)) :
    (d.2.map ((f.1 ≫ g.1) ≫ h.1)).toFunctor.map (𝟙 ((h.2.app a.1).toFunctor.obj ((g.2.app
      a.1).toFunctor.obj W))) ≫ (d.2.map₂ (α_ f.1 g.1 h.1).hom).toNatTrans.app ((h.2.app
      a.1).toFunctor.obj ((g.2.app a.1).toFunctor.obj W)) = ((d.2.mapComp (f.1 ≫ g.1)
      h.1).hom.toNatTrans.app ((h.2.app a.1).toFunctor.obj ((g.2.app a.1).toFunctor.obj W)) ≫
      ((d.2.map h.1).toFunctor.map ((h.2.naturality (f.1 ≫ g.1)).inv.toNatTrans.app ((g.2.app
      a.1).toFunctor.obj W)) ≫ 𝟙 ((d.2.map h.1).toFunctor.obj ((h.2.app c.1).toFunctor.obj
      ((c.2.map (f.1 ≫ g.1)).toFunctor.obj ((g.2.app a.1).toFunctor.obj W))))) ≫ 𝟙 ((d.2.map
      h.1).toFunctor.obj ((h.2.app c.1).toFunctor.obj ((c.2.map (f.1 ≫ g.1)).toFunctor.obj
      ((g.2.app a.1).toFunctor.obj W))))) ≫ (h.2.app c.1 ≫ d.2.map h.1).toFunctor.map
      ((c.2.mapComp f.1 g.1).hom.toNatTrans.app ((g.2.app a.1).toFunctor.obj W) ≫ ((c.2.map
      g.1).toFunctor.map ((g.2.naturality f.1).inv.toNatTrans.app W) ≫ 𝟙 ((c.2.map
      g.1).toFunctor.obj ((g.2.app b.1).toFunctor.obj ((b.2.map f.1).toFunctor.obj W)))) ≫ 𝟙
      ((c.2.map g.1).toFunctor.obj ((g.2.app b.1).toFunctor.obj ((b.2.map f.1).toFunctor.obj W))))
      ≫ ((((d.2.map h.1).toFunctor.map ((h.2.naturality g.1).hom.toNatTrans.app ((g.2.app
      b.1).toFunctor.obj ((b.2.map f.1).toFunctor.obj W))) ≫ 𝟙 ((d.2.map h.1).toFunctor.obj
      ((d.2.map g.1).toFunctor.obj ((h.2.app b.1).toFunctor.obj ((g.2.app b.1).toFunctor.obj
      ((b.2.map f.1).toFunctor.obj W)))))) ≫ 𝟙 ((d.2.map h.1).toFunctor.obj ((d.2.map
      g.1).toFunctor.obj ((h.2.app b.1).toFunctor.obj ((g.2.app b.1).toFunctor.obj ((b.2.map
      f.1).toFunctor.obj W)))))) ≫ (d.2.mapComp g.1 h.1).inv.toNatTrans.app ((h.2.app
      b.1).toFunctor.obj ((g.2.app b.1).toFunctor.obj ((b.2.map f.1).toFunctor.obj W)))) ≫ (((𝟙
      ((d.2.map (g.1 ≫ h.1)).toFunctor.obj ((h.2.app b.1).toFunctor.obj ((g.2.app
      b.1).toFunctor.obj ((b.2.map f.1).toFunctor.obj W)))) ≫ (d.2.map (g.1 ≫ h.1)).toFunctor.map
      (((g.2 ≫ h.2).naturality f.1).hom.toNatTrans.app W)) ≫ 𝟙 ((d.2.map (g.1 ≫
      h.1)).toFunctor.obj ((d.2.map f.1).toFunctor.obj ((h.2.app a.1).toFunctor.obj ((g.2.app
      a.1).toFunctor.obj W))))) ≫ 𝟙 ((d.2.map (g.1 ≫ h.1)).toFunctor.obj ((d.2.map
      f.1).toFunctor.obj ((h.2.app a.1).toFunctor.obj ((g.2.app a.1).toFunctor.obj W))))) ≫
      (d.2.mapComp f.1 (g.1 ≫ h.1)).inv.toNatTrans.app ((h.2.app a.1).toFunctor.obj ((g.2.app
      a.1).toFunctor.obj W)) := by
  rw [Functor.map_id]
  rw [Category.id_comp]
  have hw := d.2.map₂_associator_app f.1 g.1 h.1
    ((h.2.app a.1).toFunctor.obj ((g.2.app a.1).toFunctor.obj W))
  rw [hw]
  rw [Pseudofunctor.StrongTrans.naturality_comp_inv_app h.2 f.1 g.1
    ((g.2.app a.1).toFunctor.obj W)]
  have hD := Cat.Hom₂.congr_app
    (Pseudofunctor.StrongTrans.categoryStruct_comp_naturality_hom g.2 h.2 f.1)
    W
  rw [hD]
  simp only [Category.id_comp, Category.comp_id, Category.assoc, Functor.map_comp,
    Cat.Hom.comp_map]
  iterate 12 (first | erw [eqToHom_refl] | erw [Category.id_comp] | erw [Category.comp_id] | skip)
  have hsplit : ((g.2.naturality f.1).hom ▷ h.2.app b.1 ≫
      g.2.app a.1 ◁ (h.2.naturality f.1).hom).toNatTrans.app
        W =
      (h.2.app b.1).toFunctor.map
        ((g.2.naturality f.1).hom.toNatTrans.app W) ≫
      (h.2.naturality f.1).hom.toNatTrans.app
        ((g.2.app a.1).toFunctor.obj W) := rfl
  erw [hsplit]
  simp only [← Functor.map_comp]
  change(d.2.mapComp (f.1 ≫ g.1) h.1).hom.toNatTrans.app
        ((h.2.app a.1).toFunctor.obj
          ((g.2.app a.1).toFunctor.obj W)) ≫
      (d.2.map h.1).toFunctor.map
        ((d.2.mapComp f.1 g.1).hom.toNatTrans.app
          ((h.2.app a.1).toFunctor.obj
            ((g.2.app a.1).toFunctor.obj W))) ≫
      (d.2.mapComp g.1 h.1).inv.toNatTrans.app
        ((d.2.map f.1).toFunctor.obj
          ((h.2.app a.1).toFunctor.obj
            ((g.2.app a.1).toFunctor.obj W))) ≫
      (d.2.mapComp f.1 (g.1 ≫ h.1)).inv.toNatTrans.app
        ((h.2.app a.1).toFunctor.obj
          ((g.2.app a.1).toFunctor.obj W)) =
    (d.2.mapComp (f.1 ≫ g.1) h.1).hom.toNatTrans.app
        ((h.2.app a.1).toFunctor.obj
          ((g.2.app a.1).toFunctor.obj W)) ≫
      (d.2.map h.1).toFunctor.map
        ((d.2.mapComp f.1 g.1).hom.toNatTrans.app
            ((h.2.app a.1).toFunctor.obj
              ((g.2.app a.1).toFunctor.obj W)) ≫
          (d.2.map g.1).toFunctor.map
            ((h.2.naturality f.1).inv.toNatTrans.app
              ((g.2.app a.1).toFunctor.obj W)) ≫
          (h.2.naturality g.1).inv.toNatTrans.app
            ((c.2.map f.1).toFunctor.obj
              ((g.2.app a.1).toFunctor.obj W)) ≫
          (h.2.app c.1).toFunctor.map
            ((c.2.mapComp f.1 g.1).inv.toNatTrans.app
              ((g.2.app a.1).toFunctor.obj W))) ≫
      (d.2.map h.1).toFunctor.map
        ((h.2.app c.1).toFunctor.map
          ((c.2.mapComp f.1 g.1).hom.toNatTrans.app
              ((g.2.app a.1).toFunctor.obj W) ≫
            (c.2.map g.1).toFunctor.map
              ((g.2.naturality f.1).inv.toNatTrans.app W) ≫
            𝟙 ((c.2.map g.1).toFunctor.obj
              ((g.2.app b.1).toFunctor.obj
                ((b.2.map f.1).toFunctor.obj W))))) ≫
      (d.2.map h.1).toFunctor.map
        ((h.2.naturality g.1).hom.toNatTrans.app
          ((g.2.app b.1).toFunctor.obj
            ((b.2.map f.1).toFunctor.obj W))) ≫
      (d.2.mapComp g.1 h.1).inv.toNatTrans.app
        ((h.2.app b.1).toFunctor.obj
          ((g.2.app b.1).toFunctor.obj
            ((b.2.map f.1).toFunctor.obj W))) ≫
      (d.2.map (g.1 ≫ h.1)).toFunctor.map
        ((h.2.app b.1).toFunctor.map
            ((g.2.naturality f.1).hom.toNatTrans.app W) ≫
          (h.2.naturality f.1).hom.toNatTrans.app
            ((g.2.app a.1).toFunctor.obj W)) ≫
      (d.2.mapComp f.1 (g.1 ≫ h.1)).inv.toNatTrans.app
        ((h.2.app a.1).toFunctor.obj
          ((g.2.app a.1).toFunctor.obj W))
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
          ((g.2.app a.1).toFunctor.obj W)) ≫
      (h.2.app c.1).toFunctor.map ((c.2.map g.1).toFunctor.map
        ((g.2.naturality f.1).inv.toNatTrans.app W)) ≫
      (h.2.naturality g.1).hom.toNatTrans.app
        ((g.2.app b.1).toFunctor.obj
          ((b.2.map f.1).toFunctor.obj W)) =
      (d.2.map g.1).toFunctor.map ((h.2.app b.1).toFunctor.map
        ((g.2.naturality f.1).inv.toNatTrans.app W)) := by
    simpa only [Cat.Hom.comp_toFunctor, Functor.comp_map] using
      Cat.naturality_1 (h.2.naturality g.1)
        ((g.2.naturality f.1).inv.toNatTrans.app W)
  erw [key1]
  erw [← Functor.map_comp]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  have key2 : (d.2.map h.1).toFunctor.map ((d.2.map g.1).toFunctor.map
        ((h.2.naturality f.1).inv.toNatTrans.app
          ((g.2.app a.1).toFunctor.obj W) ≫
         (h.2.app b.1).toFunctor.map
          ((g.2.naturality f.1).inv.toNatTrans.app W))) ≫
      (d.2.mapComp g.1 h.1).inv.toNatTrans.app
        ((h.2.app b.1).toFunctor.obj
          ((g.2.app b.1).toFunctor.obj
            ((b.2.map f.1).toFunctor.obj W))) ≫
      (d.2.map (g.1 ≫ h.1)).toFunctor.map
        ((h.2.app b.1).toFunctor.map
          ((g.2.naturality f.1).hom.toNatTrans.app W) ≫
         (h.2.naturality f.1).hom.toNatTrans.app
          ((g.2.app a.1).toFunctor.obj W)) ≫
      (d.2.mapComp f.1 (g.1 ≫ h.1)).inv.toNatTrans.app
        ((h.2.app a.1).toFunctor.obj
          ((g.2.app a.1).toFunctor.obj W)) =
      (d.2.mapComp g.1 h.1).inv.toNatTrans.app
        ((d.2.map f.1).toFunctor.obj
          ((h.2.app a.1).toFunctor.obj
            ((g.2.app a.1).toFunctor.obj W))) ≫
      (d.2.mapComp f.1 (g.1 ≫ h.1)).inv.toNatTrans.app
        ((h.2.app a.1).toFunctor.obj
          ((g.2.app a.1).toFunctor.obj W)) := by
    have hn2 : (d.2.map h.1).toFunctor.map ((d.2.map g.1).toFunctor.map
          ((h.2.naturality f.1).inv.toNatTrans.app
            ((g.2.app a.1).toFunctor.obj W) ≫
           (h.2.app b.1).toFunctor.map
            ((g.2.naturality f.1).inv.toNatTrans.app W))) ≫
        (d.2.mapComp g.1 h.1).inv.toNatTrans.app
          ((h.2.app b.1).toFunctor.obj
            ((g.2.app b.1).toFunctor.obj
              ((b.2.map f.1).toFunctor.obj W))) =
        (d.2.mapComp g.1 h.1).inv.toNatTrans.app
          ((d.2.map f.1).toFunctor.obj
            ((h.2.app a.1).toFunctor.obj
              ((g.2.app a.1).toFunctor.obj W))) ≫
        (d.2.map (g.1 ≫ h.1)).toFunctor.map
          ((h.2.naturality f.1).inv.toNatTrans.app
            ((g.2.app a.1).toFunctor.obj W) ≫
           (h.2.app b.1).toFunctor.map
            ((g.2.naturality f.1).inv.toNatTrans.app W)) :=
      (d.2.mapComp g.1 h.1).inv.toNatTrans.naturality
        ((h.2.naturality f.1).inv.toNatTrans.app
          ((g.2.app a.1).toFunctor.obj W) ≫
         (h.2.app b.1).toFunctor.map
          ((g.2.naturality f.1).inv.toNatTrans.app W))
    rw [← Category.assoc]
    rw [hn2]
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

end CategoryTheory.Bicategory
