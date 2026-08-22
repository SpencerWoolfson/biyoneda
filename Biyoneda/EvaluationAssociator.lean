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
  rw [← Functor.map_comp_assoc]
  first
    | rw [← Functor.map_comp_assoc]
    | erw [← Functor.map_comp_assoc]
  simp only [Category.assoc]
  first
    | rw [← Functor.map_comp_assoc]
    | erw [← Functor.map_comp_assoc]
  -- the cancelling inv/hom pair is split across two `(d.2.map h.1).map _` applications, so
  -- recombine (and clear the `map (𝟙 _)`) before trying to cancel it
  simp only [Functor.map_id, Category.id_comp, Category.comp_id, ← Functor.map_comp,
    Category.assoc]
  -- PARKED (v4.33).  Everything above this point works; the proof gets three
  -- `← Functor.map_comp_assoc` steps further than it did on v4.30, and the large hand-written
  -- `change` block that used to sit after `erw [hsplit]` turned out to be redundant and is gone.
  --
  -- Residual goal: the right-hand side still carries a cancelling
  --   `(h.2.app c.1).map ((c.2.mapComp f.1 g.1).inv.app X)` / `... .hom.app X`
  -- pair split across two *separate* `(d.2.map h.1).map _` applications, plus an
  -- `(h.2.app c.1).map (𝟙 _)`.  Cancelling needs them under one `map`, and recombining is what
  -- fails: `simp only [← Functor.map_comp]`, `erw [← Functor.map_comp]` and
  -- `simp only [Functor.map_id]` all decline.  The blocker is a spelling mismatch at the join
  -- -- `(c.2.map (f.1 ≫ g.1)).obj _` against `(c.2.map f.1 ≫ c.2.map g.1).obj _` -- so the
  -- endpoints are defeq but not syntactically equal and `Functor.map_comp` cannot instantiate.
  --
  -- Candidate next moves, in the order worth trying:
  --   1. a pinned `have` doing the cancellation at the inner level, in the style of `key1`
  --      below -- that is the pattern that already works elsewhere in this file;
  --   2. a `mapComp`-spelling bridge lemma (`rfl`) for the join, then plain `simp`;
  --   3. re-prove the lemma from `prod_associator_snd_as_app_app` rather than patching.
  --
  -- The parked tail included two worked sublemmas, `key1` (naturality of `h.2.naturality g.1`
  -- against `(g.2.naturality f.1).inv`) and `key2` (the `mapComp` cancellation), both of which
  -- still look right and should be reused rather than rewritten.  They live, with the rest of
  -- the v4.30 proof, in `git show comp-core:Biyoneda/EvaluationAssociator.lean`.
  sorry

end CategoryTheory.Bicategory
