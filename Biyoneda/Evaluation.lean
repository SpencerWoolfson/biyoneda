/-
Copyright (c) 2026 Spencer Woolfson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Spencer Woolfson
-/
import Biyoneda.EvaluationAssociator

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

namespace CategoryTheory.Bicategory

open CategoryTheory Bicategory Pseudofunctor StrongTrans Functor
open scoped Pseudofunctor.StrongTrans

universe u v w

variable {C : Type u} [Bicategory.{w, v} C]


set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
-- the `skip` alternatives in the erosion loops are structural: `iterate` aborts at the
-- first wholly-failing round without them, and are unreachable on the successful path
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
    rw [Cat.whiskerLeft_app]
    have hw := c.2.map₂_whisker_left_app f.1 η.1
      (((f ≫ h).2.app a.1).toFunctor.obj Z)
    rw [hw]
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
    simpa using evaluation_whisker_left_core f η ((f.2.app a.1).toFunctor.obj Z)
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
    have hw := c.2.map₂_whisker_right_app h.1 η.1
      (((g ≫ η).2.app a.1).toFunctor.obj Z)
    rw [hw]
    have hnn := η.2.naturality_naturality_app h.1
      ((g.2.app a.1).toFunctor.obj Z)
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
    simpa using evaluation_whisker_right_core h η Z
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
    -- PARKED (v4.33).  `erw [prod_associator_snd_as_app_app, ...]` no longer finds its pattern
    -- after the `simp only` above.  Note this field is blocked anyway:
    -- `evaluation_associator_core` is itself parked in EvaluationAssociator.lean, so even a
    -- working rewrite chain here would only inherit that sorry.  Fix the core first.
    sorry
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
    -- PARKED (v4.33).  `evaluation_left_unitor_core` is proved and correct; the two sides
    -- differ in exactly two places and neither yields to the simp set:
    --   * the goal has `((λ_ (f.2.app a.1)).hom ▷ b.2.map (𝟙 a.1 ≫ f.1)).toNatTrans.app Z`
    --     where the core lemma has `(b.2.map (𝟙 a.1 ≫ f.1)).toFunctor.map (𝟙 _)`;
    --   * the goal leaves `((𝟙 a.2).app a.1).toFunctor.obj Z` un-reduced where the core has `Z`.
    -- Tried: `Pseudofunctor.StrongTrans.categoryStruct_id_app` (the `@[simps!]`-generated name --
    -- `StrongTrans.id_app` does not exist), `Cat.leftUnitor_hom_app`, the whiskering component
    -- lemmas, and a plain `simpa`.  None reduce either place.
    sorry
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
    -- PARKED (v4.33).  Mirror image of `map₂_left_unitor` above -- same two gaps, same
    -- failed attempts.  Whatever fixes one fixes this.
    sorry

/-!
## Component API for `evaluationPseudo`

The structure fields of `evaluationPseudo` are large pastings, but every coherence obligation in
practice descends into a fibre, where only the *components* matter.  The lemmas below give those
components in reduced form.

`evaluationPseudo_mapComp_hom_app` / `_inv_app` are the important ones: they state the `mapComp`
component with the associator identities of the strict bicategory `Cat` already cancelled, so a
proof can rewrite once instead of hand-cancelling them with an ordered `erw` chain.

These are deliberately **not** `@[simp]` — see the note in `Biyoneda.ForMathlib`: tagging them
globally adds a match attempt to every bare `simp` in the development.  Cite them explicitly.
-/

section API

variable {x y : C × (C ⥤ᵖ Cat.{w, v})}

/-- `evaluationPseudo` on objects: `(c, F) ↦ F.obj c`. -/
lemma evaluationPseudo_obj (x : C × (C ⥤ᵖ Cat.{w, v})) :
    (evaluationPseudo (C := C)).obj x = x.2.obj x.1 := rfl

/-- `evaluationPseudo` on 1-morphisms. -/
lemma evaluationPseudo_map (f : x ⟶ y) :
    (evaluationPseudo (C := C)).map f = f.2.app x.1 ≫ y.2.map f.1 := rfl

/-- `evaluationPseudo`'s unit coherence is that of the second component. -/
lemma evaluationPseudo_mapId (x : C × (C ⥤ᵖ Cat.{w, v})) :
    (evaluationPseudo (C := C)).mapId x = x.2.mapId x.1 := rfl

/-- Point form of `evaluationPseudo_map`. -/
lemma evaluationPseudo_map_obj (f : x ⟶ y) (Z : ↑(x.2.obj x.1)) :
    ((evaluationPseudo (C := C)).map f).toFunctor.obj Z
      = (y.2.map f.1).toFunctor.obj ((f.2.app x.1).toFunctor.obj Z) := rfl

/-- Component of `evaluationPseudo.map₂`. -/
lemma evaluationPseudo_map₂_app {f g : x ⟶ y} (η : f ⟶ g) (Z : ↑(x.2.obj x.1)) :
    ((evaluationPseudo (C := C)).map₂ η).toNatTrans.app Z
      = (y.2.map f.1).toFunctor.map ((η.2.as.app x.1).toNatTrans.app Z) ≫
        (y.2.map₂ η.1).toNatTrans.app ((g.2.app x.1).toFunctor.obj Z) := rfl

/-- Component of `evaluationPseudo.mapId`. -/
lemma evaluationPseudo_mapId_hom_app (x : C × (C ⥤ᵖ Cat.{w, v})) (Z : ↑(x.2.obj x.1)) :
    ((evaluationPseudo (C := C)).mapId x).hom.toNatTrans.app Z
      = (x.2.mapId x.1).hom.toNatTrans.app Z := rfl

/-- Component of `evaluationPseudo.mapComp`, with the strict-`Cat` associator identities
already cancelled: only the target's `mapComp` and the naturality inverse survive. -/
lemma evaluationPseudo_mapComp_hom_app {a b c : C × (C ⥤ᵖ Cat.{w, v})} (f : a ⟶ b) (g : b ⟶ c)
    (Z : ↑(a.2.obj a.1)) :
    ((evaluationPseudo (C := C)).mapComp f g).hom.toNatTrans.app Z
      = (c.2.mapComp f.1 g.1).hom.toNatTrans.app
            ((g.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z)) ≫
        (c.2.map g.1).toFunctor.map
            ((g.2.naturality f.1).inv.toNatTrans.app ((f.2.app a.1).toFunctor.obj Z)) := by
  dsimp only [evaluationPseudo]
  simp only [Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom, whiskerRightIso_hom,
    Cat.Hom.toNatTrans_comp, NatTrans.comp_app, Cat.whiskerLeft_toNatTrans,
    Cat.whiskerRight_toNatTrans, whiskerLeft_app, whiskerRight_app,
    Cat.associator_hom_toNatTrans_app, Cat.associator_inv_toNatTrans_app,
    Cat.Hom.comp_toFunctor, Functor.comp_obj, Category.id_comp, Category.comp_id]
  -- the `simp only` set above no longer reaches the `≪≫` chain on its own; a full `simp`
  -- does, and the residual is then definitional
  simp
  rfl

/-- Inverse form of `evaluationPseudo_mapComp_hom_app`. -/
lemma evaluationPseudo_mapComp_inv_app {a b c : C × (C ⥤ᵖ Cat.{w, v})} (f : a ⟶ b) (g : b ⟶ c)
    (Z : ↑(a.2.obj a.1)) :
    ((evaluationPseudo (C := C)).mapComp f g).inv.toNatTrans.app Z
      = (c.2.map g.1).toFunctor.map
            ((g.2.naturality f.1).hom.toNatTrans.app ((f.2.app a.1).toFunctor.obj Z)) ≫
        (c.2.mapComp f.1 g.1).inv.toNatTrans.app
            ((g.2.app a.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj Z)) := by
  dsimp only [evaluationPseudo]
  simp only [Iso.trans_inv, Iso.symm_inv, whiskerLeftIso_inv, whiskerRightIso_inv,
    Cat.Hom.toNatTrans_comp, NatTrans.comp_app, Cat.whiskerLeft_toNatTrans,
    Cat.whiskerRight_toNatTrans, whiskerLeft_app, whiskerRight_app,
    Cat.associator_hom_toNatTrans_app, Cat.associator_inv_toNatTrans_app,
    Cat.Hom.comp_toFunctor, Functor.comp_obj, Category.id_comp, Category.comp_id]
  simp
  rfl

end API

end CategoryTheory.Bicategory
