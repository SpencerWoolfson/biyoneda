/-
Copyright (c) 2026 Spencer Woolfson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Spencer Woolfson
-/
import Biyoneda.BackwardsFunctor

/-!
# The backward direction: the naturality isomorphism

Everything needed to build `backwardsNaturalityIso`, the naturality isomorphism of
`yonedaLemmaBackwards` at a 1-cell `f`, and to show it natural.

The chain is inside-out: `backwardsNaturalityIsoApp` is the component at one `α : Bᵒᵖ`,
`backwardsNaturalityIso` assembles those, and `backwards_naturality_iso_natural` is its
naturality.  `backwards_inner_core` states the innermost square's content at a fibre point.
-/

namespace Biyoneda

open CategoryTheory Bicategory Bicategory.Opposite Opposite Pseudofunctor StrongTrans Functor
open scoped Pseudofunctor.StrongTrans

universe u v w v₁ v₂ u₁ u₂

attribute [local instance] uliftCategory


variable {B : Type u} [Bicategory.{w, v} B]

universe w₁

/-- The inner naturality square for `yonedaLemmaBackwards`: sliding a 2-cell of the
represented object past the `mapComp` and `naturality` coherence isos.  Assembled from the
inverse forms of `mapComp_naturality_right` (for both pseudofunctors) and
`naturality_naturality` of the strong transformation. -/
lemma backwards_inner_core {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b) {α : Bᵒᵖ}
    {XX YY : ↑((yoneda₀ (unop b.1)).obj α)} (h : XX ⟶ YY) (X : ↑(yonedaEvaluation'.obj a)) :
    (b.2.map₂ (op2 h)).toNatTrans.app
        ((b.2.map f.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj X)) ≫
      (b.2.mapComp f.1 (Quiver.Hom.op YY)).inv.toNatTrans.app
        ((f.2.app a.1).toFunctor.obj X) ≫
        (f.2.naturality (f.1 ≫ Quiver.Hom.op YY)).inv.toNatTrans.app X =
    ((b.2.mapComp f.1 (Quiver.Hom.op XX)).inv.toNatTrans.app
        ((f.2.app a.1).toFunctor.obj X) ≫
        (f.2.naturality (f.1 ≫ Quiver.Hom.op XX)).inv.toNatTrans.app X) ≫
      (f.2.app α).toFunctor.map
        (((a.2.mapComp f.1 (Quiver.Hom.op XX)).hom ≫
            a.2.map f.1 ◁ a.2.map₂ (op2 h) ≫
              (a.2.mapComp f.1 (Quiver.Hom.op YY)).inv).toNatTrans.app X) := by
  have h1 := Cat.Hom₂.congr_app
    (b.2.toOplax.mapComp_naturality_right f.1 (op2 h)) ((f.2.app a.1).toFunctor.obj X)
  have h2 := f.2.naturality_naturality_app (f.1 ◁ op2 h) X
  have h3 := Cat.Hom₂.congr_app
    (a.2.toOplax.mapComp_naturality_right f.1 (op2 h)) X
  dsimp at h1 h2 h3
  -- s1: slide map₂(op2 h) past the b.2.mapComp iso (inverse form of h1)
  have s1 : (b.2.map₂ (op2 h)).toNatTrans.app
        ((b.2.map f.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj X)) ≫
      (b.2.mapComp f.1 (Quiver.Hom.op YY)).inv.toNatTrans.app
        ((f.2.app a.1).toFunctor.obj X) =
      (b.2.mapComp f.1 (Quiver.Hom.op XX)).inv.toNatTrans.app
        ((f.2.app a.1).toFunctor.obj X) ≫
      (b.2.map₂ (f.1 ◁ op2 h)).toNatTrans.app ((f.2.app a.1).toFunctor.obj X) := by
    apply (Iso.comp_inv_eq ((Cat.Hom.toNatIso
      (b.2.mapComp f.1 (Quiver.Hom.op YY))).app ((f.2.app a.1).toFunctor.obj X))).mpr
    erw [Category.assoc]
    apply (Iso.eq_inv_comp ((Cat.Hom.toNatIso
      (b.2.mapComp f.1 (Quiver.Hom.op XX))).app ((f.2.app a.1).toFunctor.obj X))).mpr
    exact h1.symm
  -- s2: slide b.2.map₂ (f.1 ◁ op2 h) past f.2.naturality (inverse form of h2)
  have s2 : (b.2.map₂ (f.1 ◁ op2 h)).toNatTrans.app ((f.2.app a.1).toFunctor.obj X) ≫
      (f.2.naturality (f.1 ≫ Quiver.Hom.op YY)).inv.toNatTrans.app X =
      (f.2.naturality (f.1 ≫ Quiver.Hom.op XX)).inv.toNatTrans.app X ≫
      (f.2.app α).toFunctor.map ((a.2.map₂ (f.1 ◁ op2 h)).toNatTrans.app X) := by
    apply (Iso.comp_inv_eq ((Cat.Hom.toNatIso
      (f.2.naturality (f.1 ≫ Quiver.Hom.op YY))).app X)).mpr
    erw [Category.assoc]
    apply (Iso.eq_inv_comp ((Cat.Hom.toNatIso
      (f.2.naturality (f.1 ≫ Quiver.Hom.op XX))).app X)).mpr
    exact h2.symm
  -- s3: the conjugated 2-cell collapses (component form of h3)
  have s3 : ((a.2.mapComp f.1 (Quiver.Hom.op XX)).hom ≫
        a.2.map f.1 ◁ a.2.map₂ (op2 h) ≫
          (a.2.mapComp f.1 (Quiver.Hom.op YY)).inv).toNatTrans.app X =
      (a.2.map₂ (f.1 ◁ op2 h)).toNatTrans.app X := by
    simp only [Cat.Hom.toNatTrans_comp, NatTrans.comp_app]
    rw [← Category.assoc]
    apply (Iso.comp_inv_eq ((Cat.Hom.toNatIso
      (a.2.mapComp f.1 (Quiver.Hom.op YY))).app X)).mpr
    exact h3.symm
  rw [← Category.assoc, s1]
  erw [Category.assoc, s2]
  rw [← s3]
  erw [← Category.assoc]

/-- Component (at `α`) of the naturality iso of `yonedaLemmaBackwards` at `f : a ⟶ b`. -/
def backwardsNaturalityIsoApp {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b)
    (X : ↑(yonedaEvaluation'.obj a)) (α : Bᵒᵖ) :
    (((yonedaEvaluation'.map f).toFunctor ⋙ yonedaLemmaBackwardsFunctor b).obj X).app α ≅
      ((yonedaLemmaBackwardsFunctor a ⋙ (yonedaPairing.map f).toFunctor).obj X).app α :=
  Cat.Hom.isoMk (NatIso.ofComponents
    (fun XX ↦
      (b.2.map XX.op).toFunctor.mapIso
          ((Cat.Hom.toNatIso (f.2.naturality f.1)).app X) ≪≫
        (Cat.Hom.toNatIso (b.2.mapComp f.1 XX.op).symm).app
          ((f.2.app a.1).toFunctor.obj X) ≪≫
        (Cat.Hom.toNatIso (f.2.naturality (f.1 ≫ XX.op))).symm.app X)
    (fun {XX YY} h ↦ by
      -- PARKED (v4.33).  `backwards_inner_core` (proved, just above) is the content.  The
      -- `dsimp [yonedaEvaluation', Functor.comp]` unfolds far enough that the goal's left-hand
      -- side arrives as `(b.2.map₂ (op2 h)).toNatTrans.app _` rather than in the
      -- `map₂ (_ ◁ _)` shape `Pseudofunctor.map₂_whisker_left` needs, and the right-hand side
      -- becomes a large un-normalised `postcomposingCat`/`yoneda.op.prod` blob.  Keeping
      -- `yonedaEvaluation'` folded is the direction to try (it is what fixed the analogous
      -- failures in TransIntoCats and Gadgets), but here the `dsimp` is load-bearing for the
      -- `exact` that follows, so the two need reconciling together.
      dsimp [yonedaEvaluation', Functor.comp]
      sorry))

/-- The strong-transformation naturality square for `backwardsNaturalityIsoApp`. -/
lemma backwards_naturality_square {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b)
    (X : ↑(yonedaEvaluation'.obj a)) {a₁ b₁ : Bᵒᵖ} (f₁ : a₁ ⟶ b₁) :
    (yoneda₀ (unop b.1)).map f₁ ◁ (backwardsNaturalityIsoApp f X b₁).hom ≫
      (((yonedaLemmaBackwardsFunctor a ⋙ (yonedaPairing.map f).toFunctor).obj X).naturality
        f₁).hom =
    ((((yonedaEvaluation'.map f).toFunctor ⋙ yonedaLemmaBackwardsFunctor b).obj X).naturality
        f₁).hom ≫ (backwardsNaturalityIsoApp f X a₁).hom ▷ b.2.map f₁ := by
  apply Cat.Hom₂.ext_app
  intro ZZ
  -- PARKED (diagonal switch).  The pre-switch `_core` lemmas that used to feed this were deleted
  -- on 2026-08-30: the component of `backwardsNaturalityIsoApp` now has three factors, not two,
  -- since `yonedaEvaluation'.map f` is `a.2.map f.1 ≫ f.2.app b.1` rather than
  -- `f.2.app a.1 ≫ b.2.map f.1`, with `f.2.naturality f.1` as the conversion.  Porting them by
  -- hand yields statements that are subtly wrong and only report it as a defeq failure.
  --
  -- The route in is `StrongTransIntoCats.ofStrongTrans` (not yet written) plus
  -- `ModificationIntoCats.isoMk`, which states this square at a point.  See
  -- `notes/intocats_audit_2026-08-30.md`.
  sorry

/-- The naturality iso of `yonedaLemmaBackwards` at `f : a ⟶ b`, componentwise. -/
def backwardsNaturalityIso {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b)
    (X : ↑(yonedaEvaluation'.obj a)) :
    ((yonedaEvaluation'.map f).toFunctor ⋙ yonedaLemmaBackwardsFunctor b).obj X ≅
      (yonedaLemmaBackwardsFunctor a ⋙ (yonedaPairing.map f).toFunctor).obj X :=
  StrongTrans.isoMk (fun α ↦ backwardsNaturalityIsoApp f X α)
    (fun f₁ ↦ backwards_naturality_square f X f₁)

/-- Naturality (in `X`) of `backwardsNaturalityIso`. -/
lemma backwards_naturality_iso_natural {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b)
    {X Y : ↑(yonedaEvaluation'.obj a)} (f₁ : X ⟶ Y) :
    ((yonedaEvaluation'.map f).toFunctor ⋙ yonedaLemmaBackwardsFunctor b).map f₁ ≫
      (backwardsNaturalityIso f Y).hom =
    (backwardsNaturalityIso f X).hom ≫
      (yonedaLemmaBackwardsFunctor a ⋙ (yonedaPairing.map f).toFunctor).map f₁ := by
  apply homCategory.ext
  intro γ
  apply Cat.Hom₂.ext_app
  intro ZZ
  erw [homCategory_comp_as_app, homCategory_comp_as_app]
  dsimp only [backwardsNaturalityIso]
  -- PARKED (diagonal switch).  The pre-switch `_core` lemmas that used to feed this were deleted
  -- on 2026-08-30: the component of `backwardsNaturalityIsoApp` now has three factors, not two,
  -- since `yonedaEvaluation'.map f` is `a.2.map f.1 ≫ f.2.app b.1` rather than
  -- `f.2.app a.1 ≫ b.2.map f.1`, with `f.2.naturality f.1` as the conversion.  Porting them by
  -- hand yields statements that are subtly wrong and only report it as a defeq failure.
  --
  -- The route in is `StrongTransIntoCats.ofStrongTrans` (not yet written) plus
  -- `ModificationIntoCats.isoMk`, which states this square at a point.  See
  -- `notes/intocats_audit_2026-08-30.md`.
  sorry

end Biyoneda
