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
naturality.

Every one of the three squares is proved the same way, and it is worth naming the pattern.
The squares live in `Cat`, where both sides carry types mentioning `yonedaPairing.obj b`;
`rw` and `simp` cannot build a motive through the residual `Cat` instance diamond there and
report "simp made no progress" or "the target expression is not type-correct under the
implicit transparency level".  Rather than fight that, each side is descended to a point once
by a `rfl` bridge that *names* its distributed form, and the mathematics is then stated as a
`*_core` lemma in plain fibre terms -- with the evaluation point typed `↑(a.2.obj a.1)` and
the represented 1-cells typed bare, not through `Cat`'s coercion.  In the fibre the ordinary
tactics work normally.

The three cores, in increasing depth:

* `backwards_inner_core` / `backwards_app_core` -- the component isomorphism is natural in the
  represented 1-cell;
* `backwards_square_core` -- the strong-transformation naturality square;
* `backwards_natural_core` -- naturality in the evaluation point.
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
inverse forms of `mapComp_naturality_right` (for `b.2`) and `naturality_naturality` of the
strong transformation.

The evaluation point is typed `↑(a.2.obj a.1)` rather than `↑(yonedaEvaluation'.obj a)`; the
two are `rfl`-equal and the latter is no longer contaminating, but the bare spelling is what
makes the fibre `simp` set apply without a translation step. -/
lemma backwards_inner_core {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b) {α : Bᵒᵖ}
    {XX YY : unop α ⟶ unop b.1} (h : XX ⟶ YY) (X : ↑(a.2.obj a.1)) :
    (b.2.map₂ (op2 h)).toNatTrans.app
        ((b.2.map f.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj X)) ≫
      (b.2.mapComp f.1 (Quiver.Hom.op YY)).inv.toNatTrans.app
        ((f.2.app a.1).toFunctor.obj X) ≫
        (f.2.naturality (f.1 ≫ Quiver.Hom.op YY)).inv.toNatTrans.app X =
    (b.2.mapComp f.1 (Quiver.Hom.op XX)).inv.toNatTrans.app
        ((f.2.app a.1).toFunctor.obj X) ≫
      (f.2.naturality (f.1 ≫ Quiver.Hom.op XX)).inv.toNatTrans.app X ≫
        (f.2.app α).toFunctor.map ((a.2.map₂ (f.1 ◁ op2 h)).toNatTrans.app X) := by
  have h1 := Cat.Hom₂.congr_app
    (b.2.toOplax.mapComp_naturality_right f.1 (op2 h)) ((f.2.app a.1).toFunctor.obj X)
  have h2 := f.2.naturality_naturality_app (f.1 ◁ op2 h) X
  dsimp at h1 h2
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
  rw [← Category.assoc, s1]
  erw [Category.assoc, s2]

/-- The naturality square of `backwardsNaturalityIsoApp`'s component isomorphism, at a point.

One step more than `backwards_inner_core`: the component has a *third* factor, the conversion
`f.2.naturality f.1` that the new (Mathlib) diagonal introduces, and the 2-cell has to be slid
past it first.  That slide is plain `NatTrans` naturality; the rest is the inner core. -/
lemma backwards_app_core {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b) (X : ↑(a.2.obj a.1))
    {α : Bᵒᵖ} {XX YY : unop α ⟶ unop b.1} (h : XX ⟶ YY) :
    (b.2.map₂ (op2 h)).toNatTrans.app
          ((f.2.app b.1).toFunctor.obj ((a.2.map f.1).toFunctor.obj X)) ≫
        ((b.2.map (Quiver.Hom.op YY)).toFunctor.map
            ((f.2.naturality f.1).hom.toNatTrans.app X) ≫
          (b.2.mapComp f.1 (Quiver.Hom.op YY)).inv.toNatTrans.app
            ((f.2.app a.1).toFunctor.obj X) ≫
          (f.2.naturality (f.1 ≫ Quiver.Hom.op YY)).inv.toNatTrans.app X)
      = ((b.2.map (Quiver.Hom.op XX)).toFunctor.map
            ((f.2.naturality f.1).hom.toNatTrans.app X) ≫
          (b.2.mapComp f.1 (Quiver.Hom.op XX)).inv.toNatTrans.app
            ((f.2.app a.1).toFunctor.obj X) ≫
          (f.2.naturality (f.1 ≫ Quiver.Hom.op XX)).inv.toNatTrans.app X) ≫
        (f.2.app α).toFunctor.map ((a.2.map₂ (f.1 ◁ op2 h)).toNatTrans.app X) := by
  have hslide :
      (b.2.map (Quiver.Hom.op XX)).toFunctor.map
            ((f.2.naturality f.1).hom.toNatTrans.app X) ≫
          (b.2.map₂ (op2 h)).toNatTrans.app
            ((b.2.map f.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj X))
        = (b.2.map₂ (op2 h)).toNatTrans.app
              ((f.2.app b.1).toFunctor.obj ((a.2.map f.1).toFunctor.obj X)) ≫
            (b.2.map (Quiver.Hom.op YY)).toFunctor.map
              ((f.2.naturality f.1).hom.toNatTrans.app X) :=
    (b.2.map₂ (op2 h)).toNatTrans.naturality _
  rw [← reassoc_of% hslide]
  simp only [Category.assoc]
  exact congrArg (CategoryStruct.comp _) (backwards_inner_core f h X)

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
    (fun h ↦ backwards_app_core f X h))

/-- The component of `backwardsNaturalityIsoApp`, spelled out.  Holds by `rfl`; naming it is
what lets the two bridges below be stated in fibre terms. -/
lemma backwardsNaturalityIsoApp_hom_app {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b)
    (X : ↑(yonedaEvaluation'.obj a)) (α : Bᵒᵖ) (W : ↑((yoneda₀ (unop b.1)).obj α)) :
    (backwardsNaturalityIsoApp f X α).hom.toNatTrans.app W
      = (b.2.map (Quiver.Hom.op W)).toFunctor.map
            ((f.2.naturality f.1).hom.toNatTrans.app X) ≫
          (b.2.mapComp f.1 (Quiver.Hom.op W)).inv.toNatTrans.app
            ((f.2.app a.1).toFunctor.obj X) ≫
          (f.2.naturality (f.1 ≫ Quiver.Hom.op W)).inv.toNatTrans.app X := rfl

/-! ### The strong-transformation naturality square

Descending the square to a point is the whole difficulty: the two sides are `Cat` 2-cells whose
types mention `yonedaPairing.obj b`, and `rw`/`simp` cannot build a motive through the residual
`Cat` instance diamond there ("simp made no progress", "the target is not type-correct under the
implicit transparency level").  So the descent is done once, by two `rfl` bridges that name the
distributed form of each side, and the content is then stated as `backwards_square_core` in
plain fibre terms where the ordinary tactics work.
-/

/-- Whisker-left side of the naturality square, distributed at a point. -/
lemma backwards_square_lhs_app {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b)
    (X : ↑(yonedaEvaluation'.obj a)) {a₁ b₁ : Bᵒᵖ} (f₁ : a₁ ⟶ b₁)
    (ZZ : ↑((yoneda₀ (unop b.1)).obj a₁)) :
    ((yoneda₀ (unop b.1)).map f₁ ◁ (backwardsNaturalityIsoApp f X b₁).hom ≫
      (((yonedaLemmaBackwardsFunctor a ⋙ (yonedaPairing.map f).toFunctor).obj X).naturality
        f₁).hom).toNatTrans.app ZZ
      = ((b.2.map (Quiver.Hom.op ZZ ≫ f₁)).toFunctor.map
              ((f.2.naturality f.1).hom.toNatTrans.app X) ≫
            (b.2.mapComp f.1 (Quiver.Hom.op ZZ ≫ f₁)).inv.toNatTrans.app
              ((f.2.app a.1).toFunctor.obj X) ≫
            (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ ≫ f₁)).inv.toNatTrans.app X) ≫
        ((postcomp₂ f.1.unop ≫ (backwardsTrans a X ≫ f.2)).naturality f₁).hom.toNatTrans.app ZZ :=
  rfl

/-- Whisker-right side of the naturality square, distributed at a point. -/
lemma backwards_square_rhs_app {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b)
    (X : ↑(yonedaEvaluation'.obj a)) {a₁ b₁ : Bᵒᵖ} (f₁ : a₁ ⟶ b₁)
    (ZZ : ↑((yoneda₀ (unop b.1)).obj a₁)) :
    (((((yonedaEvaluation'.map f).toFunctor ⋙ yonedaLemmaBackwardsFunctor b).obj X).naturality
        f₁).hom ≫ (backwardsNaturalityIsoApp f X a₁).hom ▷ b.2.map f₁).toNatTrans.app ZZ
      = (b.2.mapComp (Quiver.Hom.op ZZ) f₁).hom.toNatTrans.app
          ((yonedaEvaluation'.map f).toFunctor.obj X) ≫
        (b.2.map f₁).toFunctor.map
          ((b.2.map (Quiver.Hom.op ZZ)).toFunctor.map
              ((f.2.naturality f.1).hom.toNatTrans.app X) ≫
            (b.2.mapComp f.1 (Quiver.Hom.op ZZ)).inv.toNatTrans.app
              ((f.2.app a.1).toFunctor.obj X) ≫
            (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app X) := rfl

/-- The composite's naturality, at a point, with its three factors named.  Holds by `rfl` once
`strongTrans_comp_naturality_app` has stripped the associator padding on the left. -/
lemma backwards_square_tail_app {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b)
    (X : ↑(yonedaEvaluation'.obj a)) {a₁ b₁ : Bᵒᵖ} (f₁ : a₁ ⟶ b₁)
    (ZZ : ↑((yoneda₀ (unop b.1)).obj a₁)) :
    ((backwardsTrans a X ≫ f.2).app b₁).toFunctor.map
          (((postcomp₂ f.1.unop).naturality f₁).hom.toNatTrans.app ZZ) ≫
        (f.2.app b₁).toFunctor.map
            (((backwardsTrans a X).naturality f₁).hom.toNatTrans.app
              (((postcomp₂ f.1.unop).app a₁).toFunctor.obj ZZ)) ≫
          (f.2.naturality f₁).hom.toNatTrans.app
            (((backwardsTrans a X).app a₁).toFunctor.obj
              (((postcomp₂ f.1.unop).app a₁).toFunctor.obj ZZ))
      = (f.2.app b₁).toFunctor.map
            ((a.2.map₂ (op2 (α_ f₁.unop ZZ f.1.unop).hom)).toNatTrans.app X) ≫
          (f.2.app b₁).toFunctor.map
              ((a.2.mapComp (f.1 ≫ Quiver.Hom.op ZZ) f₁).hom.toNatTrans.app X) ≫
            (f.2.naturality f₁).hom.toNatTrans.app
              ((a.2.map (f.1 ≫ Quiver.Hom.op ZZ)).toFunctor.obj X) := rfl

/-- The content of `backwards_naturality_square`, in the fibre.

Four coherences, in order: the outer `b.2.mapComp` slides past the diagonal's conversion
2-cell; `a.2`'s reassociating 2-cell is conjugated through `f.2`'s naturality
(`strongTrans_naturality_conj`), which leaves a pair to cancel; `b.2`'s own `mapComp`
associativity (`mapComp_assoc_app'`) is solved for the outer factor; and what remains is
`f.2`'s composition coherence in inverse form (`strongTrans_naturality_comp_inv_app`). -/
lemma backwards_square_core {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b) (X : ↑(a.2.obj a.1))
    {a₁ b₁ : Bᵒᵖ} (f₁ : a₁ ⟶ b₁) (ZZ : unop a₁ ⟶ unop b.1) :
    ((b.2.map (Quiver.Hom.op ZZ ≫ f₁)).toFunctor.map
          ((f.2.naturality f.1).hom.toNatTrans.app X) ≫
        (b.2.mapComp f.1 (Quiver.Hom.op ZZ ≫ f₁)).inv.toNatTrans.app
          ((f.2.app a.1).toFunctor.obj X) ≫
        (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ ≫ f₁)).inv.toNatTrans.app X) ≫
      (f.2.app b₁).toFunctor.map
          ((a.2.map₂ (op2 (α_ f₁.unop ZZ f.1.unop).hom)).toNatTrans.app X) ≫
        (f.2.app b₁).toFunctor.map
            ((a.2.mapComp (f.1 ≫ Quiver.Hom.op ZZ) f₁).hom.toNatTrans.app X) ≫
          (f.2.naturality f₁).hom.toNatTrans.app
            ((a.2.map (f.1 ≫ Quiver.Hom.op ZZ)).toFunctor.obj X)
    = (b.2.mapComp (Quiver.Hom.op ZZ) f₁).hom.toNatTrans.app
        ((f.2.app b.1).toFunctor.obj ((a.2.map f.1).toFunctor.obj X)) ≫
      (b.2.map f₁).toFunctor.map
        ((b.2.map (Quiver.Hom.op ZZ)).toFunctor.map
            ((f.2.naturality f.1).hom.toNatTrans.app X) ≫
          (b.2.mapComp f.1 (Quiver.Hom.op ZZ)).inv.toNatTrans.app
            ((f.2.app a.1).toFunctor.obj X) ≫
          (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app X) := by
  simp only [Functor.map_comp, Category.assoc]
  -- 1. slide the outer `mapComp` past the diagonal's conversion 2-cell
  have hslide :
      (b.2.map (Quiver.Hom.op ZZ ≫ f₁)).toFunctor.map
            ((f.2.naturality f.1).hom.toNatTrans.app X) ≫
          (b.2.mapComp (Quiver.Hom.op ZZ) f₁).hom.toNatTrans.app
            ((b.2.map f.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj X))
        = (b.2.mapComp (Quiver.Hom.op ZZ) f₁).hom.toNatTrans.app
              ((f.2.app b.1).toFunctor.obj ((a.2.map f.1).toFunctor.obj X)) ≫
            (b.2.map f₁).toFunctor.map
              ((b.2.map (Quiver.Hom.op ZZ)).toFunctor.map
                ((f.2.naturality f.1).hom.toNatTrans.app X)) :=
    (b.2.mapComp (Quiver.Hom.op ZZ) f₁).hom.toNatTrans.naturality _
  rw [← reassoc_of% hslide]
  refine congrArg (CategoryStruct.comp _) ?_
  -- 2. conjugate `a.2`'s reassociating 2-cell through `f.2`, then cancel the pair
  have hconj := strongTrans_naturality_conj f.2
      (v := f.1 ≫ (Quiver.Hom.op ZZ ≫ f₁)) (v' := (f.1 ≫ Quiver.Hom.op ZZ) ≫ f₁)
      (op2 (α_ f₁.unop ZZ f.1.unop).hom) X
  rw [hconj]
  have hcancel : (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ ≫ f₁)).inv.toNatTrans.app X ≫
      (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ ≫ f₁)).hom.toNatTrans.app X = 𝟙 _ := by simp
  simp only [Category.assoc]
  rw [reassoc_of% hcancel]
  -- 3. `b.2`'s own `mapComp` associativity, solved for the outer `mapComp`
  have hz : (b.2.mapComp (Quiver.Hom.op ZZ) f₁).hom.toNatTrans.app
        ((b.2.map f.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj X))
      = (b.2.mapComp f.1 (Quiver.Hom.op ZZ ≫ f₁)).inv.toNatTrans.app
            ((f.2.app a.1).toFunctor.obj X) ≫
          (b.2.map₂ (op2 (α_ f₁.unop ZZ f.1.unop).hom)).toNatTrans.app
            ((f.2.app a.1).toFunctor.obj X) ≫
          (b.2.mapComp (f.1 ≫ Quiver.Hom.op ZZ) f₁).hom.toNatTrans.app
            ((f.2.app a.1).toFunctor.obj X) ≫
          (b.2.map f₁).toFunctor.map
            ((b.2.mapComp f.1 (Quiver.Hom.op ZZ)).hom.toNatTrans.app
              ((f.2.app a.1).toFunctor.obj X)) :=
    (Iso.eq_inv_comp ((Cat.Hom.toNatIso (b.2.mapComp f.1 (Quiver.Hom.op ZZ ≫ f₁))).app
      ((f.2.app a.1).toFunctor.obj X))).mpr
        (mapComp_assoc_app' b.2 (Quiver.Hom.op ZZ) f₁ f.1.unop ((f.2.app a.1).toFunctor.obj X))
  rw [hz]
  simp only [Category.assoc]
  rw [map_comp_cancel_assoc (b.2.map f₁).toFunctor
    ((b.2.mapComp f.1 (Quiver.Hom.op ZZ)).hom.toNatTrans.app ((f.2.app a.1).toFunctor.obj X))
    ((b.2.mapComp f.1 (Quiver.Hom.op ZZ)).inv.toNatTrans.app ((f.2.app a.1).toFunctor.obj X))
    (by simp)]
  -- 4. the two leading factors now agree
  refine congrArg (CategoryStruct.comp _) (congrArg (CategoryStruct.comp _) ?_)
  -- 5. what is left is `f.2`'s composition coherence, inverted
  refine (Iso.inv_comp_eq ((Cat.Hom.toNatIso
    (b.2.mapComp (f.1 ≫ Quiver.Hom.op ZZ) f₁)).app ((f.2.app a.1).toFunctor.obj X))).mp ?_
  change (b.2.mapComp (f.1 ≫ Quiver.Hom.op ZZ) f₁).inv.toNatTrans.app
      ((f.2.app a.1).toFunctor.obj X) ≫ _ = _
  rw [strongTrans_naturality_comp_inv_app_assoc]
  rw [map_comp_cancel_assoc (f.2.app b₁).toFunctor
    ((a.2.mapComp (f.1 ≫ Quiver.Hom.op ZZ) f₁).inv.toNatTrans.app X)
    ((a.2.mapComp (f.1 ≫ Quiver.Hom.op ZZ) f₁).hom.toNatTrans.app X) (by simp)]
  simp

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
  refine Eq.trans (backwards_square_lhs_app f X f₁ ZZ)
    (Eq.trans ?_ (backwards_square_rhs_app f X f₁ ZZ).symm)
  rw [strongTrans_comp_naturality_app, strongTrans_comp_naturality_app]
  refine Eq.trans (congrArg (CategoryStruct.comp _) (backwards_square_tail_app f X f₁ ZZ)) ?_
  exact backwards_square_core f X f₁ ZZ

/-- The naturality iso of `yonedaLemmaBackwards` at `f : a ⟶ b`, componentwise. -/
def backwardsNaturalityIso {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b)
    (X : ↑(yonedaEvaluation'.obj a)) :
    ((yonedaEvaluation'.map f).toFunctor ⋙ yonedaLemmaBackwardsFunctor b).obj X ≅
      (yonedaLemmaBackwardsFunctor a ⋙ (yonedaPairing.map f).toFunctor).obj X :=
  StrongTrans.isoMk (fun α ↦ backwardsNaturalityIsoApp f X α)
    (fun f₁ ↦ backwards_naturality_square f X f₁)

/-! ### Naturality in the fibre point

Same shape as the square above: two `rfl` bridges take the modification equation down to a
fibre equation, and `backwards_natural_core` is the content.  Here the content is only three
`NatTrans` naturality slides -- one for each factor of the component iso -- because the
1-cell is fixed and no coherence of `b.2` is involved.
-/

/-- Left-hand side of the naturality-in-`X` square, distributed at a point. -/
lemma backwards_natural_lhs_app {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b)
    {X Y : ↑(yonedaEvaluation'.obj a)} (m : X ⟶ Y) {γ : Bᵒᵖ}
    (ZZ : ↑((yoneda₀ (unop b.1)).obj γ)) :
    (((((yonedaEvaluation'.map f).toFunctor ⋙ yonedaLemmaBackwardsFunctor b).map m ≫
        (backwardsNaturalityIso f Y).hom).as.app γ).toNatTrans).app ZZ
      = (b.2.map (Quiver.Hom.op ZZ)).toFunctor.map
            ((f.2.app b.1).toFunctor.map ((a.2.map f.1).toFunctor.map m)) ≫
          (backwardsNaturalityIsoApp f Y γ).hom.toNatTrans.app ZZ := rfl

/-- Right-hand side of the naturality-in-`X` square, distributed at a point. -/
lemma backwards_natural_rhs_app {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b)
    {X Y : ↑(yonedaEvaluation'.obj a)} (m : X ⟶ Y) {γ : Bᵒᵖ}
    (ZZ : ↑((yoneda₀ (unop b.1)).obj γ)) :
    ((((backwardsNaturalityIso f X).hom ≫
        (yonedaLemmaBackwardsFunctor a ⋙ (yonedaPairing.map f).toFunctor).map
          m).as.app γ).toNatTrans).app ZZ
      = (backwardsNaturalityIsoApp f X γ).hom.toNatTrans.app ZZ ≫
          (f.2.app γ).toFunctor.map
            ((a.2.map (f.1 ≫ Quiver.Hom.op ZZ)).toFunctor.map m) := rfl

/-- The content of `backwards_naturality_iso_natural`, in the fibre: each of the three factors
of `backwardsNaturalityIsoApp`'s component is natural in the evaluation point, so the square
is the three slides composed. -/
lemma backwards_natural_core {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b)
    {X Y : ↑(a.2.obj a.1)} (m : X ⟶ Y) {γ : Bᵒᵖ} (ZZ : unop γ ⟶ unop b.1) :
    (b.2.map (Quiver.Hom.op ZZ)).toFunctor.map
        ((f.2.app b.1).toFunctor.map ((a.2.map f.1).toFunctor.map m)) ≫
      ((b.2.map (Quiver.Hom.op ZZ)).toFunctor.map
          ((f.2.naturality f.1).hom.toNatTrans.app Y) ≫
        (b.2.mapComp f.1 (Quiver.Hom.op ZZ)).inv.toNatTrans.app
          ((f.2.app a.1).toFunctor.obj Y) ≫
        (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app Y)
    = ((b.2.map (Quiver.Hom.op ZZ)).toFunctor.map
          ((f.2.naturality f.1).hom.toNatTrans.app X) ≫
        (b.2.mapComp f.1 (Quiver.Hom.op ZZ)).inv.toNatTrans.app
          ((f.2.app a.1).toFunctor.obj X) ≫
        (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app X) ≫
      (f.2.app γ).toFunctor.map ((a.2.map (f.1 ≫ Quiver.Hom.op ZZ)).toFunctor.map m) := by
  have hnat : (f.2.app b.1).toFunctor.map ((a.2.map f.1).toFunctor.map m) ≫
        (f.2.naturality f.1).hom.toNatTrans.app Y
      = (f.2.naturality f.1).hom.toNatTrans.app X ≫
        (b.2.map f.1).toFunctor.map ((f.2.app a.1).toFunctor.map m) :=
    (f.2.naturality f.1).hom.toNatTrans.naturality m
  have h2 : (b.2.map (Quiver.Hom.op ZZ)).toFunctor.map
          ((b.2.map f.1).toFunctor.map ((f.2.app a.1).toFunctor.map m)) ≫
        (b.2.mapComp f.1 (Quiver.Hom.op ZZ)).inv.toNatTrans.app
          ((f.2.app a.1).toFunctor.obj Y)
      = (b.2.mapComp f.1 (Quiver.Hom.op ZZ)).inv.toNatTrans.app
          ((f.2.app a.1).toFunctor.obj X) ≫
        (b.2.map (f.1 ≫ Quiver.Hom.op ZZ)).toFunctor.map ((f.2.app a.1).toFunctor.map m) :=
    (b.2.mapComp f.1 (Quiver.Hom.op ZZ)).inv.toNatTrans.naturality _
  have h3 : (b.2.map (f.1 ≫ Quiver.Hom.op ZZ)).toFunctor.map
          ((f.2.app a.1).toFunctor.map m) ≫
        (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app Y
      = (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app X ≫
        (f.2.app γ).toFunctor.map ((a.2.map (f.1 ≫ Quiver.Hom.op ZZ)).toFunctor.map m) :=
    (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.naturality m
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, hnat, Functor.map_comp_assoc, reassoc_of% h2, h3]

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
  exact Eq.trans (backwards_natural_lhs_app f f₁ ZZ)
    (Eq.trans (backwards_natural_core f f₁ ZZ) (backwards_natural_rhs_app f f₁ ZZ).symm)

end Biyoneda
