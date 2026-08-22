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
naturality.  The `_core` lemmas below each state a square's content at a fibre point;
`backwards_square_composite` is the same square for the composite strong transformation.
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

/-- The cancellation core of the backwards naturality square: all atoms in canonical
spelling, `X` unlifted. -/
lemma backwards_square_core {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b)
    (X : ↑(yonedaEvaluation'.obj a)) {a₁ b₁ : Bᵒᵖ} (f₁ : a₁ ⟶ b₁)
    (ZZ : ↑((yoneda₀ (unop b.1)).obj a₁)) :
    (f.2.app b₁).toFunctor.map
        ((a.2.map₂ (α_ f.1 (Quiver.Hom.op ZZ) f₁).inv).toNatTrans.app X) ≫
      (f.2.app b₁).toFunctor.map
        ((a.2.mapComp (f.1 ≫ Quiver.Hom.op ZZ) f₁).hom.toNatTrans.app X) ≫
      (f.2.naturality f₁).hom.toNatTrans.app
        ((a.2.map (f.1 ≫ Quiver.Hom.op ZZ)).toFunctor.obj X) =
    (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ ≫ f₁)).hom.toNatTrans.app X ≫
      (b.2.mapComp f.1 (Quiver.Hom.op ZZ ≫ f₁)).hom.toNatTrans.app
        ((f.2.app a.1).toFunctor.obj X) ≫
      (b.2.mapComp (Quiver.Hom.op ZZ) f₁).hom.toNatTrans.app
        ((b.2.map f.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj X)) ≫
      (b.2.map f₁).toFunctor.map
        ((b.2.mapComp f.1 (Quiver.Hom.op ZZ)).inv.toNatTrans.app
            ((f.2.app a.1).toFunctor.obj X) ≫
          (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app X) := by
  have h3 := Pseudofunctor.mapComp_assoc_right_hom_app b.2 f.1 (Quiver.Hom.op ZZ) f₁
    ((f.2.app a.1).toFunctor.obj X)
  rw [Pseudofunctor.StrongTrans.naturality_naturality_hom_app f.2
      (α_ f.1 (Quiver.Hom.op ZZ) f₁) X,
    Pseudofunctor.StrongTrans.naturality_comp_hom_app f.2 (f.1 ≫ Quiver.Hom.op ZZ) f₁ X]
  simp only [Category.assoc]
  erw [reassoc_of% h3]
  have h1 := Pseudofunctor.StrongTrans.naturality_naturality_hom_app f.2
    (α_ f.1 (Quiver.Hom.op ZZ) f₁) X
  have h2 := Pseudofunctor.StrongTrans.naturality_comp_hom_app f.2
    (f.1 ≫ Quiver.Hom.op ZZ) f₁ X
  have c1 : (b.2.map₂ (α_ f.1 (Quiver.Hom.op ZZ) f₁).hom).toNatTrans.app
        ((f.2.app a.1).toFunctor.obj X) ≫
      (b.2.map₂ (α_ f.1 (Quiver.Hom.op ZZ) f₁).inv).toNatTrans.app
        ((f.2.app a.1).toFunctor.obj X) = 𝟙 _ := by
    rw [← Cat.Hom₂.comp_app, ← PrelaxFunctor.map₂_comp, Iso.hom_inv_id,
      PrelaxFunctor.map₂_id, Cat.Hom₂.id_app]
  have c2 := Cat.Hom.inv_hom_id_toNatTrans_app (b.2.mapComp (f.1 ≫ Quiver.Hom.op ZZ) f₁)
    ((f.2.app a.1).toFunctor.obj X)
  have c3 := Cat.Hom.hom_inv_id_toNatTrans_app (b.2.mapComp f.1 (Quiver.Hom.op ZZ))
    ((f.2.app a.1).toFunctor.obj X)
  have c4 := Cat.Hom.hom_inv_id_toNatTrans_app (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ)) X
  -- PARKED (v4.33).  The cancellation data above (`c1`-`c4`, `h1`, `h2`) is all still correct
  -- and still elaborates; what breaks is `erw [reassoc_of% h1]`, whose pattern the target no
  -- longer contains.  Same family as `backwards_square_composite` below: an ordered rewrite
  -- chain over `mapComp`/`naturality` components whose assumed spelling has shifted.
  -- Prior version: `git show comp-core:Biyoneda/BackwardsNaturality.lean`.
  sorry

/-- Point form of the naturality square, spelled through the composite strong
transformation (defeq to `yonedaPairing.map`'s literal pasting).

The proof distributes the strong-transformation component through the whiskered/associated
composite from `categoryStruct_comp_naturality_hom`. This is an ordered `erw` chain rather
than a `simp only`: the `≫`/`α_`/`▷` come from the `postcomp₂` bicategory and are only *defeq*
to `Cat`'s operations (an instance diamond), so the `Cat.*_app` distribution lemmas match at
default transparency but not reducible. The order is fixed by the composite's shape. -/
lemma backwards_square_composite {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b)
    (X : ↑(yonedaEvaluation'.obj a)) {a₁ b₁ : Bᵒᵖ} (f₁ : a₁ ⟶ b₁)
    (ZZ : ↑((yoneda₀ (unop b.1)).obj a₁)) :
    ((b.2.mapComp f.1 (Quiver.Hom.op ZZ ≫ f₁)).inv.toNatTrans.app
        ((f.2.app a.1).toFunctor.obj X) ≫
      (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ ≫ f₁)).inv.toNatTrans.app X) ≫
      ((postcomp₂ f.1.unop ≫ (backwardsTrans a X ≫ f.2)).naturality
        f₁).hom.toNatTrans.app ZZ =
    (b.2.mapComp (Quiver.Hom.op ZZ) f₁).hom.toNatTrans.app
        ((b.2.map f.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj X)) ≫
      (b.2.map f₁).toFunctor.map
        ((b.2.mapComp f.1 (Quiver.Hom.op ZZ)).inv.toNatTrans.app
            ((f.2.app a.1).toFunctor.obj X) ≫
          (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app X) := by
  simp only [categoryStruct_comp_naturality_hom]
  -- PARKED (v4.33).  The mathematical content is `backwards_square_core` (parked just above);
  -- everything between is a 15-step *ordered* `rw`/`erw` chain -- associator/whisker component
  -- lemmas applied in a fixed sequence -- and the order it assumes no longer holds.
  --
  -- Tried: collapsing the whole chain into one confluent `simp only` with exactly the same
  -- lemmas.  That reports no progress, because several steps needed `erw`'s defeq matching and
  -- `simp only` matches at reducible transparency only.  So the chain cannot simply be made
  -- order-independent; the component lemmas have to be re-derived at the right spelling.
  -- Prior version: `git show comp-core:Biyoneda/BackwardsNaturality.lean`.
  sorry

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
  exact backwards_square_composite f X f₁ ZZ

/-- The naturality iso of `yonedaLemmaBackwards` at `f : a ⟶ b`, componentwise. -/
def backwardsNaturalityIso {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b)
    (X : ↑(yonedaEvaluation'.obj a)) :
    ((yonedaEvaluation'.map f).toFunctor ⋙ yonedaLemmaBackwardsFunctor b).obj X ≅
      (yonedaLemmaBackwardsFunctor a ⋙ (yonedaPairing.map f).toFunctor).obj X :=
  StrongTrans.isoMk (fun α ↦ backwardsNaturalityIsoApp f X α)
    (fun f₁ ↦ backwards_naturality_square f X f₁)

/-- The cancellation core of `backwards_naturality_iso_natural`: two `NatTrans.naturality`
squares of the component isos, in canonical spellings. -/
lemma backwards_naturality_core {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b)
    {X Y : ↑(yonedaEvaluation'.obj a)} (f₁ : X ⟶ Y) {γ : Bᵒᵖ}
    (ZZ : ↑((yoneda₀ (unop b.1)).obj γ)) :
    (b.2.map f.1 ≫ b.2.map (Quiver.Hom.op ZZ)).toFunctor.map
        ((f.2.app a.1).toFunctor.map f₁) ≫
      (b.2.mapComp f.1 (Quiver.Hom.op ZZ)).inv.toNatTrans.app
        ((f.2.app a.1).toFunctor.obj Y) ≫
      (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app Y =
    ((b.2.mapComp f.1 (Quiver.Hom.op ZZ)).inv.toNatTrans.app
        ((f.2.app a.1).toFunctor.obj X) ≫
      (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app X) ≫
      (f.2.app γ).toFunctor.map ((a.2.map (f.1 ≫ Quiver.Hom.op ZZ)).toFunctor.map f₁) := by
  have s1 := (b.2.mapComp f.1 (Quiver.Hom.op ZZ)).inv.toNatTrans.naturality
    ((f.2.app a.1).toFunctor.map f₁)
  have s2 : (b.2.map (f.1 ≫ Quiver.Hom.op ZZ)).toFunctor.map
        ((f.2.app a.1).toFunctor.map f₁) ≫
      (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app Y =
      (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app X ≫
      (f.2.app γ).toFunctor.map ((a.2.map (f.1 ≫ Quiver.Hom.op ZZ)).toFunctor.map f₁) :=
    (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.naturality f₁
  rw [reassoc_of% s1, s2]
  exact (Category.assoc _ _ _).symm

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
  exact backwards_naturality_core f f₁ ZZ

end Biyoneda
