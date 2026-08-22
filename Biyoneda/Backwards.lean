/-
Copyright (c) 2026 Spencer Woolfson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Spencer Woolfson
-/
import Biyoneda.BackwardsNaturality

/-!
# The backward direction: transport along the pseudofunctor

`yonedaLemmaBackwards : yonedaEvaluation ⟶ yonedaPairing` sends an object `s : F.obj b` to the
strong transformation `(a, f) ↦ (F.map f).obj s`.

Like the forward direction it is assembled by a lift — `StrongTransIntoCats.liftDom`, the
domain-side gadget — from `yonedaLemmaBackwardsData`.  Everything below is therefore stated in
the unlifted fibre `yonedaEvaluation'`, and no `ULift` appears in any proof.

This file holds only the last layer: the two remaining coherence ingredients
(`backwards_map_comp`, `backwards_naturality_naturality_core`), the pointwise data, and the
transformation itself.  The component functor is in `Biyoneda/BackwardsFunctor.lean` and the
naturality isomorphism in `Biyoneda/BackwardsNaturality.lean`.
-/

namespace Biyoneda

open CategoryTheory Bicategory Bicategory.Opposite Opposite Pseudofunctor StrongTrans Functor
open scoped Pseudofunctor.StrongTrans

universe u v w v₁ v₂ u₁ u₂

attribute [local instance] uliftCategory


variable {B : Type u} [Bicategory.{w, v} B]

universe w₁

/-- Component reduction for the backwards functor's `.map`: it is just the pseudofunctor's
action on the fibre morphism.  Holds by `rfl`, but must be applied with `erw` (the
`StrongTrans` `homCategory` diamond). -/
lemma backwards_map_comp (x : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})) {A₀ B₀ : ↑(yonedaEvaluation'.obj x)}
    (m : A₀ ⟶ B₀) (c : Bᵒᵖ) (W : ↑((yoneda₀ (unop x.1)).obj c)) :
    (((((yonedaLemmaBackwardsFunctor x).map m).as.app c).toNatTrans).app W)
      = (x.2.map (Quiver.Hom.op W)).toFunctor.map m := rfl

/-- The reduced fibre-morphism core of `naturality_naturality` for `yonedaLemmaBackwards`:
the 2-cell coherence descended to a single fibre `↑(b.2.obj γ)`.  Using the composite 2-cell
`θ = η.1 ▷ ZZ.op` linearizes the proof into three inverse slides — the `b.2.mapComp`
naturality (`hmc`), the strong-transformation `naturality_naturality` (`hnn`), and the
modification naturality of `η.2` (`hmod`) — plus the `mapComp`-inverse point transport. -/
lemma backwards_naturality_naturality_core {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} {f g : a ⟶ b}
    (η : f ⟶ g) (x : ↑(yonedaEvaluation'.obj a)) {γ : Bᵒᵖ}
    (ZZ : ↑((yoneda₀ (unop b.1)).obj γ)) :
    (b.2.map (Quiver.Hom.op ZZ)).toFunctor.map
        ((b.2.map f.1).toFunctor.map ((η.2.as.app a.1).toNatTrans.app x) ≫
          (b.2.map₂ η.1).toNatTrans.app ((g.2.app a.1).toFunctor.obj x)) ≫
      (b.2.mapComp g.1 (Quiver.Hom.op ZZ)).inv.toNatTrans.app ((g.2.app a.1).toFunctor.obj x) ≫
        (g.2.naturality (g.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app x =
    ((b.2.mapComp f.1 (Quiver.Hom.op ZZ)).inv.toNatTrans.app ((f.2.app a.1).toFunctor.obj x) ≫
        (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app x) ≫
      (f.2.app γ).toFunctor.map ((a.2.map₂ (op2 (ZZ ◁ η.1.unop2))).toNatTrans.app x) ≫
        (η.2.as.app γ).toNatTrans.app
          ((a.2.map (Quiver.Hom.op
            ((postcomp (unop γ) g.1.unop).toCatHom.toFunctor.obj ZZ))).toFunctor.obj x) := by
  -- The three coherences, component-distributed (θ = η.1 ▷ ZZ.op linearizes the chain)
  have hmc := Cat.Hom₂.congr_app
    (b.2.toOplax.mapComp_naturality_left η.1 (Quiver.Hom.op ZZ)) ((g.2.app a.1).toFunctor.obj x)
  have hnn := g.2.naturality_naturality_app (η.1 ▷ Quiver.Hom.op ZZ) x
  have hmod := modification_naturality_app η.2 (f.1 ≫ Quiver.Hom.op ZZ) x
  simp only [Cat.Hom.toNatTrans_comp, NatTrans.comp_app,
    Cat.whiskerRight_toNatTrans, whiskerRight_app] at hmc hnn hmod
  -- hmc_inv: slide map₂ η.1 past the b.2.mapComp iso (inverse form), point G_ax
  have hmc_inv : (b.2.map (Quiver.Hom.op ZZ)).toFunctor.map
        ((b.2.map₂ η.1).toNatTrans.app ((g.2.app a.1).toFunctor.obj x)) ≫
      (b.2.mapComp g.1 (Quiver.Hom.op ZZ)).inv.toNatTrans.app ((g.2.app a.1).toFunctor.obj x) =
      (b.2.mapComp f.1 (Quiver.Hom.op ZZ)).inv.toNatTrans.app ((g.2.app a.1).toFunctor.obj x) ≫
        (b.2.map₂ (η.1 ▷ Quiver.Hom.op ZZ)).toNatTrans.app ((g.2.app a.1).toFunctor.obj x) := by
    apply (Iso.comp_inv_eq ((Cat.Hom.toNatIso (b.2.mapComp g.1 (Quiver.Hom.op ZZ))).app
      ((g.2.app a.1).toFunctor.obj x))).mpr
    erw [Category.assoc]
    apply (Iso.eq_inv_comp ((Cat.Hom.toNatIso (b.2.mapComp f.1 (Quiver.Hom.op ZZ))).app
      ((g.2.app a.1).toFunctor.obj x))).mpr
    exact hmc.symm
  -- hnn_inv: slide map₂ (η.1 ▷ ZZ.op) past g.2.naturality (inverse form), point x
  have hnn_inv : (b.2.map₂ (η.1 ▷ Quiver.Hom.op ZZ)).toNatTrans.app
        ((g.2.app a.1).toFunctor.obj x) ≫
      (g.2.naturality (g.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app x =
      (g.2.naturality (f.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app x ≫
        (g.2.app γ).toFunctor.map ((a.2.map₂ (η.1 ▷ Quiver.Hom.op ZZ)).toNatTrans.app x) := by
    apply (Iso.comp_inv_eq ((Cat.Hom.toNatIso (g.2.naturality (g.1 ≫ Quiver.Hom.op ZZ))).app x)).mpr
    erw [Category.assoc]
    apply (Iso.eq_inv_comp ((Cat.Hom.toNatIso
      (g.2.naturality (f.1 ≫ Quiver.Hom.op ZZ))).app x)).mpr
    exact hnn.symm
  rw [Functor.map_comp]
  erw [Category.assoc]
  erw [reassoc_of% hmc_inv]
  erw [Category.assoc]
  erw [hnn_inv]
  -- remaining η.2 coherences
  have hη2 := (η.2.as.app γ).toNatTrans.naturality
    ((a.2.map₂ (op2 (ZZ ◁ η.1.unop2))).toNatTrans.app x)
  have hMCinv := (b.2.mapComp f.1 (Quiver.Hom.op ZZ)).inv.toNatTrans.naturality
    ((η.2.as.app a.1).toNatTrans.app x)
  dsimp at hmod hη2 hMCinv
  -- hmod_inv: slide mfZZ.map P past g.2.naturality → f.2.naturality (modification), point x
  have hmod_inv : (b.2.map (f.1 ≫ Quiver.Hom.op ZZ)).toFunctor.map
        ((η.2.as.app a.1).toNatTrans.app x) ≫
      (g.2.naturality (f.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app x =
      (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app x ≫
        (η.2.as.app γ).toNatTrans.app ((a.2.map (f.1 ≫ Quiver.Hom.op ZZ)).toFunctor.obj x) := by
    apply (Iso.comp_inv_eq ((Cat.Hom.toNatIso (g.2.naturality (f.1 ≫ Quiver.Hom.op ZZ))).app x)).mpr
    erw [Category.assoc]
    apply (Iso.eq_inv_comp ((Cat.Hom.toNatIso
      (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ))).app x)).mpr
    exact hmod.symm
  erw [reassoc_of% hMCinv, reassoc_of% hmod_inv]
  erw [Category.assoc, ← hη2, ← Category.assoc]
  rfl

set_option linter.flexible false in
/-- The data for `yonedaLemmaBackwards`, stated against the *unlifted* `yonedaEvaluation'`.
`StrongTransIntoCats.liftDom` then supplies the domain-side universe lift, so no `ULift`
appears in any coherence proof. -/
def yonedaLemmaBackwardsData :
    StrongTransIntoCats (@yonedaEvaluation' B _) (@yonedaPairing B _) where
  app := yonedaLemmaBackwardsFunctor
  naturality {a b} f :=
    NatIso.ofComponents (fun X ↦ backwardsNaturalityIso f X)
      (fun {X Y} f₁ ↦ backwards_naturality_iso_natural f f₁)
  naturality_naturality' {a b} {f g} η x := by
    simp only [NatIso.ofComponents_hom_app]
    apply homCategory.ext
    intro γ
    erw [homCategory_comp_as_app, homCategory_comp_as_app]
    apply Cat.Hom₂.ext_app
    intro ZZ
    dsimp only [backwardsNaturalityIso, backwardsNaturalityIsoApp]
    simp only [Cat.Hom.toNatTrans_comp, NatTrans.comp_app, isoMk_hom_as_app, Cat.Hom.isoMk_hom,
      Cat.toCatHom₂_toNatTrans, NatIso.ofComponents_hom_app, Iso.trans_hom, Iso.symm_hom,
      Iso.app_hom, Cat.Hom.toNatIso]
    erw [backwards_map_comp]
    simp only [yonedaPairing_map₂]
    simp only [NatTrans.toCatHom₂_toNatTrans]
    dsimp only [yonedaPairingMap₂, yonedaPairingMapFunctor, Functor.whiskerLeft,
      Functor.whiskerRight, precomposing, postcomposing, precomposingCat, postcomposingCat,
      postcomposing₂]
    erw [homCategory_comp_as_app]
    simp only [Cat.Hom.toNatTrans_comp, NatTrans.comp_app, Cat.whiskerRight_toNatTrans,
      whiskerRight_app, whiskerRight_as_app, Cat.toCatHom₂_toNatTrans]
    simp only [precomp_map, postcomp₂, postcomposingCat, postcomp_obj,
      Pseudofunctor.StrongTrans.comp_app, Functor.comp_map, Cat.Hom.comp_toFunctor]
    dsimp only [yonedaLemmaBackwardsFunctor, backwardsTrans,
      backwardsFibreFunctor, yonedaEvaluation']
    simp only [Cat.whiskerLeft_toNatTrans, whiskerLeft_app, whiskerLeft_as_app]
    exact backwards_naturality_naturality_core η x ZZ
  naturality_id' a x := by sorry
  naturality_comp' {a b c} f g x := by sorry

/--
The *backward strong transformation* `yonedaEvaluation ⟶ yonedaPairing` for the Yoneda lemma.

At each pair `x = (b₀, F)`, the component functor is `yonedaLemmaBackwardsFunctor x`, the
Yoneda embedding functor sending `s : F.obj b₀` to the strong transformation
`(a, f) ↦ (F.map f).obj s`.

This is the inverse direction of the Yoneda equivalence.  Together with `yonedaLemmaForwards`
and the unit/counit isos (`yonedaHomInvId`, `yonedaInvHomId`), it forms `yonedaLemma`.
-/
def yonedaLemmaBackwards : StrongTrans (@yonedaEvaluation B _) (@yonedaPairing B _) :=
  yonedaLemmaBackwardsData.liftDom

end Biyoneda
