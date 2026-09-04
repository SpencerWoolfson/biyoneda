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
  simp only [Cat.Hom.toNatTrans_comp, Cat.whiskerRight_toNatTrans] at hmc hnn hmod
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
  -- Two slides finish it: `hMCinv` carries `η.2`'s component through the `b.2.mapComp` inverse,
  -- `hmod_inv` carries it through `η.2`'s own naturality inverse, and what is left is `hη2`.
  -- The old proof spent four more `erw`s here and no longer found its pattern; `reassoc_of%`,
  -- applied to the `*_inv` haves that have already fixed the spellings, needs two rewrites.
  -- The last step is an `exact` rather than a `rw` because the goal writes the 2-cell as
  -- `op2 (ZZ ◁ η.1.unop2)` where `hη2` writes `η.1 ▷ ZZ.op` -- defeq, not syntactic.
  rw [reassoc_of% hMCinv, reassoc_of% hmod_inv]
  exact congrArg (CategoryStruct.comp _) (congrArg (CategoryStruct.comp _) hη2.symm)

/-! ### The `naturality_naturality` field, descended

Same shape as everything else in this direction: two `rfl` bridges take the modification
equation down to a fibre equation, and the content is
`backwards_naturality_naturality_core`.  The one extra ingredient is `backwards_nn_slide`,
which converts the *evaluation* side's `map₂` into the *pairing* side's — the two sides of
the field state the same 2-cell through `f.2`/`a.2` and through `b.2`/`η.2` respectively.
-/

/-- Left-hand side of the `naturality_naturality` square, distributed at a point. -/
lemma backwards_nn_lhs_app {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} {f g : a ⟶ b} (η : f ⟶ g)
    (x : ↑(yonedaEvaluation'.obj a)) {γ : Bᵒᵖ} (ZZ : ↑((yoneda₀ (unop b.1)).obj γ)) :
    ((((yonedaLemmaBackwardsFunctor b).map ((yonedaEvaluation'.map₂ η).toNatTrans.app x) ≫
        (backwardsNaturalityIso g x).hom).as.app γ).toNatTrans.app ZZ)
      = (b.2.map (Quiver.Hom.op ZZ)).toFunctor.map
            ((f.2.app b.1).toFunctor.map ((a.2.map₂ η.1).toNatTrans.app x) ≫
              (η.2.as.app b.1).toNatTrans.app ((a.2.map g.1).toFunctor.obj x)) ≫
          ((b.2.map (Quiver.Hom.op ZZ)).toFunctor.map
              ((g.2.naturality g.1).hom.toNatTrans.app x) ≫
            (b.2.mapComp g.1 (Quiver.Hom.op ZZ)).inv.toNatTrans.app
              ((g.2.app a.1).toFunctor.obj x) ≫
            (g.2.naturality (g.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app x) := rfl

/-- Right-hand side of the `naturality_naturality` square, distributed at a point. -/
lemma backwards_nn_rhs_app {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} {f g : a ⟶ b} (η : f ⟶ g)
    (x : ↑(yonedaEvaluation'.obj a)) {γ : Bᵒᵖ} (ZZ : ↑((yoneda₀ (unop b.1)).obj γ)) :
    ((((backwardsNaturalityIso f x).hom ≫
        (yonedaPairing.map₂ η).toNatTrans.app
          ((yonedaLemmaBackwardsFunctor a).obj x)).as.app γ).toNatTrans.app ZZ)
      = ((b.2.map (Quiver.Hom.op ZZ)).toFunctor.map
              ((f.2.naturality f.1).hom.toNatTrans.app x) ≫
            (b.2.mapComp f.1 (Quiver.Hom.op ZZ)).inv.toNatTrans.app
              ((f.2.app a.1).toFunctor.obj x) ≫
            (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app x) ≫
          ((f.2.app γ).toFunctor.map ((a.2.map₂ (op2 (ZZ ◁ η.1.unop2))).toNatTrans.app x) ≫
            (η.2.as.app γ).toNatTrans.app
              ((a.2.map (Quiver.Hom.op
                ((postcomp (unop γ) g.1.unop).toCatHom.toFunctor.obj ZZ))).toFunctor.obj x)) := rfl

/-- The evaluation side's 2-cell image, slid across to the pairing side's.  Three naturality
squares: `η.2`'s modification naturality at `g.1`, `f.2`'s `naturality_naturality` at `η.1`,
and the plain naturality of `b.2.map₂ η.1` at `η.2`'s own component. -/
lemma backwards_nn_slide {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} {f g : a ⟶ b} (η : f ⟶ g)
    (x : ↑(yonedaEvaluation'.obj a)) :
    ((f.2.app b.1).toFunctor.map ((a.2.map₂ η.1).toNatTrans.app x) ≫
        (η.2.as.app b.1).toNatTrans.app ((a.2.map g.1).toFunctor.obj x)) ≫
      (g.2.naturality g.1).hom.toNatTrans.app x
      = (f.2.naturality f.1).hom.toNatTrans.app x ≫
        ((b.2.map f.1).toFunctor.map ((η.2.as.app a.1).toNatTrans.app x) ≫
          (b.2.map₂ η.1).toNatTrans.app ((g.2.app a.1).toFunctor.obj x)) := by
  have h1 := modification_naturality_app η.2 g.1 x
  have h2 := f.2.naturality_naturality_app η.1 x
  have h3 := (b.2.map₂ η.1).toNatTrans.naturality ((η.2.as.app a.1).toNatTrans.app x)
  dsimp at h1 h2 h3
  rw [Category.assoc, h1, reassoc_of% h2, ← h3]

/-! ### The `naturality_id` field, descended

`yonedaPairing.mapId` is a chain of structural 2-cells in `Bᵒᵖ ⥤ᵖ Cat`; descending it with the
`*_as_app` lemmas does not work (see the note in `Biyoneda/Forwards.lean`), so
`yonedaPairing_mapId_app` (in `Biyoneda/Pairing.lean`, with its `mapComp` companion) descends it
another way.  With that in hand the field is two `rfl` bridges and one pseudofunctor coherence.
-/

/-- The fibre content of `naturality_id`: `mapComp_id_left` for `F`, with the four identities
the identity strong transformation's own naturality contributes. -/
lemma backwards_id_core (F : Bᵒᵖ ⥤ᵖ Cat.{w, v}) {b₀ γ : Bᵒᵖ} (ZZ : unop γ ⟶ unop b₀)
    (eval : ↑(F.obj b₀)) :
    ((F.map (Quiver.Hom.op ZZ)).toFunctor.map (𝟙 _ ≫ 𝟙 _) ≫
        (F.mapComp (𝟙 b₀) (Quiver.Hom.op ZZ)).inv.toNatTrans.app eval ≫ (𝟙 _ ≫ 𝟙 _)) ≫
      (F.map₂ (op2 (ρ_ ZZ).hom)).toNatTrans.app eval
      = (F.map (Quiver.Hom.op ZZ)).toFunctor.map
          ((F.mapId b₀).hom.toNatTrans.app eval) := by
  simp

/-- Left-hand side of the `naturality_id` square, distributed at a point.  The four `𝟙`s are
the identity strong transformation's naturality, which is a pair of unitors. -/
lemma backwards_id_lhs_app (a : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})) (x : ↑(yonedaEvaluation'.obj a))
    (γ : Bᵒᵖ) (ZZ : ↑((yoneda₀ (unop a.1)).obj γ)) :
    ((((backwardsNaturalityIso (𝟙 a) x).hom ≫
        (yonedaPairing.mapId a).hom.toNatTrans.app
          ((yonedaLemmaBackwardsFunctor a).obj x)).as.app γ).toNatTrans.app ZZ)
      = ((a.2.map (Quiver.Hom.op ZZ)).toFunctor.map (𝟙 _ ≫ 𝟙 _) ≫
            (a.2.mapComp (𝟙 a.1) (Quiver.Hom.op ZZ)).inv.toNatTrans.app x ≫ (𝟙 _ ≫ 𝟙 _)) ≫
          ((((yonedaPairing.mapId a).hom.toNatTrans.app
            ((yonedaLemmaBackwardsFunctor a).obj x)).as.app γ).toNatTrans.app ZZ) := rfl

/-- Right-hand side of the `naturality_id` square, distributed at a point. -/
lemma backwards_id_rhs_app (a : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})) (x : ↑(yonedaEvaluation'.obj a))
    (γ : Bᵒᵖ) (ZZ : ↑((yoneda₀ (unop a.1)).obj γ)) :
    ((((yonedaLemmaBackwardsFunctor a).map
        ((yonedaEvaluation'.mapId a).hom.toNatTrans.app x)).as.app γ).toNatTrans.app ZZ)
      = (a.2.map (Quiver.Hom.op ZZ)).toFunctor.map
          ((a.2.mapId a.1).hom.toNatTrans.app x) := rfl

/-! ### The `naturality_comp` field, descended

Same three-step shape as the two fields above, and it now goes all the way down: two `rfl`
bridges distribute the two sides at a point, `yonedaPairing_mapComp_app` turns the composite
pairing's composition constraint into an associator, and what is left is
`backwards_comp_core` -- a plain equation in the fibre `↑(c.2.obj γ)`.

That core is the last open coherence in this direction, and it is stated rather than inlined on
purpose: as a standalone lemma it can be attacked without re-deriving any of the descent.
-/

/-- The pairing's action on a modification, at a point.  A `rfl` bridge. -/
lemma backwards_comp_map_app {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (g : a ⟶ b)
    {Z₁ Z₂ : ↑(yonedaPairing.obj a)} (μ : Z₁ ⟶ Z₂) (γ : Bᵒᵖ)
    (ZZ : ↑((yoneda₀ (unop b.1)).obj γ)) :
    ((((yonedaPairing.map g).toFunctor.map μ).as.app γ).toNatTrans.app ZZ)
      = (g.2.app γ).toFunctor.map
          ((μ.as.app γ).toNatTrans.app (ZZ ≫ g.1.unop)) := rfl

/-- Left-hand side of the `naturality_comp` square, distributed at a point.  The pairing's
`mapComp` is left folded here; `yonedaPairing_mapComp_app` handles it separately. -/
lemma backwards_comp_lhs_app {a b c : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b) (g : b ⟶ c)
    (x : ↑(yonedaEvaluation'.obj a)) (γ : Bᵒᵖ) (ZZ : ↑((yoneda₀ (unop c.1)).obj γ)) :
    ((((backwardsNaturalityIso (f ≫ g) x).hom ≫
        (yonedaPairing.mapComp f g).hom.toNatTrans.app
          ((yonedaLemmaBackwardsFunctor a).obj x)).as.app γ).toNatTrans.app ZZ)
      = ((c.2.map (Quiver.Hom.op ZZ)).toFunctor.map
              (((f ≫ g).2.naturality (f ≫ g).1).hom.toNatTrans.app x) ≫
            (c.2.mapComp (f ≫ g).1 (Quiver.Hom.op ZZ)).inv.toNatTrans.app
              (((f ≫ g).2.app a.1).toFunctor.obj x) ≫
            ((f ≫ g).2.naturality ((f ≫ g).1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app x) ≫
          ((((yonedaPairing.mapComp f g).hom.toNatTrans.app
            ((yonedaLemmaBackwardsFunctor a).obj x)).as.app γ).toNatTrans.app ZZ) := rfl

/-- Right-hand side of the `naturality_comp` square, distributed at a point. -/
lemma backwards_comp_rhs_app {a b c : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b) (g : b ⟶ c)
    (x : ↑(yonedaEvaluation'.obj a)) (γ : Bᵒᵖ) (ZZ : ↑((yoneda₀ (unop c.1)).obj γ)) :
    ((((yonedaLemmaBackwardsFunctor c).map
          ((yonedaEvaluation'.mapComp f g).hom.toNatTrans.app x) ≫
        (backwardsNaturalityIso g ((yonedaEvaluation'.map f).toFunctor.obj x)).hom ≫
        (yonedaPairing.map g).toFunctor.map
          (backwardsNaturalityIso f x).hom).as.app γ).toNatTrans.app ZZ)
      = (c.2.map (Quiver.Hom.op ZZ)).toFunctor.map
            ((yonedaEvaluation'.mapComp f g).hom.toNatTrans.app x) ≫
          ((c.2.map (Quiver.Hom.op ZZ)).toFunctor.map
              ((g.2.naturality g.1).hom.toNatTrans.app
                ((yonedaEvaluation'.map f).toFunctor.obj x)) ≫
            (c.2.mapComp g.1 (Quiver.Hom.op ZZ)).inv.toNatTrans.app
              ((g.2.app b.1).toFunctor.obj ((yonedaEvaluation'.map f).toFunctor.obj x)) ≫
            (g.2.naturality (g.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app
              ((yonedaEvaluation'.map f).toFunctor.obj x)) ≫
          (g.2.app γ).toFunctor.map
            ((b.2.map (Quiver.Hom.op (ZZ ≫ g.1.unop))).toFunctor.map
                ((f.2.naturality f.1).hom.toNatTrans.app x) ≫
              (b.2.mapComp f.1 (Quiver.Hom.op (ZZ ≫ g.1.unop))).inv.toNatTrans.app
                ((f.2.app a.1).toFunctor.obj x) ≫
              (f.2.naturality (f.1 ≫ Quiver.Hom.op (ZZ ≫ g.1.unop))).inv.toNatTrans.app x)
      := rfl

/-- The fibre content of `naturality_comp` for `yonedaLemmaBackwards`: the composite
transformation's naturality against the two factors' naturalities, glued by `c.2`'s `mapComp`
and the associator that `yonedaPairing.mapComp` contributes.

**PARKED (2026-09-03) -- the last open coherence in the backward direction.**  Everything
around it is proved: the descent above reaches this statement exactly, so the remaining work is
a single equation in `↑(c.2.obj γ)` with no folded pseudofunctor left in it.

Ingredients that are known to be the right ones and elaborate here:
`strongTrans_comp_naturality_app f.2 g.2 (f.1 ≫ g.1) x` and the same at
`(f.1 ≫ g.1) ≫ ZZ.op` expand the two `(f ≫ g).2.naturality` factors;
`(yonedaEvaluation'.mapComp f g).hom.toNatTrans.app x` is `evalMapComp f.1 f.2 g.1 g.2` at `x`
by `rfl`.  Measured NOT to close it: `simp`, `cat_disch`, and
`simp only [strongTrans_comp_naturality_app, strongTrans_comp_app]` followed by `simp` -- the
last unfolds `vcomp`'s naturality into a five-factor associator chain, which is further from
the goal rather than closer.  Expect the shape of `backwards_square_core`
(`Biyoneda/BackwardsNaturality.lean`): four coherences applied in a fixed order, each one
`reassoc_of%`-ed into place. -/
lemma backwards_comp_core {a b c : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b) (g : b ⟶ c)
    (x : ↑(yonedaEvaluation'.obj a)) {γ : Bᵒᵖ} (ZZ : ↑((yoneda₀ (unop c.1)).obj γ)) :
    ((c.2.map (Quiver.Hom.op ZZ)).toFunctor.map
          (((f ≫ g).2.naturality (f ≫ g).1).hom.toNatTrans.app x) ≫
        (c.2.mapComp (f ≫ g).1 (Quiver.Hom.op ZZ)).inv.toNatTrans.app
          (((f ≫ g).2.app a.1).toFunctor.obj x) ≫
          ((f ≫ g).2.naturality ((f ≫ g).1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app x) ≫
      (g.2.app γ).toFunctor.map
        ((f.2.app γ).toFunctor.map
          ((((yonedaLemmaBackwardsFunctor a).obj x).app γ).toFunctor.map
            (α_ ZZ g.1.unop f.1.unop).inv)) =
    (c.2.map (Quiver.Hom.op ZZ)).toFunctor.map
        ((yonedaEvaluation'.mapComp f g).hom.toNatTrans.app x) ≫
      ((c.2.map (Quiver.Hom.op ZZ)).toFunctor.map
            ((g.2.naturality g.1).hom.toNatTrans.app
              ((yonedaEvaluation'.map f).toFunctor.obj x)) ≫
          (c.2.mapComp g.1 (Quiver.Hom.op ZZ)).inv.toNatTrans.app
              ((g.2.app b.1).toFunctor.obj ((yonedaEvaluation'.map f).toFunctor.obj x)) ≫
            (g.2.naturality (g.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app
              ((yonedaEvaluation'.map f).toFunctor.obj x)) ≫
        (g.2.app γ).toFunctor.map
          ((b.2.map (Quiver.Hom.op (ZZ ≫ g.1.unop))).toFunctor.map
              ((f.2.naturality f.1).hom.toNatTrans.app x) ≫
            (b.2.mapComp f.1 (Quiver.Hom.op (ZZ ≫ g.1.unop))).inv.toNatTrans.app
                ((f.2.app a.1).toFunctor.obj x) ≫
              (f.2.naturality (f.1 ≫ Quiver.Hom.op (ZZ ≫ g.1.unop))).inv.toNatTrans.app x) := by
  sorry

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
  -- The descent that used to be inlined here hit a `whnf` timeout at 200k heartbeats.  It is
  -- gone: the two `rfl` bridges above reach the fibre without unfolding anything, and the
  -- assembly below is a term, so nothing runs at default transparency.
  naturality_naturality' {a b} {f g} η x := by
    apply homCategory.ext
    intro γ
    apply Cat.Hom₂.ext_app
    intro ZZ
    refine Eq.trans (backwards_nn_lhs_app η x ZZ)
      (Eq.trans ?_ (backwards_nn_rhs_app η x ZZ).symm)
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun t => t ≫ _)
      ((((b.2.map (Quiver.Hom.op ZZ)).toFunctor.map_comp _ _).symm.trans
        (congrArg (b.2.map (Quiver.Hom.op ZZ)).toFunctor.map (backwards_nn_slide η x))).trans
        ((b.2.map (Quiver.Hom.op ZZ)).toFunctor.map_comp _ _))) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (CategoryStruct.comp _)
      (backwards_naturality_naturality_core η x ZZ)) ?_
    exact (Category.assoc _ _ _).symm
  naturality_id' a x := by
    apply homCategory.ext
    intro γ
    apply Cat.Hom₂.ext_app
    intro ZZ
    refine Eq.trans (backwards_id_lhs_app a x γ ZZ)
      (Eq.trans ?_ (backwards_id_rhs_app a x γ ZZ).symm)
    refine Eq.trans (congrArg (CategoryStruct.comp _) (yonedaPairing_mapId_app a _ γ ZZ)) ?_
    exact backwards_id_core a.2 ZZ x
  naturality_comp' {a b c} f g x := by
    apply homCategory.ext
    intro γ
    apply Cat.Hom₂.ext_app
    intro ZZ
    refine Eq.trans (backwards_comp_lhs_app f g x γ ZZ)
      (Eq.trans ?_ (backwards_comp_rhs_app f g x γ ZZ).symm)
    refine Eq.trans (congrArg (CategoryStruct.comp _)
      (yonedaPairing_mapComp_app f g ((yonedaLemmaBackwardsFunctor a).obj x) γ ZZ)) ?_
    exact backwards_comp_core f g x ZZ

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
