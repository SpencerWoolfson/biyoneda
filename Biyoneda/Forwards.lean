/-
Copyright (c) 2026 Spencer Woolfson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Spencer Woolfson
-/
import Biyoneda.Pairing

/-!
# The forward direction: evaluate at the identity

`yonedaLemmaForwards : yonedaPairing ⟶ yonedaEvaluation` sends a strong transformation
`η : yoneda₀ b ⟶ F` to the object `η.app b (𝟙 b) : F.obj b`.

The transformation is assembled by `StrongTransIntoCats.lift` from `yonedaLemmaForwardsData`,
so no `ULift` plumbing appears in any coherence proof.  Each of the three coherence obligations
reduces to one of the `forwards_naturality_*_core` lemmas below, which state the content in the
unlifted fibre.

## A note on transparency, and why the proofs here look the way they do

Most goals in this file are **not type-correct at `implicit` transparency**.  The evaluation
point is `𝟙 (unop a.1)`, which elaborates at the bare type `unop a.1 ⟶ unop a.1`, while the
functors it is fed to expect `↑((yoneda₀ (unop a.1)).obj a.1)`; the two are the same type, but
only after unfolding a semireducible definition.  `rw` and `simp` match at reducible
transparency, so on such a goal they do not merely fail to find a pattern -- they can never
fire at all, and Lean says so in a note rather than an error.  This is a property of the
statements themselves, not damage done by a previous tactic.

Three moves get around it, and every proof below is one of them:

* the **padding trick** (`forwards_naturality_id_core`) -- `show` the goal's value in its
  distributed form, identities and all, and let `simp` cancel them.  `show` checks at default
  transparency, so it sidesteps the mismatch instead of fighting it;
* **`rfl` bridges** (`forwards_naturality_naturality_lhs_app` / `_rhs_app`) -- name the
  distributed form of a folded side, which needs no motive;
* **term assembly** (`forwards_naturality_naturality_unitor`, `..._core`) -- state the
  mathematics as a separate lemma in a spelling where the tactics do work, then chain
  `congrArg`, `Category.assoc` and `Functor.map_comp` by hand.  `exact` checks at default
  transparency, so it bridges the two spellings for free.
-/

namespace Biyoneda

open CategoryTheory Bicategory Bicategory.Opposite Opposite Pseudofunctor StrongTrans Functor
open scoped Pseudofunctor.StrongTrans

universe u v w v₁ v₂ u₁ u₂

attribute [local instance] uliftCategory


variable {B : Type u} [Bicategory.{w, v} B]

universe w₁

/--
At a fixed pair `x = (b, F)`, the *evaluate-at-identity functor*
`StrongTrans (yoneda₀ b) F ⥤ F.obj b`.

This is the core of the Yoneda equivalence at the level of individual categories:
* **On objects**: a strong transformation `η : yoneda₀ b ⟶ F` maps to
  `η.app b (𝟙 b) : F.obj b` — apply the component at `b`, then evaluate at `𝟙 b`.
* **On morphisms**: a modification `m : η ⟶ θ` maps to
  `m.as.app b (𝟙 b) : η.app b (𝟙 b) ⟶ θ.app b (𝟙 b)`.
-/
@[simp]
def yonedaLemmaForwardsFunctor (x : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat)) :
    yonedaPairing.obj x ⥤ yonedaEvaluation'.obj x where
  obj pair := (pair.app x.1).toFunctor.obj (𝟙 (unop x.1))
  map {a b} f := (f.as.app x.1).toNatTrans.app (𝟙 (unop x.1))

/-- The component form of the naturality square for `yonedaLemmaForwards`. -/
lemma forwards_naturality_core {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b)
    {X Y : yoneda₀ (unop a.1) ⟶ a.2} (h : X ⟶ Y) :
    (f.2.app b.1).toFunctor.map ((h.as.app b.1).toNatTrans.app (𝟙 (unop b.1) ≫ f.1.unop)) ≫
      (f.2.app b.1).toFunctor.map ((Y.app b.1).toFunctor.map (λ_ f.1.unop).hom) ≫
        (f.2.app b.1).toFunctor.map ((Y.app b.1).toFunctor.map (ρ_ f.1.unop).inv) ≫
          (f.2.app b.1).toFunctor.map ((Y.naturality f.1).hom.toNatTrans.app (𝟙 (unop a.1))) =
    ((f.2.app b.1).toFunctor.map ((X.app b.1).toFunctor.map (λ_ f.1.unop).hom) ≫
        (f.2.app b.1).toFunctor.map ((X.app b.1).toFunctor.map (ρ_ f.1.unop).inv) ≫
          (f.2.app b.1).toFunctor.map ((X.naturality f.1).hom.toNatTrans.app (𝟙 (unop a.1)))) ≫
      (f.2.app b.1).toFunctor.map ((a.2.map f.1).toFunctor.map
        ((h.as.app a.1).toNatTrans.app (𝟙 (unop a.1)))) := by
  have h1 := (h.as.app b.1).toNatTrans.naturality ((λ_ f.1.unop).hom ≫ (ρ_ f.1.unop).inv)
  have h2 := modification_naturality_app h f.1 (𝟙 (unop a.1))
  have h3 := (f.2.naturality f.1).hom.toNatTrans.naturality
    ((h.as.app a.1).toNatTrans.app (𝟙 (unop a.1)))
  dsimp at h1 h2 h3
  -- The lemma's statement keeps `(λ_).hom` and `(ρ_).inv` as separate factors, but `h1` is
  -- naturality at their composite.  `simp only [Functor.map_comp]` cannot bridge the two --
  -- it reaches the outer `(f.2.app b.1).map` and reports no progress on the inner one, the
  -- usual sign that the two spell the functor through different instance paths.  Supplying
  -- `map_comp` as an explicitly-typed term sidesteps the instantiation.
  rw [(X.app b.1).toFunctor.map_comp (λ_ f.1.unop).hom (ρ_ f.1.unop).inv,
    (Y.app b.1).toFunctor.map_comp (λ_ f.1.unop).hom (ρ_ f.1.unop).inv] at h1
  have h1' := congrArg (fun m ↦ (f.2.app b.1).toFunctor.map m) h1
  have h2' := congrArg (fun m ↦ (f.2.app b.1).toFunctor.map m) h2
  simp only [Functor.map_comp] at h1' h2'
  rw [← reassoc_of% h1']
  -- with the diagonal slide gone from the statement, the goal ends exactly at `h2'`'s left-hand
  -- side, so this is a plain rewrite rather than the `reassoc_of%` the old shape needed
  erw [h2']
  simp only [Category.assoc]
  rfl

/--
Inserting the cancelling pair `(ρ_ f).inv ≫ (ρ_ f).hom` into a unitor conjugation changes
nothing.  Trivial as stated, and stated anyway: the goal it is used on is not type-correct at
`implicit` transparency, so `rw`/`simp` cannot reach it, while `exact` -- which checks at
default transparency -- can.
-/
lemma unitor_conj_pad {x y : B} {f g : x ⟶ y} (θ : f ⟶ g) :
    (λ_ f).hom ≫ θ ≫ (ρ_ g).inv
      = ((λ_ f).hom ≫ (ρ_ f).inv) ≫ (ρ_ f).hom ≫ θ ≫ (ρ_ g).inv := by
  simp

-- `linter.flexible` wants the `simp` inside `hL` squeezed. Its output is matched against the
-- named `unitor_conj_pad`, so simp drift fails loudly rather than silently; and the suggested
-- list names an auto-generated projection lemma that any Mathlib bump would rename.
set_option linter.flexible false in
/--
The `Z`-side identity underlying `naturality_naturality` for `yonedaLemmaForwards`.

Transporting the evaluation point `𝟙` along `η.1` and then through `Z.naturality g.1` agrees
with going through `Z.naturality f.1` and then applying `a.2.map₂ η.1`.  It is exactly the
2-naturality of `Z.naturality` in the 2-cell `η.1` (`Z.naturality_naturality`), combined with
right-unitor naturality to reconcile the two unitor spellings.
-/
lemma forwards_naturality_naturality_unitor {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} {f g : a ⟶ b}
    (η : f ⟶ g) (Z : Pseudofunctor.StrongTrans (yoneda₀ (unop a.1)) a.2) :
    (Z.app b.1).toFunctor.map ((λ_ f.1.unop).hom ≫ η.1.unop2 ≫ (λ_ g.1.unop).inv) ≫
      (Z.app b.1).toFunctor.map ((λ_ g.1.unop).hom ≫ (ρ_ g.1.unop).inv) ≫
        (Z.naturality g.1).hom.toNatTrans.app (𝟙 (unop a.1)) =
    ((Z.app b.1).toFunctor.map ((λ_ f.1.unop).hom ≫ (ρ_ f.1.unop).inv) ≫
        (Z.naturality f.1).hom.toNatTrans.app (𝟙 (unop a.1))) ≫
      (a.2.map₂ η.1).toNatTrans.app ((Z.app a.1).toFunctor.obj (𝟙 (unop a.1))) := by
  -- The goal is not type-correct at `implicit` transparency -- the evaluation point
  -- `𝟙 (unop a.1)` is typed `unop a.1 ⟶ unop a.1` where `↑((yoneda₀ (unop a.1)).obj a.1)` is
  -- wanted -- so no `rw` or `simp` can fire on it, and none ever will: this is the statement's
  -- own elaboration, not damage from a prior tactic.  `exact` checks at *default* transparency,
  -- so the proof is assembled as a term out of facts proved elsewhere, in spellings where the
  -- tactics do work.
  have hnn := Z.naturality_naturality_app η.1 (𝟙 (unop a.1))
  -- `(yoneda₀ x).map₂ η.1` at the point is `η.1.unop2 ▷ 𝟙`, i.e. the right-unitor conjugate of
  -- `η.1.unop2`; `unitor_conj_pad` supplies the cancelling pair the two spellings differ by.
  have hL : ((λ_ f.1.unop).hom ≫ η.1.unop2 ≫ (λ_ g.1.unop).inv) ≫
        ((λ_ g.1.unop).hom ≫ (ρ_ g.1.unop).inv)
      = ((λ_ f.1.unop).hom ≫ (ρ_ f.1.unop).inv) ≫
        ((yoneda₀ (unop a.1)).map₂ η.1).toNatTrans.app (𝟙 (unop a.1)) := by
    simp
    exact unitor_conj_pad _
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg
    (fun t => t ≫ (Z.naturality g.1).hom.toNatTrans.app (𝟙 (unop a.1)))
    (((Z.app b.1).toFunctor.map_comp _ _).symm.trans
      (congrArg (Z.app b.1).toFunctor.map hL))) ?_
  refine Eq.trans (congrArg
    (fun t => t ≫ (Z.naturality g.1).hom.toNatTrans.app (𝟙 (unop a.1)))
    ((Z.app b.1).toFunctor.map_comp _ _)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg
    (fun t => (Z.app b.1).toFunctor.map ((λ_ f.1.unop).hom ≫ (ρ_ f.1.unop).inv) ≫ t) hnn) ?_
  exact (Category.assoc _ _ _).symm

/-- The pairing's `map₂`, evaluated on a strong transformation and then at the identity: the
whiskering by `η.1` first, then `η.2`'s own component.  A `rfl` bridge -- its only job is to
name the distributed form, since the folded one carries `Z` at a type mentioning
`yonedaPairing.obj a` and no tactic can build a motive through that. -/
lemma forwards_naturality_naturality_lhs_app {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} {f g : a ⟶ b}
    (η : f ⟶ g) (Z : Pseudofunctor.StrongTrans (yoneda₀ (unop a.1)) a.2) :
    (((yonedaPairing.map₂ η).toNatTrans.app Z).as.app b.1).toNatTrans.app (𝟙 (unop b.1))
      = (f.2.app b.1).toFunctor.map
            ((Z.app b.1).toFunctor.map (𝟙 (unop b.1) ◁ η.1.unop2)) ≫
          (η.2.as.app b.1).toNatTrans.app
            ((Z.app b.1).toFunctor.obj (𝟙 (unop b.1) ≫ g.1.unop)) := rfl

/-- The evaluation pseudofunctor's `map₂` at a point, distributed: `evalMap₂`'s two whiskerings.
The companion `rfl` bridge to `forwards_naturality_naturality_lhs_app`. -/
lemma forwards_naturality_naturality_rhs_app {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} {f g : a ⟶ b}
    (η : f ⟶ g) (X : ↑(a.2.obj a.1)) :
    (yonedaEvaluation'.map₂ η).toNatTrans.app X
      = (f.2.app b.1).toFunctor.map ((a.2.map₂ η.1).toNatTrans.app X) ≫
          (η.2.as.app b.1).toNatTrans.app ((a.2.map g.1).toFunctor.obj X) := rfl

/--
The component core of the `naturality_naturality` obligation of `yonedaLemmaForwards`, stated
in the unlifted fibre (the `.down` of the lifted 2-cells).

It says the forward naturality isomorphism is natural in the 2-cell `η = (η.1, η.2)`.  The
proof splits `η` into its two components: the modification part `η.2` contributes its own
naturality square, and the base 2-cell `η.1` contributes
`forwards_naturality_naturality_unitor`, which is where all the mathematics is.
-/
lemma forwards_naturality_naturality_core {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} {f g : a ⟶ b}
    (η : f ⟶ g) (Z : Pseudofunctor.StrongTrans (yoneda₀ (unop a.1)) a.2) :
    (((yonedaPairing.map₂ η).toNatTrans.app Z).as.app b.1).toNatTrans.app (𝟙 (unop b.1)) ≫
        (g.2.app b.1).toFunctor.map
          ((Z.app b.1).toFunctor.map ((λ_ g.1.unop).hom ≫ (ρ_ g.1.unop).inv) ≫
            ((Cat.Hom.toNatIso (Z.naturality g.1)).app (𝟙 (unop a.1))).hom) =
    (f.2.app b.1).toFunctor.map
          ((Z.app b.1).toFunctor.map ((λ_ f.1.unop).hom ≫ (ρ_ f.1.unop).inv) ≫
            ((Cat.Hom.toNatIso (Z.naturality f.1)).app (𝟙 (unop a.1))).hom) ≫
    (yonedaEvaluation'.map₂ η).toNatTrans.app ((Z.app a.1).toFunctor.obj (𝟙 (unop a.1))) := by
  -- Both sides are descended once by the `rfl` bridges above, after which the goal is an
  -- ordinary fibre equation and the content is exactly the unitor lemma.  `hu` restates it in
  -- the goal's `Cat.Hom.toNatIso` spelling; the `have`'s ascription is what bridges the two.
  have hnat := (η.2.as.app b.1).toNatTrans.naturality
    ((Z.app b.1).toFunctor.map ((λ_ g.1.unop).hom ≫ (ρ_ g.1.unop).inv) ≫
      ((Cat.Hom.toNatIso (Z.naturality g.1)).app (𝟙 (unop a.1))).hom)
  have hu : (Z.app b.1).toFunctor.map ((λ_ f.1.unop).hom ≫ η.1.unop2 ≫ (λ_ g.1.unop).inv) ≫
        ((Z.app b.1).toFunctor.map ((λ_ g.1.unop).hom ≫ (ρ_ g.1.unop).inv) ≫
          ((Cat.Hom.toNatIso (Z.naturality g.1)).app (𝟙 (unop a.1))).hom)
      = ((Z.app b.1).toFunctor.map ((λ_ f.1.unop).hom ≫ (ρ_ f.1.unop).inv) ≫
          ((Cat.Hom.toNatIso (Z.naturality f.1)).app (𝟙 (unop a.1))).hom) ≫
        (a.2.map₂ η.1).toNatTrans.app ((Z.app a.1).toFunctor.obj (𝟙 (unop a.1))) :=
    forwards_naturality_naturality_unitor η Z
  refine Eq.trans (congrArg
    (fun t => t ≫ (g.2.app b.1).toFunctor.map
      ((Z.app b.1).toFunctor.map ((λ_ g.1.unop).hom ≫ (ρ_ g.1.unop).inv) ≫
        ((Cat.Hom.toNatIso (Z.naturality g.1)).app (𝟙 (unop a.1))).hom))
    (forwards_naturality_naturality_lhs_app η Z)) ?_
  refine Eq.trans ?_ (congrArg
    (fun t => (f.2.app b.1).toFunctor.map
      ((Z.app b.1).toFunctor.map ((λ_ f.1.unop).hom ≫ (ρ_ f.1.unop).inv) ≫
        ((Cat.Hom.toNatIso (Z.naturality f.1)).app (𝟙 (unop a.1))).hom) ≫ t)
    (forwards_naturality_naturality_rhs_app η ((Z.app a.1).toFunctor.obj (𝟙 (unop a.1))))).symm
  -- the pairing's `map₂` contributes `𝟙 ◁ η.1.unop2`; the unitor lemma is stated in the
  -- conjugated spelling, which is what `id_whiskerLeft` converts it to
  simp only [Bicategory.id_whiskerLeft]
  -- slide `η.2`'s component past `g.2`, then the two `f.2`-images merge and `hu` finishes
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun t => (f.2.app b.1).toFunctor.map
      ((Z.app b.1).toFunctor.map ((λ_ f.1.unop).hom ≫ η.1.unop2 ≫ (λ_ g.1.unop).inv)) ≫ t)
    hnat.symm) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun t => t ≫ (η.2.as.app b.1).toNatTrans.app
      ((a.2.map g.1).toFunctor.obj ((Z.app a.1).toFunctor.obj (𝟙 (unop a.1)))))
    (((f.2.app b.1).toFunctor.map_comp _ _).symm.trans
      (congrArg (f.2.app b.1).toFunctor.map hu))) ?_
  refine Eq.trans (congrArg (fun t => t ≫ (η.2.as.app b.1).toNatTrans.app
      ((a.2.map g.1).toFunctor.obj ((Z.app a.1).toFunctor.obj (𝟙 (unop a.1)))))
    ((f.2.app b.1).toFunctor.map_comp _ _)) ?_
  exact Category.assoc _ _ _

set_option backward.isDefEq.respectTransparency false in
-- `linter.flexible`: the `simp` below is followed by a `change` to an explicitly written
-- form, so drift fails loudly. The suggested `simp only` runs to 25 lemma names.
set_option linter.flexible false in
/--
The component core of the `naturality_id` obligation of `yonedaLemmaForwards`, stated in the
unlifted fibre.

This is the genuine unit coherence: it relates `yonedaPairing.mapId` to `a.2.mapId`.  The proof
is driven by `Z.naturality_id` — the unit coherence of the strong transformation `Z` itself —
after which both sides are pure unitor data and the remaining content is
`Bicategory.unitors_equal` (`(λ_ (𝟙 x)).hom = (ρ_ (𝟙 x)).hom`).
-/
lemma forwards_naturality_id_core (a : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v}))
    (Z : Pseudofunctor.StrongTrans (yoneda₀ (unop a.1)) a.2) :
    ((Z.app a.1).toFunctor.map ((λ_ (𝟙 a.1).unop).hom ≫ (ρ_ (𝟙 a.1).unop).inv) ≫
        (Z.naturality (𝟙 a.1)).hom.toNatTrans.app (𝟙 (unop a.1))) ≫
      (yonedaEvaluation'.mapId a).hom.toNatTrans.app ((Z.app a.1).toFunctor.obj (𝟙 (unop a.1))) =
    (((yonedaPairing.mapId a).hom.toNatTrans.app Z).as.app a.1).toNatTrans.app (𝟙 (unop a.1)) := by
  -- `Z.naturality_id` is the whole mathematical input; the descent below just follows the
  -- composite's `mapId` down to `homPseudo`'s unitor iso, which is now the named `homMapId`.
  dsimp only [yonedaPairing, yonedaPairingComposite, Pseudofunctor.comp, homPseudo,
    homMapId, homMapIdApp,
    Pseudofunctor.prod, Pseudofunctor.op, yonedaEvaluation', evaluationPseudo]
  simp only [prelax_map₂_app, Iso.trans_hom, Cat.Hom.isoMk_hom, NatIso.ofComponents_hom_app,
    Cat.toCatHom₂_toNatTrans, Cat.Hom.toNatTrans_comp, NatTrans.comp_app,
    PrelaxFunctor.map₂Iso_hom, Category.assoc]
  have hZ := Cat.Hom₂.congr_app (Z.naturality_id a.1) (𝟙 (unop a.1))
  simp only [Cat.Hom.toNatTrans_comp, NatTrans.comp_app, Cat.whiskerLeft_toNatTrans,
    Cat.whiskerRight_toNatTrans, whiskerLeft_app, whiskerRight_app] at hZ
  rw [hZ]
  -- What is left is a single clean equation: `(Z.app a.1).map (ρ_ (𝟙 (unop a.1))).hom` against
  -- the `mapId` chain of `Bᵒᵖ ⥤ᵖ Cat` evaluated at the point.  Descending that chain with the
  -- `*_as_app` lemmas is measured to fail -- `simp`/`dsimp` report no progress and Lean notes
  -- the target is not type-correct at `implicit` transparency, because `(𝟙 F).app α` and
  -- `𝟙 (F.obj α)` are the same 1-cell spelled through two `CategoryStruct` paths.  The padding
  -- trick sidesteps that entirely: name the chain's value at the point, identities and all,
  -- and let `simp` cancel them.  Each `𝟙` below is one structural factor of the chain -- the
  -- two associators, the left unitor, the whiskered identity and the right unitor -- and the
  -- single surviving factor is `yoneda.mapId`'s own right unitor, whiskered by `Z`.
  simp
  change _ = 𝟙 _ ≫ (Z.app a.1).toFunctor.map (ρ_ (𝟙 (unop a.1))).hom ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
  simp

/-- Core of `naturality_comp` for `yonedaLemmaForwards` (unlifted fibre form). -/
lemma forwards_naturality_comp_core {a b c : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b) (g : b ⟶ c)
    (Z : Pseudofunctor.StrongTrans (yoneda₀ (unop a.1)) a.2) :
    ((f.2 ≫ g.2).app c.1).toFunctor.map
          ((Z.app c.1).toFunctor.map
              ((λ_ (f.1 ≫ g.1).unop).hom ≫ (ρ_ (f.1 ≫ g.1).unop).inv) ≫
            (Z.naturality (f.1 ≫ g.1)).hom.toNatTrans.app (𝟙 (unop a.1))) ≫
      (yonedaEvaluation'.mapComp f g).hom.toNatTrans.app
        ((Z.app a.1).toFunctor.obj (𝟙 (unop a.1))) =
    (((yonedaPairing.mapComp f g).hom.toNatTrans.app Z).as.app c.1).toNatTrans.app
        (𝟙 (unop c.1)) ≫
      (g.2.app c.1).toFunctor.map
            ((((yonedaPairing.map f).toFunctor.obj Z).app c.1).toFunctor.map
                ((λ_ g.1.unop).hom ≫ (ρ_ g.1.unop).inv) ≫
              (((yonedaPairing.map f).toFunctor.obj Z).naturality g.1).hom.toNatTrans.app
                (𝟙 (unop b.1))) ≫
        (yonedaEvaluation'.map g).toFunctor.map
          ((f.2.app b.1).toFunctor.map
              ((Z.app b.1).toFunctor.map ((λ_ f.1.unop).hom ≫ (ρ_ f.1.unop).inv) ≫
                (Z.naturality f.1).hom.toNatTrans.app (𝟙 (unop a.1)))) := by
  -- Pending: the statement mentions `yonedaPairing.mapComp`, which the composite defines
  -- differently (not defeq), so this needs a genuine re-proof rather than a re-spelling.
  sorry

/--
Distributing a functor over a composite whose left factor is itself a functor image.  Three
`Functor.map_comp` steps, stated in bare categories because at the use site they are exactly
what will not fire: the goal there is not type-correct at `implicit` transparency.  Instantiated
by `exact`, which checks at default transparency, it goes straight through.
-/
lemma map_map_comp_dist {C D E : Type*} [Category C] [Category D] [Category E]
    (F : D ⥤ E) (G : C ⥤ D) {X Y Z : C} (u : X ⟶ Y) (v : Y ⟶ Z) {W : D} (N : G.obj Z ⟶ W) :
    F.map (G.map (u ≫ v) ≫ N) = F.map (G.map u) ≫ F.map (G.map v) ≫ F.map N := by
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The data for `yonedaLemmaForwards`, stated against the *unlifted* `yonedaEvaluation'`.
`StrongTransIntoCats.lift` then supplies the lifted strong transformation.

Every field is now a term: three are their `*_core` lemmas verbatim, and `naturality` is the
core with `map_map_comp_dist` distributing the folded `mapIso` on each side.  Only
`naturality_comp'` is still open, through `forwards_naturality_comp_core`. -/
def yonedaLemmaForwardsData :
    StrongTransIntoCats (@yonedaPairing B _) (@yonedaEvaluation' B _) where
  app := yonedaLemmaForwardsFunctor
  naturality {a b} f :=
    NatIso.ofComponents
      (fun X =>
        (f.2.app b.1).toFunctor.mapIso
            ((X.app b.1).toFunctor.mapIso (λ_ f.1.unop ≪≫ (ρ_ f.1.unop).symm) ≪≫
              (Cat.Hom.toNatIso (X.naturality f.1)).app (𝟙 (unop a.1))))
      (by
        -- The mathematical content is exactly `forwards_naturality_core`, which states the two
        -- sides distributed; the field states them folded, as one `mapIso`.  The old proof tried
        -- to close that gap with a descent simp set and `convert`, which cannot work -- the goal
        -- is not type-correct at `implicit` transparency, so `Functor.map_comp` never fires.
        -- Distributing by an explicitly instantiated term does work, and the `rfl`-equal
        -- composite-functor spellings on the outside are absorbed by `exact`.
        intro X Y h
        refine Eq.trans (congrArg (CategoryStruct.comp _)
          (map_map_comp_dist (f.2.app b.1).toFunctor (Y.app b.1).toFunctor _ _ _)) ?_
        refine Eq.trans ?_ (congrArg (fun t => t ≫ _)
          (map_map_comp_dist (f.2.app b.1).toFunctor (X.app b.1).toFunctor _ _ _)).symm
        exact forwards_naturality_core f h)
  naturality_naturality' {a b} {f g} η Z := forwards_naturality_naturality_core η Z
  naturality_id' a Z := forwards_naturality_id_core a Z
  naturality_comp' {a b c} f g Z := forwards_naturality_comp_core f g Z

/--
The *forward strong transformation* `yonedaPairing ⟶ yonedaEvaluation` for the Yoneda lemma.

At each pair `x = (b, F)`, the component functor is `yonedaLemmaForwardsFunctor x`, which
sends a strong transformation `η : yoneda₀ b ⟶ F` to the element `η.app b (𝟙 b) : F.obj b`.

Mathematically, this is the "evaluate at identity" direction of the equivalence
  `StrongTrans(yoneda₀ b, F)  ≃  F.obj b`.

The data lives in `yonedaLemmaForwardsData`, stated against the unlifted
`yonedaEvaluation'`; `StrongTransIntoCats.lift` supplies the universe lift, so no `ULift`
plumbing appears in any of the coherence proofs.
-/
def yonedaLemmaForwards : StrongTrans (@yonedaPairing B _) (@yonedaEvaluation B _) :=
  StrongTransIntoCats.lift yonedaLemmaForwardsData

end Biyoneda
