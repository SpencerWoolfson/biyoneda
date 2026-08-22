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
          (f.2.app b.1).toFunctor.map ((Y.naturality f.1).hom.toNatTrans.app (𝟙 (unop a.1))) ≫
            (f.2.naturality f.1).hom.toNatTrans.app ((Y.app a.1).toFunctor.obj (𝟙 (unop a.1))) =
    ((f.2.app b.1).toFunctor.map ((X.app b.1).toFunctor.map (λ_ f.1.unop).hom) ≫
        (f.2.app b.1).toFunctor.map ((X.app b.1).toFunctor.map (ρ_ f.1.unop).inv) ≫
          (f.2.app b.1).toFunctor.map ((X.naturality f.1).hom.toNatTrans.app (𝟙 (unop a.1))) ≫
            (f.2.naturality f.1).hom.toNatTrans.app
              ((X.app a.1).toFunctor.obj (𝟙 (unop a.1)))) ≫
      (b.2.map f.1).toFunctor.map ((f.2.app a.1).toFunctor.map
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
  erw [reassoc_of% h2', h3]
  simp only [Category.assoc]
  rfl

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
  -- PARKED (v4.33).  The statement is right -- it is `Z.naturality_naturality` at the point
  -- `𝟙 (unop a.1)`, reconciled with right-unitor naturality -- but the proof cannot get started:
  -- neither `rw [Category.assoc]` nor `simp only [Category.assoc]` will fire on the right-hand
  -- side's `(_ ≫ _) ≫ _`, and Lean's note says the target is not type-correct at `implicit`
  -- transparency.  That is an instance diamond in the statement's own elaboration, not damage
  -- from a prior tactic: no tactic has run yet.
  --
  -- Next move: diagnose with `convert` (its `e_N✝` hypotheses name the mismatched instances),
  -- or restate the lemma so both sides spell `≫` through the same path -- most likely by
  -- phrasing it in `Cat.Hom₂` rather than in the fibre category.
  -- Prior version: `git show comp-core:Biyoneda/Forwards.lean`.
  sorry

/--
The component core of the `naturality_naturality` obligation of `yonedaLemmaForwards`, stated
in the unlifted fibre (the `.down` of the lifted 2-cells).

It says the forward naturality isomorphism is natural in the 2-cell `η = (η.1, η.2)`.  The
proof splits `η` into its two components: the modification part `η.2` contributes
`modification_naturality_app`, the base 2-cell `η.1` contributes `g.2.naturality_naturality`,
and the evaluation point is handled by `forwards_naturality_naturality_unitor`.
-/
lemma forwards_naturality_naturality_core {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} {f g : a ⟶ b}
    (η : f ⟶ g) (Z : Pseudofunctor.StrongTrans (yoneda₀ (unop a.1)) a.2) :
    (((yonedaPairing.map₂ η).toNatTrans.app Z).as.app b.1).toNatTrans.app (𝟙 (unop b.1)) ≫
        ((g.2.app b.1).toFunctor.map
            ((Z.app b.1).toFunctor.map ((λ_ g.1.unop).hom ≫ (ρ_ g.1.unop).inv) ≫
              ((Cat.Hom.toNatIso (Z.naturality g.1)).app (𝟙 (unop a.1))).hom) ≫
          ((Cat.Hom.toNatIso (g.2.naturality g.1)).app
              ((Z.app a.1).toFunctor.obj (𝟙 (unop a.1)))).hom) =
    ((f.2.app b.1).toFunctor.map
            ((Z.app b.1).toFunctor.map ((λ_ f.1.unop).hom ≫ (ρ_ f.1.unop).inv) ≫
              ((Cat.Hom.toNatIso (Z.naturality f.1)).app (𝟙 (unop a.1))).hom) ≫
          ((Cat.Hom.toNatIso (f.2.naturality f.1)).app
              ((Z.app a.1).toFunctor.obj (𝟙 (unop a.1)))).hom) ≫
      (yonedaEvaluation'.map₂ η).toNatTrans.app ((Z.app a.1).toFunctor.obj (𝟙 (unop a.1))) := by
  simp only [yonedaPairing_map₂]
  dsimp only [Cat.toCatHom₂_toNatTrans, yonedaPairingMap₂, yonedaEvaluation',
    postcomposing₂, postcomposingCat]
  simp only [NatTrans.comp_app, precomposing_map_app, postcomposing_map_app,
    precomposing_obj, postcomposing_obj, precomp_map,
    Cat.toCatHom₂_toNatTrans, whiskerLeft_as_app, whiskerRight_as_app,
    homCategory_comp_as_app,
    Cat.Hom.toNatTrans_comp, Cat.whiskerLeft_toNatTrans, Cat.whiskerRight_toNatTrans,
    whiskerLeft_app, whiskerRight_app, Iso.app_hom, Cat.Hom.toNatIso]
  simp only [Pseudofunctor.StrongTrans.comp_app, Functor.comp_map,
    postcomp₂, postcomposingCat, postcomp_obj, Cat.Hom.comp_toFunctor,
    Bicategory.id_whiskerLeft]
  have h1 := modification_naturality_app η.2 f.1 ((Z.app a.1).toFunctor.obj (𝟙 (unop a.1)))
  have h2 := g.2.naturality_naturality_app η.1
    ((Z.app a.1).toFunctor.obj (𝟙 (unop a.1)))
  dsimp at h1 h2
  -- PARKED (v4.33).  `simp only [Category.assoc]` reports no progress and Lean notes the target
  -- is not type-correct at `implicit` transparency, naming the mismatch: `Z` is typed
  -- `(yoneda₀ (unop a.1)).StrongTrans a.2` where the goal wants `↑(yonedaPairing.obj a)`.
  -- Retyping `Z` past that coercion is the documented move for an *element*; tried, and the
  -- `dsimp only` above still leaves the two spellings apart.  This lemma also calls
  -- `forwards_naturality_naturality_unitor`, which is parked, so it is blocked regardless.
  sorry

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
-- the descent through the composite's `mapId` into `homPseudo`'s unitor iso, run with
-- transparency relaxed, does not fit the default budget; 1M is ~2x the measured floor
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
  -- PARKED (v4.33).  `Z.naturality_id` is the whole mathematical input; the descent just
  -- follows the composite's `mapId` down to `homPseudo`'s unitor iso.  The `rw [hZ]` now hits a
  -- `(deterministic) timeout at isDefEq` at 1e6 heartbeats.
  --
  -- Strongly suspected knock-on: the descent `dsimp only [...]` unfolds `homPseudo`, whose
  -- coherence fields are sorried as of this branch, so the unfolded term now carries `sorryAx`
  -- subterms with large types.  Re-check this the moment Gadgets is restored -- do NOT raise
  -- maxHeartbeats to paper over it.
  sorry

/-- The head unit-coherence in `B`'s hom-categories underlying `naturality_comp`: `u_{f≫g}`
composed with the yoneda `mapComp` equals the postcomp₂ reorganisation with `u_g`, `u_f`.  Both
sides are pure associator/unitor data — `bicategory` after unfolding to `α_`/`λ_`/`ρ_`. -/
lemma forwards_naturality_comp_head {a b c : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b) (g : b ⟶ c) :
    ((λ_ (f.1 ≫ g.1).unop).hom ≫ (ρ_ (f.1 ≫ g.1).unop).inv) ≫
        ((yoneda₀ (unop a.1)).mapComp f.1 g.1).hom.toNatTrans.app (𝟙 (unop a.1)) =
    (((postcompComp₂ g.1.unop f.1.unop).hom.as.app c.1).toNatTrans.app (𝟙 (unop c.1)) ≫
        ((postcomp₂ f.1.unop).app c.1).toFunctor.map ((λ_ g.1.unop).hom ≫ (ρ_ g.1.unop).inv) ≫
        ((postcomp₂ f.1.unop).naturality g.1).hom.toNatTrans.app (𝟙 (unop b.1))) ≫
      ((yoneda₀ (unop a.1)).map g.1).toFunctor.map ((λ_ f.1.unop).hom ≫ (ρ_ f.1.unop).inv) := by
  erw [show ((yoneda₀ (unop a.1)).map g.1).toFunctor.map ((λ_ f.1.unop).hom ≫ (ρ_ f.1.unop).inv)
        = g.1.unop ◁ ((λ_ f.1.unop).hom ≫ (ρ_ f.1.unop).inv) from rfl,
     show ((postcomp₂ f.1.unop).app c.1).toFunctor.map ((λ_ g.1.unop).hom ≫ (ρ_ g.1.unop).inv)
        = ((λ_ g.1.unop).hom ≫ (ρ_ g.1.unop).inv) ▷ f.1.unop from rfl]
  dsimp only [postcompComp₂, yoneda, postcomp₂, yoneda₀,
    associatorNatIsoRightCat, associatorNatIsoMiddleCat, associatorNatIsoLeftCat]
  simp only [Cat.Hom.isoMk_hom, Cat.Hom.isoMk_inv, Cat.toCatHom₂_toNatTrans, Iso.symm_hom,
    NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app, isoMk_inv_as_app]
  -- PARKED (v4.33).  Both sides are pure associator/unitor data and `bicategory` runs, but
  -- leaves a residual -- the same shape as `homPseudo`'s two unitor coherence fields in
  -- Gadgets.lean, and probably the same cause.  Fix those first.
  sorry

-- set_option maxHeartbeats 500000 in
-- the long descent + `naturality_comp_hom_app` telescoping + three `u_f`-transport squares
-- exceed the default budget (measured floor ≈ 350k, so ~1.4× margin); does not fit in 200k
/-- Core of `naturality_comp` for `yonedaLemmaForwards` (unlifted fibre form). -/
lemma forwards_naturality_comp_core {a b c : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b) (g : b ⟶ c)
    (Z : Pseudofunctor.StrongTrans (yoneda₀ (unop a.1)) a.2) :
    (((f.2 ≫ g.2).app c.1).toFunctor.map
          ((Z.app c.1).toFunctor.map
              ((λ_ (f.1 ≫ g.1).unop).hom ≫ (ρ_ (f.1 ≫ g.1).unop).inv) ≫
            (Z.naturality (f.1 ≫ g.1)).hom.toNatTrans.app (𝟙 (unop a.1))) ≫
        ((f.2 ≫ g.2).naturality (f.1 ≫ g.1)).hom.toNatTrans.app
          ((Z.app a.1).toFunctor.obj (𝟙 (unop a.1)))) ≫
      (yonedaEvaluation'.mapComp f g).hom.toNatTrans.app
        ((Z.app a.1).toFunctor.obj (𝟙 (unop a.1))) =
    (((yonedaPairing.mapComp f g).hom.toNatTrans.app Z).as.app c.1).toNatTrans.app
        (𝟙 (unop c.1)) ≫
      ((g.2.app c.1).toFunctor.map
            ((((yonedaPairing.map f).toFunctor.obj Z).app c.1).toFunctor.map
                ((λ_ g.1.unop).hom ≫ (ρ_ g.1.unop).inv) ≫
              (((yonedaPairing.map f).toFunctor.obj Z).naturality g.1).hom.toNatTrans.app
                (𝟙 (unop b.1))) ≫
          (g.2.naturality g.1).hom.toNatTrans.app
            ((((yonedaPairing.map f).toFunctor.obj Z).app b.1).toFunctor.obj (𝟙 (unop b.1)))) ≫
        (yonedaEvaluation'.map g).toFunctor.map
          ((f.2.app b.1).toFunctor.map
              ((Z.app b.1).toFunctor.map ((λ_ f.1.unop).hom ≫ (ρ_ f.1.unop).inv) ≫
                (Z.naturality f.1).hom.toNatTrans.app (𝟙 (unop a.1))) ≫
            (f.2.naturality f.1).hom.toNatTrans.app
              ((Z.app a.1).toFunctor.obj (𝟙 (unop a.1)))) := by
  -- Pending: the statement mentions `yonedaPairing.mapComp`, which the composite defines
  -- differently (not defeq), so this needs a genuine re-proof rather than a re-spelling.
  sorry

-- `linter.flexible` wants the two non-terminal `simp`s below squeezed to `simp only [...]`.
-- The suggested lists run to 17 and 30 lemma names, which the pending v4.30 -> v4.33 walk would
-- invalidate wholesale; and both are followed by a match against a *named* lemma, so simp drift
-- fails loudly rather than silently. Revisit after the bump.
set_option linter.flexible false in
set_option backward.isDefEq.respectTransparency false in
/-- The data for `yonedaLemmaForwards`, stated against the *unlifted* `yonedaEvaluation'`.
`StrongTransIntoCats.lift` then supplies the lifted strong transformation. -/
def yonedaLemmaForwardsData :
    StrongTransIntoCats (@yonedaPairing B _) (@yonedaEvaluation' B _) where
  app := yonedaLemmaForwardsFunctor
  naturality {a b} f :=
    NatIso.ofComponents
      (fun X =>
        (f.2.app b.1).toFunctor.mapIso
            ((X.app b.1).toFunctor.mapIso (λ_ f.1.unop ≪≫ (ρ_ f.1.unop).symm) ≪≫
              (Cat.Hom.toNatIso (X.naturality f.1)).app (𝟙 (unop a.1))) ≪≫
          (Cat.Hom.toNatIso (f.2.naturality f.1)).app
            ((X.app a.1).toFunctor.obj (𝟙 (unop a.1))))
      (by
        intro X Y h
        -- The mathematical content is exactly `forwards_naturality_core`; the simp set
        -- descends the composite pairing to its shape.  `convert` then absorbs both the
        -- `Cat`-instance mismatch (the two sides spell the fibre category differently, which is
        -- why `Functor.map_comp` will not fire here) and the residual regrouping.
        -- PARKED (v4.33).  `forwards_naturality_core` above is proved and is exactly the
        -- mathematical content; what fails is the reconciliation -- `convert ... using 2` no
        -- longer closes the residual after the descent simp set.
        have key := forwards_naturality_core f h
        simp only [Category.assoc] at key
        sorry)
  naturality_naturality' {a b} {f g} η Z := forwards_naturality_naturality_core η Z
  naturality_id' a Z := by
    -- PARKED (v4.33), inherited: `forwards_naturality_id_core` is itself parked above, so this
    -- field could only inherit that sorry even with a working reconciliation.
    have core := forwards_naturality_id_core a Z
    sorry
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
