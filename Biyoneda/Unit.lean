/-
Copyright (c) 2026 Spencer Woolfson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Spencer Woolfson
-/
import Biyoneda.Forwards
import Biyoneda.Backwards

/-!
# The unit and counit of the Yoneda equivalence

The two round-trip isomorphisms witnessing that `yonedaLemmaForwards` and
`yonedaLemmaBackwards` are mutually inverse:

* `yonedaHomInvId : yonedaLemmaForwards ≫ yonedaLemmaBackwards ≅ 𝟙 yonedaPairing`
* `yonedaInvHomId : yonedaLemmaBackwards ≫ yonedaLemmaForwards ≅ 𝟙 yonedaEvaluation`

Each is assembled inside-out: a component iso at a point, then at a fibre, then a natural
iso, then the modification.
-/

namespace Biyoneda

open CategoryTheory Bicategory Bicategory.Opposite Opposite Pseudofunctor StrongTrans Functor
open scoped Pseudofunctor.StrongTrans

universe u v w v₁ v₂ u₁ u₂

attribute [local instance] uliftCategory


variable {B : Type u} [Bicategory.{w, v} B]

universe w₁

/-- Component form of the naturality constraint of a composite strong transformation.

Currently unused: it is staged for the parked `yonedaHomInvId` / `yonedaInvHomId` naturality
squares, whose notes call for exactly this decomposition of `(η ≫ θ).naturality`. -/
lemma strongTrans_comp_naturality_hom_app {F G H : Bᵒᵖ ⥤ᵖ Cat.{w, v}} (η : F ⟶ G) (θ : G ⟶ H)
    {X Y : Bᵒᵖ} (k : X ⟶ Y) (x : ↑(F.obj X)) :
    ((η ≫ θ).naturality k).hom.toNatTrans.app x =
      (θ.app Y).toFunctor.map ((η.naturality k).hom.toNatTrans.app x) ≫
        (θ.naturality k).hom.toNatTrans.app ((η.app X).toFunctor.obj x) := by
  simp only [Pseudofunctor.StrongTrans.categoryStruct_comp_naturality_hom]
  iterate (first | erw [eqToHom_refl] | erw [Category.id_comp] | erw [Category.comp_id])
  rfl

/--
The canonical isomorphism used to build the unit of the Yoneda equivalence.

Given:
* `a = (b₀, F)` — a pair in `Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat)`,
* `b : Bᵒᵖ` — the component,
* `x : yonedaPairing.obj a` — a strong transformation `yoneda₀ b₀ ⟶ F`,
* `f : unop b ⟶ b₀` — an object of `(yoneda₀ b₀).obj b`,

this is the isomorphism
  `(yonedaLemmaBackwards.app a ∘ yonedaLemmaForwards.app a)(x).app b f  ≅  x.app b f`

built as the composite:
  `(x.naturality (op f)).inv.app (𝟙 b₀)  ≫  (x.app b).map (ρ_ f).hom`

where `ρ_ f : f ≫ 𝟙 b₀ ≅ f` is the right unitor in `B`.
-/
def yonedaUnitAppIso (a : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat)) (b : Bᵒᵖ) (x : ↑(yonedaPairing.obj a))
    (f : ↑((yoneda₀ (unop a.1)).obj b)) :=
  (Iso.trans
    (Iso.symm (Iso.app (Cat.Hom.toNatIso (x.naturality (Quiver.Hom.op f))) (𝟙 (unop a.1))))
    ((x.app b).toFunctor.mapIso (rightUnitor f)))

set_option linter.flexible false in
/--
For a pair `a = (b₀, F)`, a component `b : Bᵒᵖ`, and a strong transformation
`x : yoneda₀ b₀ ⟶ F`, the natural transformation from the `b`-component of the roundtrip
`(yonedaLemmaBackwards ∘ yonedaLemmaForwards)(x)` back to the `b`-component of `x`.

Each component at `f : unop b ⟶ b₀` is `(yonedaUnitAppIso a b x f).hom`.

This is the innermost layer of the unit coherence; it is assembled into a full modification
by `yonedaHomInvIdNatIso` and then into the unit iso by `yonedaHomInvId`.
-/
def yonedaHomInvIdFunctorIso {a : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat)} (b : Bᵒᵖ) (x : ↑(yonedaPairing.obj a)) :
    (((yonedaLemmaBackwards.app a).toFunctor.obj
        ((yonedaLemmaForwards.app a).toFunctor.obj x)).app b).toFunctor ≅
    (x.app b).toFunctor := by
    refine NatIso.ofComponents (fun y ↦ yonedaUnitAppIso a b x y) ?_
    -- Pending: goal shape changed with the composite pairing.
    sorry

/--
At a fixed pair `a = (b₀, F)` and a strong transformation `x : yoneda₀ b₀ ⟶ F`, the
isomorphism
  `(yonedaLemmaForwards.app a ≫ yonedaLemmaBackwards.app a).toFunctor.obj x ≅ x`
in `yonedaPairing.obj a`.

This is the component of the unit natural isomorphism `yonedaHomInvIdNatIso` at the object
`x`, assembled by applying `yonedaHomInvIdFunctorIso` at each component `b : Bᵒᵖ`.
-/
def yonedaHomInvIdObjIso (a : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat)) (x : ↑(yonedaPairing.obj a)) :
    (yonedaLemmaForwards.app a ≫ yonedaLemmaBackwards.app a).toFunctor.obj x ≅
    (𝟭 ↑(yonedaPairing.obj a)).obj x := by
    refine StrongTrans.isoMk (fun b ↦ (Cat.Hom.isoMk (yonedaHomInvIdFunctorIso b x))) ?_
    -- Pending: goal shape changed with the composite pairing.
    sorry

/--
For a pair `a = (b₀, F)`, the modification
`(yonedaLemmaForwards.app a ≫ yonedaLemmaBackwards.app a)(x) ⟶ x`
in `yonedaPairing.obj a`, for each `x : yonedaPairing.obj a`.

This is the component of the unit morphism `yonedaHomInvId.hom` at the object `a`, assembled
component-wise using `yonedaHomInvIdObjIso` for each `b : Bᵒᵖ`.
-/
def yonedaHomInvIdNatIso (a : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat)) :
    (yonedaLemmaForwards.app a ≫ yonedaLemmaBackwards.app a).toFunctor ≅
    (𝟭 ↑(yonedaPairing.obj a)) := by
  refine NatIso.ofComponents (fun x ↦ yonedaHomInvIdObjIso a x) ?_
  -- Pending: goal shape changed with the composite pairing.
  sorry

/-- The unit, built in the `StrongTransIntoCats` world.

This is the whole mathematical content of `yonedaHomInvId`, and it is stated where the
obligation is tractable: `ModificationIntoCats.isoMk` takes the natural isomorphisms we already
have, one per object, and asks for the modification square **at a point** -- no `Cat` 2-cells,
no associators, and only the forward direction (the inverse comes for free). -/
def yonedaHomInvIdIso :
    (yonedaLemmaForwardsData.comp yonedaLemmaBackwardsData) ≅
      (StrongTransIntoCats.Id (F := @yonedaPairing B _)) :=
  ModificationIntoCats.isoMk (fun a ↦ yonedaHomInvIdNatIso a) (fun {a b} f x ↦ by
    sorry)

/--
The *unit isomorphism* `yonedaLemmaForwards ≫ yonedaLemmaBackwards ≅ 𝟙 yonedaPairing`.

This witnesses that composing the "evaluate at identity" map with the Yoneda embedding returns
the original strong transformation, up to a canonical isomorphism.  It is the `homInvId` field
of `yonedaLemma`.
-/
def yonedaHomInvId : yonedaLemmaForwards ≫ yonedaLemmaBackwards ≅ 𝟙 (@yonedaPairing B _) := by
  refine StrongTrans.isoMk (fun a ↦ Cat.Hom.isoMk (yonedaHomInvIdNatIso a)) ?_
  intro a b f
  -- `rw1`/`rw3` used to strip the `fun a ↦ …` applications; Lean beta-reduces them on its own
  -- now, so `erw` finds no pattern for them.  Only the `isoMk`-to-`toCatHom₂` step is real.
  have rw2 : (Cat.Hom.isoMk (yonedaHomInvIdNatIso b)).hom =
      NatTrans.toCatHom₂ ((yonedaHomInvIdNatIso b).hom) := rfl
  erw [rw2]
  clear rw2
  refine Cat.Hom₂.ext_iff.mpr ?_
  ext x
  simp only [Cat.Hom.toNatTrans_comp, NatTrans.comp_app, Cat.whiskerLeft_toNatTrans,
    Cat.whiskerRight_toNatTrans, whiskerLeft_app, whiskerRight_app,
    Cat.Hom.isoMk_hom, NatTrans.toCatHom₂_toNatTrans]
  -- The two bridges turn `(forwards ≫ backwards).naturality` -- a five-factor associator
  -- sandwich -- into `comp`'s naturality, and `(𝟙 _).naturality` into `Id`'s.  What is left is
  -- exactly the modification square of `yonedaHomInvIdIso`, at a point.
  dsimp only [yonedaLemmaForwards, yonedaLemmaBackwards]
  erw [StrongTransIntoCats.lift_comp_liftDom_naturality_app,
    StrongTransIntoCats.Id_naturality_app]
  exact yonedaHomInvIdIso.hom.naturality' f x

/--
At a fixed pair `a = (b₀, F)`, the natural isomorphism from the roundtrip functor
`(yonedaLemmaBackwards.app a ≫ yonedaLemmaForwards.app a)` to the identity on
`yonedaEvaluation.obj a`.

This is the component of the counit `yonedaInvHomId` at the object `a`, witnessing that
`yonedaLemmaForwards(yonedaLemmaBackwards(s)) ≅ s` for `s : F.obj b₀`.
-/
def yonedaInvHomIdNatIso (a : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat)) :
    (yonedaLemmaBackwards.app a ≫ yonedaLemmaForwards.app a).toFunctor ≅
    (𝟭 ↑(yonedaEvaluation.obj a)) := by
  refine NatIso.ofComponents ?_ ?_
  · intro ⟨x⟩
    dsimp [yonedaLemmaForwards, ULiftHom.objDown, yonedaLemmaBackwards, Quiver.Hom]
    let I1 := (Cat.Hom.toNatIso (a.2.mapId a.1)).app x
    exact ULiftHom.up.mapIso
      ((@ULift.upFunctor.{_, _, max (max u v) w} (↑(yonedaEvaluation'.obj a)) _).mapIso I1)
  · rintro ⟨x⟩ ⟨y⟩ ⟨f⟩
    dsimp [yonedaLemmaForwards, ULiftHom.up]
    have h := (a.2.mapId a.1).hom.toNatTrans.naturality f
    dsimp at h
    exact Quiver.homOfEq_injective rfl rfl (congrArg (ULiftHom.up.map) h)

/--
The *counit isomorphism* `yonedaLemmaBackwards ≫ yonedaLemmaForwards ≅ 𝟙 yonedaEvaluation`.

This witnesses that composing the Yoneda embedding with "evaluate at identity" returns the
original element of `F.obj b`, up to a canonical isomorphism.  It is the `invHomId` field
of `yonedaLemma`.
-/
def yonedaInvHomId : yonedaLemmaBackwards ≫ yonedaLemmaForwards ≅ 𝟙 (@yonedaEvaluation B _) := by
  refine StrongTrans.isoMk (fun a ↦ Cat.Hom.isoMk (yonedaInvHomIdNatIso a)) ?_
  intro a b f
  -- `rw1`/`rw3` used to strip the `fun a ↦ …` applications; Lean beta-reduces them on its own
  -- now, so `erw` finds no pattern for them.  Only the `isoMk`-to-`toCatHom₂` step is real.
  have rw2 : (Cat.Hom.isoMk (yonedaInvHomIdNatIso b)).hom =
      NatTrans.toCatHom₂ ((yonedaInvHomIdNatIso b).hom) := rfl
  erw [rw2]
  clear rw2
  refine Cat.Hom₂.ext_iff.mpr ?_
  ext x
  simp only [Cat.Hom.toNatTrans_comp, NatTrans.comp_app, Cat.whiskerLeft_toNatTrans,
    Cat.whiskerRight_toNatTrans, whiskerLeft_app, whiskerRight_app,
    Cat.Hom.isoMk_hom, NatTrans.toCatHom₂_toNatTrans]
  -- Parked (2026-07-29): same shape and size as yonedaHomInvId's naturality goal (see the note
  -- there). After the descent above, the goal is
  --   (yonedaInvHomIdNatIso b).hom.app ((yonedaEvaluation.map f).obj x) ≫
  --     ((𝟙 yonedaEvaluation).naturality f).hom.app x
  --   = ((yonedaLemmaBackwards ≫ yonedaLemmaForwards).naturality f).hom.app x ≫
  --     (yonedaEvaluation.map f).map ((yonedaInvHomIdNatIso a).hom.app x)
  -- Next step if resumed: the same `dsimp only [CategoryStruct.id, CategoryStruct.comp,
  -- StrongTrans.categoryStruct, StrongTrans.id, StrongTrans.vcomp, StrongTrans.mkOfOplax,
  -- Oplax.StrongTrans.mkOfOplax, Oplax.StrongTrans.vcomp]` unfold used there (~5 min/cycle),
  -- then the ingredient-square recipe applied to `yonedaLemmaBackwards.naturality f` and
  -- `yonedaLemmaForwards.naturality f` in turn.
  sorry

end Biyoneda
