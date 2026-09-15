/-
Copyright (c) 2026 Spencer Woolfson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Spencer Woolfson
-/
module

public import Biyoneda.Forwards
public import Biyoneda.Backwards

/-!
# The unit and counit of the Yoneda equivalence

The two round-trip isomorphisms witnessing that `yonedaLemmaForwards` and
`yonedaLemmaBackwards` are mutually inverse:

* `yonedaHomInvId : yonedaLemmaForwards ≫ yonedaLemmaBackwards ≅ 𝟙 yonedaPairing`
* `yonedaInvHomId : yonedaLemmaBackwards ≫ yonedaLemmaForwards ≅ 𝟙 yonedaEvaluation`

Each is assembled inside-out: a component iso at a point, then at a fibre, then a natural
iso, then the modification.
-/

@[expose] public section

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


/-- The naturality square of `yonedaUnitAppIso`, in clean unbundled variables.

For a 2-cell `θ : X ⟶ Y` in the hom-category `unop b ⟶ b₀`, the roundtrip functor acts by
`G.map₂ θ.op` at the evaluation point, and the claim is that this commutes with the two
copies of the unit component.  `strongTrans_naturality_conj` solves `α`'s
`naturality_naturality` for the bare `map₂` image, which turns the left-hand side into the
right one up to a single 2-cell identity in `B` -- `rightUnitor_naturality`.

Stated against an arbitrary `α : yoneda₀ b₀ ⟶ G` rather than inside the definition: the goal
there mentions `(α.app _).obj (𝟙 b₀)`, which is not type-correct at `implicit` transparency,
so no rewriting tactic can fire on it.  Every step below is therefore a term. -/
lemma unit_functor_core {b₀ : B} {G : Bᵒᵖ ⥤ᵖ Cat.{w, v}} (α : yoneda₀ b₀ ⟶ G) (b : Bᵒᵖ)
    {X Y : unop b ⟶ b₀} (θ : X ⟶ Y) :
    (G.map₂ (op2 θ)).toNatTrans.app ((α.app (op b₀)).toFunctor.obj (𝟙 b₀)) ≫
      ((α.naturality (Quiver.Hom.op Y)).inv.toNatTrans.app (𝟙 b₀) ≫
        (α.app b).toFunctor.map (ρ_ Y).hom)
      = ((α.naturality (Quiver.Hom.op X)).inv.toNatTrans.app (𝟙 b₀) ≫
          (α.app b).toFunctor.map (ρ_ X).hom) ≫ (α.app b).toFunctor.map θ := by
  have hconj : (α.app b).toFunctor.map (θ ▷ 𝟙 b₀)
      = (α.naturality (Quiver.Hom.op X)).hom.toNatTrans.app (𝟙 b₀) ≫
        (G.map₂ (op2 θ)).toNatTrans.app ((α.app (op b₀)).toFunctor.obj (𝟙 b₀)) ≫
        (α.naturality (Quiver.Hom.op Y)).inv.toNatTrans.app (𝟙 b₀) :=
    strongTrans_naturality_conj α (op2 θ) (𝟙 b₀)
  have hcancel := Cat.Hom.inv_hom_id_toNatTrans_app (α.naturality (Quiver.Hom.op X)) (𝟙 b₀)
  have hkey : (α.naturality (Quiver.Hom.op X)).inv.toNatTrans.app (𝟙 b₀) ≫
        (α.app b).toFunctor.map (θ ▷ 𝟙 b₀)
      = (G.map₂ (op2 θ)).toNatTrans.app ((α.app (op b₀)).toFunctor.obj (𝟙 b₀)) ≫
        (α.naturality (Quiver.Hom.op Y)).inv.toNatTrans.app (𝟙 b₀) :=
    (congrArg (fun t => (α.naturality (Quiver.Hom.op X)).inv.toNatTrans.app (𝟙 b₀) ≫ t)
        hconj).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun t => t ≫ _) hcancel).trans (Category.id_comp _)))
  have hunit : (α.app b).toFunctor.map (θ ▷ 𝟙 b₀) ≫ (α.app b).toFunctor.map (ρ_ Y).hom
      = (α.app b).toFunctor.map (ρ_ X).hom ≫ (α.app b).toFunctor.map θ :=
    ((α.app b).toFunctor.map_comp _ _).symm.trans
      ((congrArg (α.app b).toFunctor.map (rightUnitor_naturality θ)).trans
        ((α.app b).toFunctor.map_comp _ _))
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun t => t ≫ (α.app b).toFunctor.map (ρ_ Y).hom) hkey.symm) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun t =>
    (α.naturality (Quiver.Hom.op X)).inv.toNatTrans.app (𝟙 b₀) ≫ t) hunit) ?_
  exact (Category.assoc _ _ _).symm

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
    intro X Y θ
    exact unit_functor_core x b θ


set_option backward.isDefEq.respectTransparency false in
/-- The modification square of `yonedaHomInvIdObjIso`, at a point, in clean unbundled variables.

For `f : c ⟶ d` in `Bᵒᵖ` and `W : unop c ⟶ b₀`, the roundtrip's naturality at `f` is `G`'s own
`mapComp` constraint, and the claim is that the two unit components -- at `W` and at
`f.unop ≫ W` -- intertwine it with `α`'s naturality.  Three moves: `α`'s `naturality_comp`
solved for the `mapComp` (`hA`), the `hom`/`inv` cancellation it exposes (`hK`), and one
naturality square of `α.naturality f` (`hS`, from `strongTrans_naturality_slide`).  What is
left is the bicategory identity `(ρ_ (f ≫ g)).hom = (α_ f g (𝟙 _)).hom ≫ f ◁ (ρ_ g).hom`.

The `backward.isDefEq.respectTransparency` opt-out is what lets `rw` fire at all: the statement
mentions `(α.app _).obj (𝟙 b₀)`, which is not type-correct at `implicit` transparency, so every
pattern whose instantiation has to elaborate that subterm is otherwise rejected. -/
lemma unit_obj_core {b₀ : B} {G : Bᵒᵖ ⥤ᵖ Cat.{w, v}} (α : yoneda₀ b₀ ⟶ G) {c d : Bᵒᵖ}
    (f : c ⟶ d) (W : unop c ⟶ b₀) :
    ((α.naturality (Quiver.Hom.op W ≫ f)).inv.toNatTrans.app (𝟙 b₀) ≫
        (α.app d).toFunctor.map (ρ_ (f.unop ≫ W)).hom) ≫
      (α.naturality f).hom.toNatTrans.app W
      = (G.mapComp (Quiver.Hom.op W) f).hom.toNatTrans.app
          ((α.app (op b₀)).toFunctor.obj (𝟙 b₀)) ≫
        (G.map f).toFunctor.map
          ((α.naturality (Quiver.Hom.op W)).inv.toNatTrans.app (𝟙 b₀) ≫
            (α.app c).toFunctor.map (ρ_ W).hom) := by
  have hcomp := (Pseudofunctor.StrongTrans.naturality_comp_app α (Quiver.Hom.op W) f (𝟙 b₀)).symm
  have hPH := Cat.Hom.inv_hom_id_toNatTrans_app (α.naturality (Quiver.Hom.op W ≫ f)) (𝟙 b₀)
  have hHN := Cat.Hom.hom_inv_id_toNatTrans_app (α.naturality (Quiver.Hom.op W)) (𝟙 b₀)
  have hNH := Cat.Hom.inv_hom_id_toNatTrans_app (α.naturality f) W
  have hslide : (α.naturality f).hom.toNatTrans.app
        (((yoneda₀ b₀).map (Quiver.Hom.op W)).toFunctor.obj (𝟙 b₀)) ≫
      (G.map f).toFunctor.map ((α.app c).toFunctor.map (ρ_ W).hom) ≫
        (α.naturality f).inv.toNatTrans.app W
      = (α.app d).toFunctor.map (f.unop ◁ (ρ_ W).hom) :=
    strongTrans_naturality_slide α f (ρ_ W).hom
  have hA : (G.mapComp (Quiver.Hom.op W) f).hom.toNatTrans.app
        ((α.app (op b₀)).toFunctor.obj (𝟙 b₀))
      = (α.naturality (Quiver.Hom.op W ≫ f)).inv.toNatTrans.app (𝟙 b₀) ≫
        ((α.app d).toFunctor.map
            (((yoneda₀ b₀).mapComp (Quiver.Hom.op W) f).hom.toNatTrans.app (𝟙 b₀)) ≫
          (α.naturality f).hom.toNatTrans.app
              (((yoneda₀ b₀).map (Quiver.Hom.op W)).toFunctor.obj (𝟙 b₀)) ≫
            (G.map f).toFunctor.map
              ((α.naturality (Quiver.Hom.op W)).hom.toNatTrans.app (𝟙 b₀))) := by
    rw [hcomp, ← Category.assoc, hPH, Category.id_comp]
  have hK : (G.map f).toFunctor.map
        ((α.naturality (Quiver.Hom.op W)).hom.toNatTrans.app (𝟙 b₀)) ≫
      (G.map f).toFunctor.map
        ((α.naturality (Quiver.Hom.op W)).inv.toNatTrans.app (𝟙 b₀) ≫
          (α.app c).toFunctor.map (ρ_ W).hom)
      = (G.map f).toFunctor.map ((α.app c).toFunctor.map (ρ_ W).hom) := by
    rw [← Functor.map_comp, ← Category.assoc, hHN, Category.id_comp]
  have hS : (α.naturality f).hom.toNatTrans.app
        (((yoneda₀ b₀).map (Quiver.Hom.op W)).toFunctor.obj (𝟙 b₀)) ≫
      (G.map f).toFunctor.map ((α.app c).toFunctor.map (ρ_ W).hom)
      = (α.app d).toFunctor.map (f.unop ◁ (ρ_ W).hom) ≫
        (α.naturality f).hom.toNatTrans.app W := by
    rw [← hslide, Category.assoc, Category.assoc, hNH]
    exact (congrArg (fun t => (α.naturality f).hom.toNatTrans.app
      (((yoneda₀ b₀).map (Quiver.Hom.op W)).toFunctor.obj (𝟙 b₀)) ≫ t)
      (Category.comp_id ((G.map f).toFunctor.map ((α.app c).toFunctor.map (ρ_ W).hom)))).symm
  rw [hA, Category.assoc, Category.assoc, Category.assoc, Category.assoc, hK, hS]
  refine congrArg
    (fun t => (α.naturality (Quiver.Hom.op W ≫ f)).inv.toNatTrans.app (𝟙 b₀) ≫ t) ?_
  rw [← Category.assoc, ← Functor.map_comp]
  refine congrArg
    (fun t => (α.app d).toFunctor.map t ≫ (α.naturality f).hom.toNatTrans.app W) ?_
  exact (by bicategory :
    (ρ_ (f.unop ≫ W)).hom = (α_ f.unop W (𝟙 b₀)).hom ≫ f.unop ◁ (ρ_ W).hom)

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
    intro c d f
    refine Cat.Hom₂.ext_iff.mpr ?_
    ext W
    simp only [Cat.Hom.toNatTrans_comp, NatTrans.comp_app, Cat.whiskerLeft_toNatTrans,
      Cat.whiskerRight_toNatTrans, whiskerLeft_app, whiskerRight_app]
    exact unit_obj_core x f W


set_option backward.isDefEq.respectTransparency false in
/-- The naturality square of `yonedaHomInvIdObjIso` in the *object* variable, at a point.

For a modification `m : X ⟶ Y` between two strong transformations `yoneda₀ b₀ ⟶ G`, the
roundtrip sends `m` to `G.map V.op` applied to `m`'s component at the identity.  The
modification axiom at `𝟙 b₀` (`hM`) turns that into `m`'s component at `V ≫ 𝟙 b₀`, conjugated
by the two naturality isos; the residual is one naturality square of the natural
transformation `m.as.app b` at `(ρ_ V).hom` (`hnat`). -/
lemma unit_natiso_core {b₀ : B} {G : Bᵒᵖ ⥤ᵖ Cat.{w, v}} {X Y : yoneda₀ b₀ ⟶ G} (m : X ⟶ Y)
    (b : Bᵒᵖ) (V : unop b ⟶ b₀) :
    (G.map (Quiver.Hom.op V)).toFunctor.map ((m.as.app (op b₀)).toNatTrans.app (𝟙 b₀)) ≫
      ((Y.naturality (Quiver.Hom.op V)).inv.toNatTrans.app (𝟙 b₀) ≫
        (Y.app b).toFunctor.map (ρ_ V).hom)
      = ((X.naturality (Quiver.Hom.op V)).inv.toNatTrans.app (𝟙 b₀) ≫
          (X.app b).toFunctor.map (ρ_ V).hom) ≫ (m.as.app b).toNatTrans.app V := by
  have hmod := Cat.Hom₂.congr_app (m.as.naturality (Quiver.Hom.op V)) (𝟙 b₀)
  simp only [Cat.Hom.toNatTrans_comp, NatTrans.comp_app, Cat.whiskerLeft_toNatTrans,
    Cat.whiskerRight_toNatTrans, whiskerLeft_app, whiskerRight_app] at hmod
  have hnat : (X.app b).toFunctor.map (ρ_ V).hom ≫ (m.as.app b).toNatTrans.app V
      = (m.as.app b).toNatTrans.app (((yoneda₀ b₀).map (Quiver.Hom.op V)).toFunctor.obj (𝟙 b₀)) ≫
        (Y.app b).toFunctor.map (ρ_ V).hom :=
    (m.as.app b).toNatTrans.naturality (ρ_ V).hom
  have hXi := Cat.Hom.inv_hom_id_toNatTrans_app (X.naturality (Quiver.Hom.op V)) (𝟙 b₀)
  have hYh := Cat.Hom.hom_inv_id_toNatTrans_app (Y.naturality (Quiver.Hom.op V)) (𝟙 b₀)
  have hM : (G.map (Quiver.Hom.op V)).toFunctor.map ((m.as.app (op b₀)).toNatTrans.app (𝟙 b₀))
      = (X.naturality (Quiver.Hom.op V)).inv.toNatTrans.app (𝟙 b₀) ≫
        (m.as.app b).toNatTrans.app (((yoneda₀ b₀).map (Quiver.Hom.op V)).toFunctor.obj (𝟙 b₀)) ≫
        (Y.naturality (Quiver.Hom.op V)).hom.toNatTrans.app (𝟙 b₀) := by
    rw [hmod, ← Category.assoc, hXi, Category.id_comp]
  have hcancel : (Y.naturality (Quiver.Hom.op V)).hom.toNatTrans.app (𝟙 b₀) ≫
      (Y.naturality (Quiver.Hom.op V)).inv.toNatTrans.app (𝟙 b₀) ≫
        (Y.app b).toFunctor.map (ρ_ V).hom
      = (Y.app b).toFunctor.map (ρ_ V).hom := by
    rw [← Category.assoc, hYh, Category.id_comp]
  rw [hM]
  simp only [Category.assoc]
  rw [hcancel, ← hnat]

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
  intro X Y m
  apply homCategory.ext
  intro b
  apply Cat.Hom₂.ext_app
  intro V
  exact unit_natiso_core m b V


/-! ### The unit's modification square

`ModificationIntoCats.isoMk`'s obligation, at a point.  The four folded pieces of the goal --
the transported transformation's unit component, the identity transformation's naturality, the
composite record's naturality, and the pairing's action on the unit modification -- are all
definitionally the shapes below, so the descent needs no bridges: `exact` crosses it.

What the square says is that the unit is natural in the *pair* `(b₀, F)`.  The proof splits it
into three: `unit_top_lhs` and `unit_top_rhs` strip the outer transformation `β`, and
`unit_top_alpha` is what is left -- a statement about `α` alone, ending in the 2-cell identity
`(α_ ZZ (𝟙 _) g).inv ≫ (ρ_ ZZ).hom ▷ g = ZZ ◁ ((λ_ g).hom ≫ (ρ_ g).inv) ≫ (α_ ZZ g (𝟙 _)).inv
≫ (ρ_ (ZZ ≫ g)).hom`, which `bicategory` discharges.
-/

section UnitTop

variable {b₀ b₁ : B} {F G : Bᵒᵖ ⥤ᵖ Cat.{w, v}} (α : yoneda₀ b₀ ⟶ F) (β : F ⟶ G)
  (g : b₁ ⟶ b₀) {γ : Bᵒᵖ} (ZZ : unop γ ⟶ b₁)

set_option backward.isDefEq.respectTransparency false in
/-- Left-hand side of the unit's modification square, with `β` pulled out in front.

`postcomp₂ g ≫ α ≫ β` is a triple composite, so `strongTrans_comp_naturality_inv_app` applies
twice; `postcomp₂`'s own naturality is an associator, definitionally. -/
lemma unit_top_lhs :
    ((postcomp₂ g ≫ α ≫ β).naturality (Quiver.Hom.op ZZ)).inv.toNatTrans.app (𝟙 b₁) ≫
        ((postcomp₂ g ≫ α ≫ β).app γ).toFunctor.map (ρ_ ZZ).hom
      = (β.naturality (Quiver.Hom.op ZZ)).inv.toNatTrans.app
            ((α.app (op b₁)).toFunctor.obj (𝟙 b₁ ≫ g)) ≫
          (β.app γ).toFunctor.map
            ((α.naturality (Quiver.Hom.op ZZ)).inv.toNatTrans.app (𝟙 b₁ ≫ g) ≫
              (α.app γ).toFunctor.map ((α_ ZZ (𝟙 b₁) g).inv ≫ ((ρ_ ZZ).hom ▷ g))) := by
  rw [strongTrans_comp_naturality_inv_app (postcomp₂ g) (α ≫ β) (Quiver.Hom.op ZZ) (𝟙 b₁),
    strongTrans_comp_naturality_inv_app α β (Quiver.Hom.op ZZ)
      (((postcomp₂ g).app (op b₁)).toFunctor.obj (𝟙 b₁))]
  simp only [Category.assoc, Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Right-hand side of the same square, brought to the same shape.

`β`'s `naturality_comp` (in inverse form) exposes a `hom`/`inv` pair under `G.map ZZ.op`, and
once that cancels the remaining `β`-factor slides out in front by naturality. -/
lemma unit_top_rhs :
    ((G.map (Quiver.Hom.op ZZ)).toFunctor.map
          ((β.app (op b₁)).toFunctor.map
            ((α.app (op b₁)).toFunctor.map ((λ_ g).hom ≫ (ρ_ g).inv) ≫
              (α.naturality (Quiver.Hom.op g)).hom.toNatTrans.app (𝟙 b₀))) ≫
        ((G.map (Quiver.Hom.op ZZ)).toFunctor.map
            ((β.naturality (Quiver.Hom.op g)).hom.toNatTrans.app
              ((α.app (op b₀)).toFunctor.obj (𝟙 b₀))) ≫
          (G.mapComp (Quiver.Hom.op g) (Quiver.Hom.op ZZ)).inv.toNatTrans.app
            ((β.app (op b₀)).toFunctor.obj ((α.app (op b₀)).toFunctor.obj (𝟙 b₀))) ≫
          (β.naturality (Quiver.Hom.op g ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app
            ((α.app (op b₀)).toFunctor.obj (𝟙 b₀)))) ≫
      (β.app γ).toFunctor.map
        ((α.naturality (Quiver.Hom.op (ZZ ≫ g))).inv.toNatTrans.app (𝟙 b₀) ≫
          (α.app γ).toFunctor.map (ρ_ (ZZ ≫ g)).hom)
      = (β.naturality (Quiver.Hom.op ZZ)).inv.toNatTrans.app
            ((α.app (op b₁)).toFunctor.obj (𝟙 b₁ ≫ g)) ≫
          (β.app γ).toFunctor.map
            ((F.map (Quiver.Hom.op ZZ)).toFunctor.map
                ((α.app (op b₁)).toFunctor.map ((λ_ g).hom ≫ (ρ_ g).inv) ≫
                  (α.naturality (Quiver.Hom.op g)).hom.toNatTrans.app (𝟙 b₀)) ≫
              (F.mapComp (Quiver.Hom.op g) (Quiver.Hom.op ZZ)).inv.toNatTrans.app
                ((α.app (op b₀)).toFunctor.obj (𝟙 b₀)) ≫
              ((α.naturality (Quiver.Hom.op (ZZ ≫ g))).inv.toNatTrans.app (𝟙 b₀) ≫
                (α.app γ).toFunctor.map (ρ_ (ZZ ≫ g)).hom)) := by
  simp only [Category.assoc]
  rw [strongTrans_naturality_comp_inv_app_assoc β (Quiver.Hom.op g) (Quiver.Hom.op ZZ)
    ((α.app (op b₀)).toFunctor.obj (𝟙 b₀))]
  rw [map_comp_cancel_assoc (G.map (Quiver.Hom.op ZZ)).toFunctor _ _
    (Cat.Hom.hom_inv_id_toNatTrans_app (β.naturality (Quiver.Hom.op g))
      ((α.app (op b₀)).toFunctor.obj (𝟙 b₀)))]
  have hslide : (G.map (Quiver.Hom.op ZZ)).toFunctor.map
        ((β.app (op b₁)).toFunctor.map
          ((α.app (op b₁)).toFunctor.map ((λ_ g).hom ≫ (ρ_ g).inv) ≫
            (α.naturality (Quiver.Hom.op g)).hom.toNatTrans.app (𝟙 b₀))) ≫
      (β.naturality (Quiver.Hom.op ZZ)).inv.toNatTrans.app
        ((F.map (Quiver.Hom.op g)).toFunctor.obj ((α.app (op b₀)).toFunctor.obj (𝟙 b₀)))
      = (β.naturality (Quiver.Hom.op ZZ)).inv.toNatTrans.app
            ((α.app (op b₁)).toFunctor.obj (𝟙 b₁ ≫ g)) ≫
          (β.app γ).toFunctor.map
            ((F.map (Quiver.Hom.op ZZ)).toFunctor.map
              ((α.app (op b₁)).toFunctor.map ((λ_ g).hom ≫ (ρ_ g).inv) ≫
                (α.naturality (Quiver.Hom.op g)).hom.toNatTrans.app (𝟙 b₀))) :=
    (β.naturality (Quiver.Hom.op ZZ)).inv.toNatTrans.naturality _
  rw [reassoc_of% hslide]
  simp only [Functor.map_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- What the square reduces to once `β` is stripped: a statement about `α` alone.

Same three moves as `unit_obj_core`, in the other order -- `α`'s `naturality_comp`, the
cancellation it exposes, and one naturality square of `(α.naturality ZZ.op).inv` -- ending in a
pure 2-cell identity in `B`. -/
lemma unit_top_alpha :
    (α.naturality (Quiver.Hom.op ZZ)).inv.toNatTrans.app (𝟙 b₁ ≫ g) ≫
        (α.app γ).toFunctor.map ((α_ ZZ (𝟙 b₁) g).inv ≫ ((ρ_ ZZ).hom ▷ g))
      = (F.map (Quiver.Hom.op ZZ)).toFunctor.map
            ((α.app (op b₁)).toFunctor.map ((λ_ g).hom ≫ (ρ_ g).inv) ≫
              (α.naturality (Quiver.Hom.op g)).hom.toNatTrans.app (𝟙 b₀)) ≫
          (F.mapComp (Quiver.Hom.op g) (Quiver.Hom.op ZZ)).inv.toNatTrans.app
            ((α.app (op b₀)).toFunctor.obj (𝟙 b₀)) ≫
          ((α.naturality (Quiver.Hom.op g ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app (𝟙 b₀) ≫
            (α.app γ).toFunctor.map (ρ_ (ZZ ≫ g)).hom) := by
  simp only [Category.assoc, Functor.map_comp]
  rw [strongTrans_naturality_comp_inv_app_assoc α (Quiver.Hom.op g) (Quiver.Hom.op ZZ) (𝟙 b₀)]
  rw [map_comp_cancel_assoc (F.map (Quiver.Hom.op ZZ)).toFunctor _ _
    (Cat.Hom.hom_inv_id_toNatTrans_app (α.naturality (Quiver.Hom.op g)) (𝟙 b₀))]
  rw [map_map_comp_assoc (α.app (op b₁)).toFunctor (F.map (Quiver.Hom.op ZZ)).toFunctor]
  have hsl : (F.map (Quiver.Hom.op ZZ)).toFunctor.map
        ((α.app (op b₁)).toFunctor.map ((λ_ g).hom ≫ (ρ_ g).inv)) ≫
      (α.naturality (Quiver.Hom.op ZZ)).inv.toNatTrans.app
        (((yoneda₀ b₀).map (Quiver.Hom.op g)).toFunctor.obj (𝟙 b₀))
      = (α.naturality (Quiver.Hom.op ZZ)).inv.toNatTrans.app (𝟙 b₁ ≫ g) ≫
        (α.app γ).toFunctor.map (ZZ ◁ ((λ_ g).hom ≫ (ρ_ g).inv)) :=
    (α.naturality (Quiver.Hom.op ZZ)).inv.toNatTrans.naturality _
  rw [reassoc_of% hsl]
  refine congrArg (fun t =>
    (α.naturality (Quiver.Hom.op ZZ)).inv.toNatTrans.app (𝟙 b₁ ≫ g) ≫ t) ?_
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  refine congrArg (α.app γ).toFunctor.map ?_
  exact (by bicategory : (α_ ZZ (𝟙 b₁) g).inv ≫ ((ρ_ ZZ).hom ▷ g)
    = ZZ ◁ ((λ_ g).hom ≫ (ρ_ g).inv) ≫ (α_ ZZ g (𝟙 b₀)).inv ≫ (ρ_ (ZZ ≫ g)).hom)

/-- The unit's modification square, at a point, in clean unbundled variables. -/
lemma unit_top_core :
    ((postcomp₂ g ≫ α ≫ β).naturality (Quiver.Hom.op ZZ)).inv.toNatTrans.app (𝟙 b₁) ≫
        ((postcomp₂ g ≫ α ≫ β).app γ).toFunctor.map (ρ_ ZZ).hom
      = ((G.map (Quiver.Hom.op ZZ)).toFunctor.map
            ((β.app (op b₁)).toFunctor.map
              ((α.app (op b₁)).toFunctor.map ((λ_ g).hom ≫ (ρ_ g).inv) ≫
                (α.naturality (Quiver.Hom.op g)).hom.toNatTrans.app (𝟙 b₀))) ≫
          ((G.map (Quiver.Hom.op ZZ)).toFunctor.map
              ((β.naturality (Quiver.Hom.op g)).hom.toNatTrans.app
                ((α.app (op b₀)).toFunctor.obj (𝟙 b₀))) ≫
            (G.mapComp (Quiver.Hom.op g) (Quiver.Hom.op ZZ)).inv.toNatTrans.app
              ((β.app (op b₀)).toFunctor.obj ((α.app (op b₀)).toFunctor.obj (𝟙 b₀))) ≫
            (β.naturality (Quiver.Hom.op g ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app
              ((α.app (op b₀)).toFunctor.obj (𝟙 b₀)))) ≫
        (β.app γ).toFunctor.map
          ((α.naturality (Quiver.Hom.op (ZZ ≫ g))).inv.toNatTrans.app (𝟙 b₀) ≫
            (α.app γ).toFunctor.map (ρ_ (ZZ ≫ g)).hom) :=
  (unit_top_lhs α β g ZZ).trans
    ((congrArg (fun t => (β.naturality (Quiver.Hom.op ZZ)).inv.toNatTrans.app
        ((α.app (op b₁)).toFunctor.obj (𝟙 b₁ ≫ g)) ≫ (β.app γ).toFunctor.map t)
      (unit_top_alpha α g ZZ)).trans (unit_top_rhs α β g ZZ).symm)

end UnitTop

/-- The unit, built in the `StrongTransIntoCats` world.

This is the whole mathematical content of `yonedaHomInvId`, and it is stated where the
obligation is tractable: `ModificationIntoCats.isoMk` takes the natural isomorphisms we already
have, one per object, and asks for the modification square **at a point** -- no `Cat` 2-cells,
no associators, and only the forward direction (the inverse comes for free). -/
def yonedaHomInvIdIso :
    (yonedaLemmaForwardsData.comp yonedaLemmaBackwardsData) ≅
      (StrongTransIntoCats.Id (F := @yonedaPairing B _)) :=
  ModificationIntoCats.isoMk (fun a ↦ yonedaHomInvIdNatIso a) (fun {a b} f x ↦ by
    apply homCategory.ext
    intro γ
    apply Cat.Hom₂.ext_app
    intro ZZ
    change _ ≫ _ = _ ≫ _
    exact Eq.trans (Category.comp_id _) (unit_top_core x f.2 f.1.unop ZZ))

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
  simp only [Cat.Hom.toNatTrans_comp, NatTrans.comp_app,
    Cat.whiskerRight_toNatTrans, whiskerRight_app]
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


/-! ### The counit's naturality square

The counit is the other half of the equivalence, and unlike the unit it is *not* routed through
`ModificationIntoCats`: `yonedaLemmaBackwards ≫ yonedaLemmaForwards` is `liftDom d ≫ lift d'`,
and the `StrongTransIntoCats` bridge that exists (`lift_comp_liftDom_naturality_app`) is for the
other order.  So the square is descended by hand, with five `rfl` bridges naming the folded
pieces, and the content is `counit_core`.

Every bridge is stated at an **unlifted** point `⟨s⟩`: writing the universe-lift as the
anonymous constructor rather than as `catLiftUnit` keeps the lift's universe parameters pinned
by the goal instead of leaving one of them undetermined.
-/

section CounitCore

variable {F G : Bᵒᵖ ⥤ᵖ Cat.{w, v}} (β : F ⟶ G) {x y : Bᵒᵖ} (u : x ⟶ y) (s : ↑(F.obj x))

set_option backward.isDefEq.respectTransparency false in
/-- The content of the counit's naturality square, in clean unbundled variables.

Three moves.  `β`'s `naturality_comp` for `u` and `𝟙 y`, in inverse form, exposes a `hom`/`inv`
pair under `G.map (𝟙 y)`; `β`'s `naturality_id` turns the surviving factor into `G.mapId`; and
what is left is a coherence of `F` alone: Mathlib's `whiskerRight_mapId_hom_app` cancels the left
`mapComp` against `mapId`, `simp` reduces the right one against the unitor, and the two unitor
2-cells cancel. -/
lemma counit_core :
    (G.mapId y).hom.toNatTrans.app ((β.app y).toFunctor.obj ((F.map u).toFunctor.obj s))
      = (((G.map (𝟙 y)).toFunctor.map ((β.naturality u).hom.toNatTrans.app s) ≫
            (G.mapComp u (𝟙 y)).inv.toNatTrans.app ((β.app x).toFunctor.obj s) ≫
            (β.naturality (u ≫ 𝟙 y)).inv.toNatTrans.app s) ≫
          (β.app y).toFunctor.map
            ((F.map₂ ((ρ_ u).hom ≫ (λ_ u).inv)).toNatTrans.app s ≫
              (F.mapComp (𝟙 x) u).hom.toNatTrans.app s)) ≫
        (β.app y).toFunctor.map ((F.map u).toFunctor.map ((F.mapId x).hom.toNatTrans.app s)) := by
  have h1 : (G.map (𝟙 y)).toFunctor.map ((β.naturality u).hom.toNatTrans.app s) ≫
        (G.mapComp u (𝟙 y)).inv.toNatTrans.app ((β.app x).toFunctor.obj s) ≫
        (β.naturality (u ≫ 𝟙 y)).inv.toNatTrans.app s
      = (β.naturality (𝟙 y)).inv.toNatTrans.app ((F.map u).toFunctor.obj s) ≫
        (β.app y).toFunctor.map ((F.mapComp u (𝟙 y)).inv.toNatTrans.app s) := by
    rw [strongTrans_naturality_comp_inv_app β u (𝟙 y) s,
      map_comp_cancel_assoc (G.map (𝟙 y)).toFunctor _ _
        (Cat.Hom.hom_inv_id_toNatTrans_app (β.naturality u) s)]
  have h2 : (G.mapId y).hom.toNatTrans.app ((β.app y).toFunctor.obj ((F.map u).toFunctor.obj s))
      = (β.naturality (𝟙 y)).inv.toNatTrans.app ((F.map u).toFunctor.obj s) ≫
        (β.app y).toFunctor.map
          ((F.mapId y).hom.toNatTrans.app ((F.map u).toFunctor.obj s)) := by
    rw [← Pseudofunctor.StrongTrans.naturality_id_app β y ((F.map u).toFunctor.obj s),
      ← Category.assoc,
      Cat.Hom.inv_hom_id_toNatTrans_app, Category.id_comp]
  rw [h1, h2]
  simp only [Category.assoc]
  refine congrArg (fun t => (β.naturality (𝟙 y)).inv.toNatTrans.app
    ((F.map u).toFunctor.obj s) ≫ t) ?_
  rw [← Functor.map_comp, ← Functor.map_comp]
  refine congrArg (β.app y).toFunctor.map ?_
  simp only [Category.assoc]
  rw [Pseudofunctor.whiskerRight_mapId_hom_app, Cat.Hom.hom_inv_id_toNatTrans_app_assoc]
  have hm := Cat.Hom₂.congr_app
    (show (F.map₂ ((ρ_ u).hom ≫ (λ_ u).inv)) ≫ (F.map₂ (λ_ u).hom) = F.map₂ (ρ_ u).hom by
      rw [← PrelaxFunctor.map₂_comp]; congr 1; simp) s
  simp only [Cat.Hom.toNatTrans_comp, NatTrans.comp_app] at hm
  rw [hm]
  have hr : (F.mapComp u (𝟙 y)).hom.toNatTrans.app s ≫
      (F.mapId y).hom.toNatTrans.app ((F.map u).toFunctor.obj s)
      = (F.map₂ (ρ_ u).hom).toNatTrans.app s := by
    simp
  rw [← hr, ← Category.assoc, Cat.Hom.inv_hom_id_toNatTrans_app]
  exact (Category.id_comp _).symm

end CounitCore

section CounitBridges

variable {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b) (s : ↑(yonedaEvaluation'.obj a))

/-- The left-hand side of the counit square at a point: the counit component of the transported
element.  A `rfl` bridge. -/
lemma counit_square_lhs_app :
    (yonedaEvaluation.map f ◁ (Cat.Hom.isoMk (yonedaInvHomIdNatIso b)).hom).toNatTrans.app
        (⟨s⟩ : ↑(yonedaEvaluation.obj a))
      = ⟨(b.2.mapId b.1).hom.toNatTrans.app
          ((f.2.app b.1).toFunctor.obj ((a.2.map f.1).toFunctor.obj s))⟩ := rfl

lemma counit_id_naturality_app :
    ((show (@yonedaEvaluation B _) ⟶ yonedaEvaluation from
      𝟙 yonedaEvaluation).naturality f).hom.toNatTrans.app (⟨s⟩ : ↑(yonedaEvaluation.obj a))
      = 𝟙 _ ≫ 𝟙 _ := rfl

lemma counit_square_rhs_app :
    ((Cat.Hom.isoMk (yonedaInvHomIdNatIso a)).hom ▷ yonedaEvaluation.map f).toNatTrans.app
        (⟨s⟩ : ↑(yonedaEvaluation.obj a))
      = ⟨(f.2.app b.1).toFunctor.map
          ((a.2.map f.1).toFunctor.map ((a.2.mapId a.1).hom.toNatTrans.app s))⟩ := rfl

lemma counit_backwards_app :
    (yonedaLemmaForwards.app b).toFunctor.map
        ((yonedaLemmaBackwards.naturality f).hom.toNatTrans.app
          (⟨s⟩ : ↑(yonedaEvaluation.obj a)))
      = ⟨((backwardsNaturalityIso f s).hom.as.app b.1).toNatTrans.app (𝟙 (unop b.1))⟩ := rfl

lemma counit_forwards_app :
    (yonedaLemmaForwards.naturality f).hom.toNatTrans.app
        ((yonedaLemmaBackwards.app a).toFunctor.obj (⟨s⟩ : ↑(yonedaEvaluation.obj a)))
      = ⟨(f.2.app b.1).toFunctor.map
          ((a.2.map₂ (op2 ((λ_ f.1.unop).hom ≫ (ρ_ f.1.unop).inv))).toNatTrans.app s ≫
            (a.2.mapComp (Quiver.Hom.op (𝟙 (unop a.1))) f.1).hom.toNatTrans.app s) ≫ 𝟙 _⟩ := rfl

end CounitBridges

set_option backward.isDefEq.respectTransparency false in
/--
The *counit isomorphism* `yonedaLemmaBackwards ≫ yonedaLemmaForwards ≅ 𝟙 yonedaEvaluation`.

This witnesses that composing the Yoneda embedding with "evaluate at identity" returns the
original element of `F.obj b`, up to a canonical isomorphism.  It is the `invHomId` field
of `yonedaLemma`.
-/
def yonedaInvHomId : yonedaLemmaBackwards ≫ yonedaLemmaForwards ≅ 𝟙 (@yonedaEvaluation B _) := by
  refine StrongTrans.isoMk (fun a ↦ Cat.Hom.isoMk (yonedaInvHomIdNatIso a)) ?_
  intro a b f
  apply Cat.Hom₂.ext_app
  rintro ⟨s⟩
  -- Split the composite's naturality, then let the five bridges name every folded piece.
  change _ ≫ _ = _ ≫ _
  rw [strongTrans_comp_naturality_app yonedaLemmaBackwards yonedaLemmaForwards f ⟨s⟩,
    counit_square_lhs_app f s, counit_id_naturality_app f s, counit_backwards_app f s,
    counit_forwards_app f s, counit_square_rhs_app f s]
  simp only [Category.comp_id]
  rw [counit_core f.2 f.1]
  exact rfl

end Biyoneda
