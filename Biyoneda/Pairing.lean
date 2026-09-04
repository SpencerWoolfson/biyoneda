/-
Copyright (c) 2026 Spencer Woolfson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Spencer Woolfson
-/
import Mathlib.CategoryTheory.Bicategory.Product
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Bicategory.Yoneda
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.Tactic.CategoryTheory.Bicategory.Basic
import Mathlib.Tactic.CategoryTheory.Slice
import Biyoneda.Evaluation
import Biyoneda.UniverseLift
import Biyoneda.BiEquiv
import Biyoneda.Gadgets
import Biyoneda.TransIntoCats

/-!
# The Yoneda pairing and evaluation pseudofunctors

The two sides of the bicategorical Yoneda lemma, and the bridge lemmas that let the
composite-built `yonedaPairing` be used in its hand-rolled spelling.

* `yonedaPairing` — `(b, F) ↦ StrongTrans (yoneda₀ b) F`, defined as `yonedaPairingComposite`
  so that its coherence laws are inherited from `Biyoneda.Gadgets` rather than proved by hand.
* `yonedaEvaluation'` — `(b, F) ↦ F.obj b`, in the small universe.
* `yonedaEvaluation` — the same, lifted to match `yonedaPairing`'s universe.

## Universe notes

`yonedaEvaluation'` lands in `Cat.{w, v}` while `yonedaPairing` lands in
`Cat.{max u (max v w), max u (max v w)}`.  `catPseudoULift` promotes the former to the
latter, yielding `yonedaEvaluation`.
-/

namespace Biyoneda

open CategoryTheory Bicategory Bicategory.Opposite Opposite Pseudofunctor StrongTrans Functor
open scoped Pseudofunctor.StrongTrans

universe u v w v₁ v₂ u₁ u₂

attribute [local instance] uliftCategory


variable {B : Type u} [Bicategory.{w, v} B]

universe w₁

/-- `postcomp₂` at an identity 1-morphism is isomorphic to the identity strong transformation.
This is `Bicategory.yoneda.mapId` restated for `postcomp₂`. -/
def postcompId₂ (a : B) : postcomp₂ (𝟙 a) ≅ 𝟙 (yoneda₀ a) := Bicategory.yoneda.mapId a

/-- `postcomp₂` is functorial in the 1-morphism, up to isomorphism: `postcomp₂ (f ≫ g)` is
isomorphic to `postcomp₂ f ≫ postcomp₂ g`.  This is `Bicategory.yoneda.mapComp` restated. -/
def postcompComp₂ {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    postcomp₂ (f ≫ g) ≅ postcomp₂ f ≫ postcomp₂ g := Bicategory.yoneda.mapComp f g

/--
The functor underlying `yonedaPairing.map f`, expressed as the composite of the
"postcompose with `f.2`" functor and the "precompose with `postcomp₂ f.1.unop`" functor
on hom-categories of the pseudofunctor bicategory.

Its action agrees definitionally with the functor used in `yonedaPairing.map`
(`η ↦ postcomp₂ f.1.unop ≫ η ≫ f.2`); phrasing it as a composite of the `precomposing` and
`postcomposing` functors makes functoriality and naturality properties available for free.
-/
def yonedaPairingMapFunctor {x y : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : x ⟶ y) :
    (yoneda₀ (unop x.1) ⟶ x.2) ⥤ (yoneda₀ (unop y.1) ⟶ y.2) :=
  (postcomposing (yoneda₀ (unop x.1)) x.2 y.2).obj f.2 ⋙
    (precomposing (yoneda₀ (unop y.1)) (yoneda₀ (unop x.1)) y.2).obj (postcomp₂ f.1.unop)

/--
The natural transformation underlying `yonedaPairing.map₂ η`, built by whiskering the
images of `η.1` and `η.2` under `precomposing`/`postcomposing`.  Because it is assembled
from whiskerings of natural transformations, naturality is automatic, and its components
agree definitionally with `(h1 ▷ (a ≫ f.2)) ≫ postcomp₂ g.1.unop ◁ (a ◁ h2)` as used in
`yonedaPairing.map₂`.
-/
def yonedaPairingMap₂ {x y : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} {f g : x ⟶ y} (η : f ⟶ g) :
    yonedaPairingMapFunctor f ⟶ yonedaPairingMapFunctor g :=
  Functor.whiskerLeft ((postcomposing (yoneda₀ (unop x.1)) x.2 y.2).obj f.2)
      ((precomposing (yoneda₀ (unop y.1)) (yoneda₀ (unop x.1)) y.2).map
        ((postcomposing₂ (unop y.1) (unop x.1)).map η.1.unop2)) ≫
    Functor.whiskerRight ((postcomposing (yoneda₀ (unop x.1)) x.2 y.2).map η.2)
      ((precomposing (yoneda₀ (unop y.1)) (yoneda₀ (unop x.1)) y.2).obj (postcomp₂ g.1.unop))

/-- `yonedaPairingMap₂ η` is the horizontal composition of the whiskering transformations
induced by `η.2` and `η.1`. -/
lemma yonedaPairingMap₂_hcomp {x y : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} {f g : x ⟶ y} (η : f ⟶ g) :
    yonedaPairingMap₂ η =
      ((postcomposing (yoneda₀ (unop x.1)) x.2 y.2).map η.2) ◫
        ((precomposing (yoneda₀ (unop y.1)) (yoneda₀ (unop x.1)) y.2).map
          ((postcomposing₂ (unop y.1) (unop x.1)).map η.1.unop2)) :=
  (NatTrans.hcomp_eq_whiskerLeft_comp_whiskerRight _ _).symm

/--
The *pairing pseudofunctor* `Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat) ⥤ᵖ Cat`.

This is the left-hand side of the Yoneda equivalence, encoding "strong transformations out of
the Yoneda embedding":

* **On objects**: `(b, F) ↦ StrongTrans (yoneda₀ b) F` — the category whose objects are strong
  transformations `yoneda₀ b ⟶ F` and whose morphisms are modifications between them.
* **On 1-morphisms**: a pair `(f : b' ⟶ b, α : F ⟶ G)` acts on a strong transformation `η`
  by `η ↦ postcomp₂ f ≫ η ≫ α` — precomposing with the Yoneda image of `f` and
  postcomposing with `α`.
* **On 2-morphisms**: a pair `(σ : f ⟶ f', τ : α ⟶ β)` acts by left- and right-whiskering
  the corresponding postcomposing transformations.
-/
def yonedaPairing : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v}) ⥤ᵖ Cat.{max u (max v w), max u (max v w)} :=
  yonedaPairingComposite


/-! ### Bridge lemmas: the composite's projections in hand-rolled spelling

`yonedaPairing` is the gadget composite, but `.obj`, `.map` and `.map₂` agree with the
hand-rolled construction *definitionally*. These `rfl` lemmas let `simp only` reconcile the
two spellings, which is what keeps the proofs below matching. (`.mapId`/`.mapComp` do NOT
bridge — the composite's are genuinely different terms — so no such lemma exists for them.)
-/

@[simp] lemma yonedaPairing_map₂ {x y : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} {f g : x ⟶ y} (η : f ⟶ g) :
    (yonedaPairing (B := B)).map₂ η = NatTrans.toCatHom₂ (yonedaPairingMap₂ η) := rfl

lemma yonedaPairing_map' {x y : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : x ⟶ y) :
    (yonedaPairing (B := B)).map f = Functor.toCatHom (yonedaPairingMapFunctor f) := rfl

/--
The *evaluation pseudofunctor* `Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat) ⥤ᵖ Cat`, sending `(b, F)` to `F.obj b`.

This is the general `evaluationPseudo` of `Biyoneda.Evaluation` instantiated at `C := Bᵒᵖ`;
nothing about it is Yoneda-specific.  It is the right-hand side of the Yoneda equivalence,
before the universe lift to `yonedaEvaluation`.
-/
def yonedaEvaluation' : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v}) ⥤ᵖ Cat.{w, v} :=
  evaluationPseudo (C := Bᵒᵖ)

/--
The *evaluation pseudofunctor* at the correct universe level,
`Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat) ⥤ᵖ Cat.{max u (max v w), max u (max v w)}`.

Defined as the composite `yonedaEvaluation' ⋙ catPseudoULift`, which promotes the smaller
pseudofunctor `yonedaEvaluation'` (landing in `Cat.{w, v}`) to match the universe of
`yonedaPairing`.
-/
def yonedaEvaluation : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v}) ⥤ᵖ Cat.{max u (max v w), max u (max v w)} :=
  Pseudofunctor.comp yonedaEvaluation' catPseudoULift

/-- Reduction: the 2-morphism image of the lifted evaluation pseudofunctor at a lifted point is
the unlifted `yonedaEvaluation'.map₂` component. -/
lemma yonedaEvaluation_map₂_app_down {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} {f g : a ⟶ b}
    (η : f ⟶ g) (x : ↑(yonedaEvaluation'.obj a)) :
    (yonedaEvaluation.map₂ η).toNatTrans.app { down := x }
      = { down := (yonedaEvaluation'.map₂ η).toNatTrans.app x } := by
  dsimp [yonedaEvaluation, Pseudofunctor.comp, catPseudoULift, catLift, ULiftHom.up]
  rfl

/-! ### The pairing's unit and composition constraints, at a point

`yonedaPairing` is a composite, so its `mapId`/`mapComp` are chains of structural 2-cells in
`Bᵒᵖ ⥤ᵖ Cat` -- and unlike `.obj`/`.map`/`.map₂` they do **not** bridge to the hand-rolled
spelling by `rfl`.  Descending such a chain with the `*_as_app` lemmas alone does not work: the
goals are not type-correct at `implicit` transparency (see the note in `Biyoneda/Forwards.lean`),
and `(𝟙 F).app α` versus `𝟙 (F.obj α)` is a `CategoryStruct` diamond that no simp lemma bridges.

What does work is to descend to a point first and *then* distribute.  The unit lemma takes the
padding trick -- name the chain's value with its structural identities written in, and let
`simp` cancel them.  The composition lemma is longer but no harder once the chain is split by
`change _ ≫ _ ≫ _ ≫ _ ≫ _ ≫ _ = _`, an all-holes `change` that reveals the six factors instead
of asking you to guess them.

Both are needed on *both* sides of the equivalence -- `Forwards.lean` and `Backwards.lean` are
siblings -- which is why they live here rather than next to either use site.
-/

set_option backward.isDefEq.respectTransparency false in
/-- The pairing's unit constraint, evaluated on a strong transformation and then at a point:
just the right unitor, transported by that transformation. -/
lemma yonedaPairing_mapId_app (a : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})) (Z : ↑(yonedaPairing.obj a))
    (γ : Bᵒᵖ) (ZZ : ↑((yoneda₀ (unop a.1)).obj γ)) :
    (((yonedaPairing.mapId a).hom.toNatTrans.app Z).as.app γ).toNatTrans.app ZZ
      = (Z.app γ).toFunctor.map (ρ_ ZZ).hom := by
  dsimp only [yonedaPairing, yonedaPairingComposite, Pseudofunctor.comp, homPseudo,
    homMapId, homMapIdApp, Pseudofunctor.prod, Pseudofunctor.op]
  simp only [prelax_map₂_app, Iso.trans_hom, Cat.Hom.isoMk_hom, NatIso.ofComponents_hom_app,
    Cat.toCatHom₂_toNatTrans, Cat.Hom.toNatTrans_comp, NatTrans.comp_app,
    PrelaxFunctor.map₂Iso_hom, Category.assoc]
  -- the chain has four factors; three of them are identities at a point
  change (Z.app γ).toFunctor.map (ρ_ ZZ).hom ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ = _
  simp

-- `linter.flexible`: the final `simp` is followed by a `Category.comp_id` supplied as a named
-- term, so drift fails loudly rather than silently.
set_option linter.flexible false in
set_option backward.isDefEq.respectTransparency false in
/-- The pairing's composition constraint, evaluated on a strong transformation and then at a
point: just the associator, transported by that transformation and then by the two component
functors.  This is the one place where the composite's `mapComp` had to be computed rather than
re-spelled, and it is what both `forwards_naturality_comp_core` and
`yonedaLemmaBackwardsData.naturality_comp'` reduce to. -/
lemma yonedaPairing_mapComp_app {a b c : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b) (g : b ⟶ c)
    (Z : ↑(yonedaPairing.obj a)) (γ : Bᵒᵖ) (ZZ : ↑((yoneda₀ (unop c.1)).obj γ)) :
    (((yonedaPairing.mapComp f g).hom.toNatTrans.app Z).as.app γ).toNatTrans.app ZZ
      = (g.2.app γ).toFunctor.map
          ((f.2.app γ).toFunctor.map
            ((Z.app γ).toFunctor.map (α_ ZZ g.1.unop f.1.unop).inv)) := by
  dsimp only [yonedaPairing, yonedaPairingComposite, Pseudofunctor.comp, homPseudo,
    homMapComp, homMapCompApp, Pseudofunctor.prod, Pseudofunctor.op]
  simp only [prelax_map₂_app, Iso.trans_hom, Cat.Hom.isoMk_hom, NatIso.ofComponents_hom_app,
    Cat.toCatHom₂_toNatTrans, Cat.Hom.toNatTrans_comp, NatTrans.comp_app,
    PrelaxFunctor.map₂Iso_hom, Category.assoc]
  -- all-holes `change`: split the chain into its six factors without guessing what they are
  change _ ≫ _ ≫ _ ≫ _ ≫ _ ≫ _ = _
  dsimp only [Pseudofunctor.StrongTrans.comp_app]
  simp only [whiskerLeftIso_hom, whiskerRightIso_hom, Iso.symm_hom,
    whiskerLeft_as_app, whiskerRight_as_app, associator_hom_as_app, associator_inv_as_app]
  simp only [Cat.whiskerRight_app, Cat.whiskerLeft_app, Cat.associator_hom_app,
    Cat.associator_inv_app, Cat.Hom.comp_toFunctor, Functor.comp_obj]
  simp
  -- `(Pseudofunctor.id _).map (f.2 ≫ g.2)` does not reduce at reducible transparency, so the
  -- last step is an `exact` rather than another `simp`
  exact Category.comp_id _

end Biyoneda
