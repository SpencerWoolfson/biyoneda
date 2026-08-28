/-
Copyright (c) 2026 Spencer Woolfson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Spencer Woolfson
-/
import Biyoneda.EvaluationAssociator

/-!
# The evaluation pseudofunctor

For a bicategory `C`, this file constructs the **evaluation pseudofunctor**

  `evaluationPseudo : C × (C ⥤ᵖ Cat) ⥤ᵖ Cat`,   `(c, F) ↦ F.obj c`,

the bicategorical analogue of Mathlib's `CategoryTheory.evaluationUncurried`, which is currently
missing from the `Bicategory` library.  Nothing here is specific to the Yoneda lemma: `C` is an
arbitrary bicategory.  The bicategorical Yoneda development uses the instance `C := Bᵒᵖ`.

## Implementation notes

### Which diagonal

The action on 1-morphisms fills a square in one of two ways.  This file uses **Mathlib's**
choice, matching `evaluationUncurried`:

```
map f = x.2.map f.1 ≫ f.2.app y.1
```

The other diagonal, `f.2.app x.1 ≫ y.2.map f.1`, is what this file used before 2026-08-28.  The
two are isomorphic but not equal: for a strong transformation `f.2` they are related by
`f.2.naturality f.1`, which is an iso and not an identity.  They agree in a 1-category, where
naturality is an equation, which is why Mathlib's choice looks arbitrary there and is not here.

The switch was made for alignment with Mathlib and for eventual upstreaming.  It is **not** a
simplification: the coherence budget is symmetric.  Measured on `mapComp`, both diagonals need
exactly one `mapComp` of a component pseudofunctor and one strong-transformation `naturality`
slide.  The only asymmetries found are cosmetic and are recorded at the two component lemmas at
the end of this file.

### Why the target is `Cat` and not a general `D`

The target bicategory is fixed to `Cat` rather than an arbitrary bicategory `D`.  This is not
incidental: the `mapId` field is `x.2.mapId x.1`, which typechecks only because `Cat` is a
`Bicategory.Strict` and so a unitor reduces definitionally.  Over a general `D` the field needs
an explicit unitor, which changes the term and is a separate (non-definitional) construction.

Note the diagonal switch moves which unitor is being leaned on.  The old diagonal needed
`𝟙 ≫ f`; this one needs `f ≫ 𝟙`.  See the comment at `mapId`.
-/

namespace CategoryTheory.Bicategory

open CategoryTheory Bicategory Pseudofunctor StrongTrans Functor
open scoped Pseudofunctor.StrongTrans

universe u v w

variable {C : Type u} [Bicategory.{w, v} C]


/--
The *evaluation pseudofunctor* `C × (C ⥤ᵖ Cat) ⥤ᵖ Cat.{w, v}`.

This is the right-hand side of the Yoneda equivalence (before universe promotion):

* **On objects**: `(b, F) ↦ F.obj b` — evaluate the pseudofunctor `F` at the object `b`.
* **On 1-morphisms**: `(f : b' ⟶ b, α : F ⟶ G) ↦ F.map f ≫ α.app b`, i.e., map along `f` using
  `F`, then apply the component of `α` at `b`.  This is Mathlib's diagonal; see the module
  docstring.
* **On 2-morphisms**: `(σ, τ) ↦ (F.map₂ σ ▷ α.app b) ≫ (F.map g ◁ τ.as.app b)`.
* **Coherence iso `mapId`**: `F.mapId b`, the identity coherence of `F`.
* **Coherence iso `mapComp`**: built from the associator, `F.mapComp`, and `α.naturality`.

Note: this pseudofunctor lands in the smaller universe `Cat.{w, v}`.  Use `yonedaEvaluation`
(which post-composes with `catPseudoULift`) for the universe-matched version.
-/
def evaluationPseudo : C × (C ⥤ᵖ Cat.{w, v}) ⥤ᵖ Cat.{w, v} where
  obj x := x.snd.obj x.fst
  map {x y} f := x.2.map f.1 ≫ f.2.app y.1
  map₂ {x y f g} η := (x.2.map₂ η.1 ▷ f.2.app y.1) ≫ (x.2.map g.1 ◁ η.2.as.app y.1)
  -- The other filling of the square, `(x.2.map f.1 ◁ η.2.as.app y.1) ≫ (x.2.map₂ η.1 ▷ …)`, is
  -- equal by `whisker_exchange`, so the choice is free.  Picked to keep the `map₂` factor
  -- leftmost, mirroring the pre-2026-08-28 field.
  mapId x := x.2.mapId x.1
  -- Typechecks only if `map (𝟙 x) = x.2.map (𝟙 x.1) ≫ 𝟙` reduces definitionally, i.e. if
  -- `f ≫ 𝟙` is defeq to `f` in `Cat`.  The previous diagonal needed `𝟙 ≫ f` here instead, and
  -- that one was known to reduce (notes/level2_refactor.md, Finding 3).  The right-hand case is
  -- the first thing this file establishes at build time.  If it fails, insert an explicit
  -- `ρ_` — but note that the result is then no longer `rfl`-equal to the bare form, which is the
  -- same trap Finding 3 documents for the target-generalisation attempt.
  mapComp {a b c} f g := by
    -- goal:  a.2.map (f.1 ≫ g.1) ≫ (f.2.app c.1 ≫ g.2.app c.1)
    --          ≅ (a.2.map f.1 ≫ f.2.app b.1) ≫ (b.2.map g.1 ≫ g.2.app c.1)
    --
    -- One `mapComp` and one `naturality`, the same budget as the other diagonal.  Note the
    -- orientation: this needs `f.2.naturality g.1` in the *hom* direction, where the previous
    -- diagonal needed `(g.2.naturality f.1).symm`.
    refine (a.2.mapComp f.1 g.1) ▷ᵢ (f.2.app c.1 ≫ g.2.app c.1) ≪≫ ?_
    refine (α_ (a.2.map f.1) (a.2.map g.1) (f.2.app c.1 ≫ g.2.app c.1)) ≪≫ ?_
    refine (a.2.map f.1) ◁ᵢ ?_ ≪≫
      (α_ (a.2.map f.1) (f.2.app b.1) (b.2.map g.1 ≫ g.2.app c.1)).symm
    refine (α_ (a.2.map g.1) (f.2.app c.1) (g.2.app c.1)).symm ≪≫
      ((f.2.naturality g.1) ▷ᵢ (g.2.app c.1)) ≪≫
      (α_ (f.2.app b.1) (b.2.map g.1) (g.2.app c.1))
  map₂_whisker_left {a b c} f {g h} {η} := by
    -- PARKED (diagonal switch, 2026-08-28).  The five coherence fields below were proved against
    -- the *other* diagonal via the `evaluation_*_core` lemmas in `EvaluationCore.lean` and
    -- `EvaluationAssociator.lean`.  Those cores are stated in raw expanded terms whose every
    -- point spelling changes under the flip, so they no longer apply and are left in place only
    -- as a source of re-derivable proof structure.
    --
    -- Sequence for picking these up, in order, one build each:
    --   1. `cat_disch` / `bicategory` on each field.  Cheap, and the honest prior is that it
    --      fails, but the answer decides whether the cores need to exist at all.
    --   2. If it fails: re-derive each core from the ACTUAL goal state using the two-layer
    --      template in notes/evaluation_coherence_wip.md.  Do not hand-edit the old cores into
    --      the new spellings; a subtly wrong statement only reports itself as a defeq failure at
    --      the `exact` plug, which is the most expensive way to find out.
    sorry
  map₂_whisker_right {a b c f g h} η := by
    sorry
  map₂_associator {a b c d} f g h := by
    -- Note this field was already parked before the diagonal switch, along with
    -- `evaluation_associator_core` beneath it.  Nothing is lost here.
    sorry
  map₂_left_unitor {a b} f := by
    sorry
  map₂_right_unitor {a b} f := by
    sorry

/-!
## Component API for `evaluationPseudo`

The structure fields of `evaluationPseudo` are large pastings, but every coherence obligation in
practice descends into a fibre, where only the *components* matter.  The lemmas below give those
components in reduced form.

These are deliberately **not** `@[simp]` — see the note in `Biyoneda.ForMathlib`: tagging them
globally adds a match attempt to every bare `simp` in the development.  Cite them explicitly.

Measured 2026-08-28: this API has **no uses outside this file**.  It is kept because the
`mapComp` component lemmas are the intended entry point for the coherence work above, not
because anything currently depends on it.
-/

section API

variable {x y : C × (C ⥤ᵖ Cat.{w, v})}

/-- `evaluationPseudo` on objects: `(c, F) ↦ F.obj c`. -/
lemma evaluationPseudo_obj (x : C × (C ⥤ᵖ Cat.{w, v})) :
    (evaluationPseudo (C := C)).obj x = x.2.obj x.1 := rfl

/-- `evaluationPseudo` on 1-morphisms, on Mathlib's diagonal. -/
lemma evaluationPseudo_map (f : x ⟶ y) :
    (evaluationPseudo (C := C)).map f = x.2.map f.1 ≫ f.2.app y.1 := rfl

/-- `evaluationPseudo`'s unit coherence is that of the first component. -/
lemma evaluationPseudo_mapId (x : C × (C ⥤ᵖ Cat.{w, v})) :
    (evaluationPseudo (C := C)).mapId x = x.2.mapId x.1 := rfl

/-- Point form of `evaluationPseudo_map`. -/
lemma evaluationPseudo_map_obj (f : x ⟶ y) (Z : ↑(x.2.obj x.1)) :
    ((evaluationPseudo (C := C)).map f).toFunctor.obj Z
      = (f.2.app y.1).toFunctor.obj ((x.2.map f.1).toFunctor.obj Z) := rfl

/-- Component of `evaluationPseudo.map₂`. -/
lemma evaluationPseudo_map₂_app {f g : x ⟶ y} (η : f ⟶ g) (Z : ↑(x.2.obj x.1)) :
    ((evaluationPseudo (C := C)).map₂ η).toNatTrans.app Z
      = (f.2.app y.1).toFunctor.map ((x.2.map₂ η.1).toNatTrans.app Z) ≫
        (η.2.as.app y.1).toNatTrans.app ((x.2.map g.1).toFunctor.obj Z) := rfl

/-- Component of `evaluationPseudo.mapId`. -/
lemma evaluationPseudo_mapId_hom_app (x : C × (C ⥤ᵖ Cat.{w, v})) (Z : ↑(x.2.obj x.1)) :
    ((evaluationPseudo (C := C)).mapId x).hom.toNatTrans.app Z
      = (x.2.mapId x.1).hom.toNatTrans.app Z := rfl

/-- Component of `evaluationPseudo.mapComp`, with the strict-`Cat` associator identities
already cancelled: only the source's `mapComp` and the naturality survive.

Cosmetic regression from the diagonal switch, recorded deliberately: on the previous diagonal
the `mapComp` factor was whiskered on the *right* and so appeared as a bare component
`(c.2.mapComp f.1 g.1).hom.app _`.  Here it is whiskered on the left, so it appears under a
`Functor.map`.  Nothing depends on this, but it is one more `Functor.map` for the folding
cascades in the coherence proofs to see past. -/
lemma evaluationPseudo_mapComp_hom_app {a b c : C × (C ⥤ᵖ Cat.{w, v})} (f : a ⟶ b) (g : b ⟶ c)
    (Z : ↑(a.2.obj a.1)) :
    ((evaluationPseudo (C := C)).mapComp f g).hom.toNatTrans.app Z
      = (f.2.app c.1 ≫ g.2.app c.1).toFunctor.map
            ((a.2.mapComp f.1 g.1).hom.toNatTrans.app Z) ≫
        (g.2.app c.1).toFunctor.map
            ((f.2.naturality g.1).hom.toNatTrans.app ((a.2.map f.1).toFunctor.obj Z)) := by
  dsimp only [evaluationPseudo]
  simp only [Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom, whiskerRightIso_hom,
    Cat.Hom.toNatTrans_comp, NatTrans.comp_app, Cat.whiskerLeft_toNatTrans,
    Cat.whiskerRight_toNatTrans, whiskerLeft_app, whiskerRight_app,
    Cat.associator_hom_toNatTrans_app, Cat.associator_inv_toNatTrans_app,
    Cat.Hom.comp_toFunctor, Functor.comp_obj, Category.id_comp, Category.comp_id]
  -- the `simp only` set above no longer reaches the `≪≫` chain on its own; a full `simp`
  -- does, and the residual is then definitional
  simp
  rfl

/-- Inverse form of `evaluationPseudo_mapComp_hom_app`. -/
lemma evaluationPseudo_mapComp_inv_app {a b c : C × (C ⥤ᵖ Cat.{w, v})} (f : a ⟶ b) (g : b ⟶ c)
    (Z : ↑(a.2.obj a.1)) :
    ((evaluationPseudo (C := C)).mapComp f g).inv.toNatTrans.app Z
      = (g.2.app c.1).toFunctor.map
            ((f.2.naturality g.1).inv.toNatTrans.app ((a.2.map f.1).toFunctor.obj Z)) ≫
        (f.2.app c.1 ≫ g.2.app c.1).toFunctor.map
            ((a.2.mapComp f.1 g.1).inv.toNatTrans.app Z) := by
  dsimp only [evaluationPseudo]
  simp only [Iso.trans_inv, Iso.symm_inv, whiskerLeftIso_inv, whiskerRightIso_inv,
    Cat.Hom.toNatTrans_comp, NatTrans.comp_app, Cat.whiskerLeft_toNatTrans,
    Cat.whiskerRight_toNatTrans, whiskerLeft_app, whiskerRight_app,
    Cat.associator_hom_toNatTrans_app, Cat.associator_inv_toNatTrans_app,
    Cat.Hom.comp_toFunctor, Functor.comp_obj, Category.id_comp, Category.comp_id]
  simp
  rfl

end API

end CategoryTheory.Bicategory
