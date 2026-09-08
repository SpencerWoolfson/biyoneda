/-
Copyright (c) 2026 Spencer Woolfson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Spencer Woolfson
-/
module

public import Mathlib.CategoryTheory.Bicategory.Product
public import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
public import Mathlib.Tactic.ApplyFun

/-!
# Currying for pseudofunctors

The bicategorical analogue of `CategoryTheory.Functor.currying`: a pseudofunctor out of a
product bicategory is the same thing as a pseudofunctor into a bicategory of pseudofunctors.

  `A × B ⥤ᵖ C   ≃   A ⥤ᵖ B ⥤ᵖ C`

## Status

**Work in progress, and deliberately outside the build.**  This module is not imported by
`Biyoneda.lean`, so Lake does not compile it and none of the project gates apply to it: the
sorry ratchet, the axiom ratchet and the warning baseline all ignore everything below.  Compile
it by hand with

```
lake env lean Biyoneda/BiCurrying.lean
```

Nothing here is used by `Biyoneda.yonedaLemma`, which remains sorry-free.

What is actually proved, as of 2026-09-07:

| declaration | state |
|---|---|
| `whiskerRightPseudo` | 3 of 4 fields proved; `naturality_comp` parked with its residual goal |
| `liftToProd` | complete |
| `liftToProdMap` | data complete, all three coherence fields parked with residual goals |
| `curryObj` | `obj` pinned down; `map` onwards parked |
| `uncurryObj` | `obj`/`map` pinned down; `mapId` parked mid-chain, rest parked |
| `curry`, `uncurry`, and the two round trips | types only |

Every `sorry` below carries the residual goal it was parked on.  That is the format this
project uses for stuck work — see the "budget compile cycles, then park" discipline in
`CLAUDE.md`; a parked goal is resumable, a broken half-state is archaeology.

## Why this is not a `Bicategory.Equivalence` of the two sides

`Bicategory.Equivalence x y` is an **internal** equivalence: `x` and `y` must be two *objects of
one bicategory*.  Here the two sides are themselves bicategories, so the statement

```lean
def currying : Bicategory.Equivalence (A × B ⥤ᵖ C) (A ⥤ᵖ B ⥤ᵖ C)
```

asks Lean for `Bicategory (Type _)` and fails.  The notion actually wanted is a *biequivalence*,
which Mathlib cannot state directly because there is no tricategory `Bicat`.

The formulation below is the one Mathlib's structures do support, and it is the same shape
`Biyoneda.yonedaLemma` uses: give the two pseudofunctors, then say each round trip is
internally equivalent to the identity **in the appropriate functor bicategory** — `X ⥤ᵖ X` is a
bicategory (the scoped instance in `FunctorBicategory.Pseudo`), so `≌` typechecks there.

## The 1-categorical template

`Mathlib/CategoryTheory/Functor/Currying.lean` is the model, and worth reading first:

* `Functor.curryObj (F : C × D ⥤ E) : C ⥤ D ⥤ E` — `obj X` has `map g := F.map (𝟙 X ×ₘ g)`,
  and `map f` has `app Y := F.map (f ×ₘ 𝟙 Y)`.
* `Functor.uncurry : (C ⥤ D ⥤ E) ⥤ C × D ⥤ E` — note the diagonal it picks,
  `(F.map f.1).app X.2 ≫ (F.obj Y.1).map f.2`.  **Match it.**  This development has already
  been bitten once by choosing the other diagonal (see `Biyoneda/Evaluation.lean`'s header):
  the two are isomorphic but not equal, and in a bicategory the difference is a coherence
  obligation rather than an equation.
* `Functor.currying : C ⥤ D ⥤ E ≌ C × D ⥤ E` — an `Equivalence` of *categories*, which is
  exactly the step that does not transpose to this setting.

## Where the work is — measured, not guessed

Probed 2026-09-07 on the inner component of `curryObj`, the pseudofunctor
`b ↦ F.obj (a, b)`, `g ↦ F.map (𝟙 a, g)`, `η ↦ F.map₂ (𝟙 (𝟙 a), η)`:

* `map₂_id` — **free.**  `(𝟙 (𝟙 a), 𝟙 f) = 𝟙 (𝟙 a, f)` holds by `rfl` in the product bicategory,
  so it is one `rw` and `F.map₂_id`.
* `map₂_comp` — **cheap.**  `(𝟙 (𝟙 a), η ≫ θ) = (𝟙 (𝟙 a), η) ≫ (𝟙 (𝟙 a), θ)` needs
  `𝟙 (𝟙 a) = 𝟙 (𝟙 a) ≫ 𝟙 (𝟙 a)`, which `simp` supplies; then `F.map₂_comp`.
* `mapId` — **free.**  It is exactly `F.mapId (a, b)`.
* `mapComp` — **this is the real obstacle.**  `exact F.mapComp (𝟙 a, g) (𝟙 a, g')` does *not*
  typecheck: it produces the constraint for `(𝟙 a ≫ 𝟙 a, g ≫ g')`, and the first coordinate
  differs from `𝟙 a` by a unitor.  So the iso has to be built as `F.mapComp` conjugated by
  `F.map₂` of a left (or right) unitor.  This is the bicategorical content the 1-categorical
  proof does not have — there `𝟙 X ≫ 𝟙 X = 𝟙 X` on the nose.
* The five coherence laws (`map₂_whisker_left` and friends) were **not** measured.  Expect them
  to inherit the same unitor correction, since they are stated in terms of `mapComp`.

`liftToProd` below packages exactly that inner component, so the unitor correction is isolated
in its `mapComp` field rather than spread through `curryObj`.

The same correction reappears one level up, in `curry`'s action on strong transformations,
for the same reason.

## A note on `cat_disch` in the product bicategory

`cat_disch` closes almost nothing in `A × B`.  Its 2-cells are *pairs*, its unitors and
associators are `Iso.prod` of the two factors' unitors and associators, and the simp set does
not descend through `Iso.prod` to get at the coordinates.  Every parked goal in `liftToProdMap`
has this shape.  The move that is expected to work — untested, this is the candidate, not a
result — is to descend first with `Prod.ext` / `Iso.prod_hom` so the goal splits into two
independent 2-cell equations, and only then run `bicategory` on each coordinate.
-/

@[expose] public section

namespace CategoryTheory.Pseudofunctor

open CategoryTheory Bicategory
open scoped Pseudofunctor.StrongTrans

universe u₁ u₂ u₃ v₁ v₂ v₃ w₁ w₂ w₃

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
  [Bicategory.{w₁, v₁} A] [Bicategory.{w₂, v₂} B] [Bicategory.{w₃, v₃} C]

/-! ### Whiskering a strong transformation by a pseudofunctor

Not currying-specific, and the piece most likely to be wanted upstream.  Note the name: Mathlib
already has `StrongTrans.whiskerRight`, which whiskers a *modification* by a strong
transformation.  This is the other operation — whiskering a strong transformation by a
pseudofunctor — so it needs a distinct name. -/

set_option backward.isDefEq.respectTransparency false in
/-- Post-whisker a strong transformation of pseudofunctors by a following pseudofunctor.
The bicategorical analogue of `CategoryTheory.Functor.whiskerRight` for `NatTrans`. -/
def whiskerRightPseudo {F G : A ⥤ᵖ B} (η : StrongTrans F G) (H : B ⥤ᵖ C) :
    StrongTrans (F.comp H) (G.comp H) where
  app a := H.map (η.app a)
  naturality {a b} f :=
    (H.mapComp (F.map f) (η.app b)).symm ≪≫ H.map₂Iso (η.naturality f) ≪≫
      H.mapComp (η.app a) (G.map f)
  naturality_naturality {a b f g} θ := by
    have e1 : (F.comp H).map₂ θ = H.map₂ (F.map₂ θ) := rfl
    have e2 : (G.comp H).map₂ θ = H.map₂ (G.map₂ θ) := rfl
    have e3 : (H.map₂Iso (η.naturality g)).hom = H.map₂ (η.naturality g).hom := rfl
    have e4 : (H.map₂Iso (η.naturality f)).hom = H.map₂ (η.naturality f).hom := rfl
    simp only [Iso.trans_hom, Iso.symm_hom, e1, e2]
    have h := congrArg H.map₂ (η.naturality_naturality θ)
    simp only [H.map₂_comp, Pseudofunctor.map₂_whisker_left,
      Pseudofunctor.map₂_whisker_right] at h
    have h2 := congrArg (· ≫ (H.mapComp (η.app a) (G.map g)).hom) h
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h2
    have h3 := congrArg ((H.mapComp (F.map f) (η.app b)).inv ≫ ·) h2
    simpa [Category.assoc] using h3
  naturality_id a := by
    have e1 : ((F.comp H).mapId a).hom = H.map₂ (F.mapId a).hom ≫ (H.mapId (F.obj a)).hom := rfl
    have e2 : ((G.comp H).mapId a).hom = H.map₂ (G.mapId a).hom ≫ (H.mapId (G.obj a)).hom := rfl
    have e3 : (H.map₂Iso (η.naturality (𝟙 a))).hom = H.map₂ (η.naturality (𝟙 a)).hom := rfl
    simp only [Iso.trans_hom, Iso.symm_hom, e1, e2, e3, Bicategory.whiskerLeft_comp,
      Bicategory.comp_whiskerRight, Category.assoc]
    -- `e6` is Mathlib's `whiskerLeft_mapId_inv` solved for `H.map₂ (ρ_ _).inv`.
    have e6 : H.map₂ (ρ_ (η.app a)).inv =
        (ρ_ (H.map (η.app a))).inv ≫ H.map (η.app a) ◁ (H.mapId (G.obj a)).inv ≫
          (H.mapComp (η.app a) (𝟙 (G.obj a))).inv := by
      simp [whiskerLeft_mapId_inv]
    have h := congrArg H.map₂ (η.naturality_id a)
    simp only [H.map₂_comp, Pseudofunctor.map₂_whisker_left, Pseudofunctor.map₂_whisker_right,
      Pseudofunctor.map₂_left_unitor, e6, Category.assoc] at h
    simp only [Iso.inv_hom_id_assoc] at h
    apply_fun (· ≫ (H.mapComp (η.app a) (𝟙 (G.obj a))).hom) at h
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h
    apply_fun (· ≫ H.map (η.app a) ◁ (H.mapId (G.obj a)).hom) at h
    simp only [Category.assoc, ← Bicategory.whiskerLeft_comp, Iso.inv_hom_id,
      Bicategory.whiskerLeft_id, Category.comp_id] at h
    apply_fun ((H.mapComp (F.map (𝟙 a)) (η.app a)).inv ≫ ·) at h
    simpa [Category.assoc] using h
  naturality_comp {a b c} f g := by
    have e1 : ((F.comp H).mapComp f g).hom =
        H.map₂ (F.mapComp f g).hom ≫ (H.mapComp (F.map f) (F.map g)).hom := rfl
    have e2 : ((G.comp H).mapComp f g).hom =
        H.map₂ (G.mapComp f g).hom ≫ (H.mapComp (G.map f) (G.map g)).hom := rfl
    have e3 : (H.map₂Iso (η.naturality (f ≫ g))).hom = H.map₂ (η.naturality (f ≫ g)).hom := rfl
    have e4 : (H.map₂Iso (η.naturality g)).hom = H.map₂ (η.naturality g).hom := rfl
    have e5 : (H.map₂Iso (η.naturality f)).hom = H.map₂ (η.naturality f).hom := rfl
    simp only [Iso.trans_hom, Iso.symm_hom, e1, e2, e3, e4, e5,
      Bicategory.whiskerLeft_comp, Bicategory.comp_whiskerRight, Category.assoc]
    -- `e7` is Mathlib's `mapComp_assoc_left_inv` solved for `H.map₂ (α_ _ _ _).inv`.
    have e7 : H.map₂ (α_ (F.map f) (η.app b) (G.map g)).inv =
        (H.mapComp (F.map f) (η.app b ≫ G.map g)).hom ≫
          H.map (F.map f) ◁ (H.mapComp (η.app b) (G.map g)).hom ≫
          (α_ (H.map (F.map f)) (H.map (η.app b)) (H.map (G.map g))).inv ≫
          (H.mapComp (F.map f) (η.app b)).inv ▷ H.map (G.map g) ≫
          (H.mapComp (F.map f ≫ η.app b) (G.map g)).inv := by
      simp [mapComp_assoc_left_inv]
    have h := congrArg H.map₂ (η.naturality_comp f g)
    simp only [H.map₂_comp, Pseudofunctor.map₂_whisker_left, Pseudofunctor.map₂_whisker_right,
      Pseudofunctor.map₂_associator, e7, Category.assoc, Iso.inv_hom_id_assoc] at h
    -- PARKED 2026-09-07, budget exhausted (this field is `naturality_comp`, the pentagon one).
    -- `h` at this point is fully expanded and cancelled down to:
    --   H.map₂(η.naturality (f≫g)).hom ≫ (mapComp ηa,(G.map(f≫g))).hom
    --     ≫ ηa ◁ H.map₂(G.mapComp f g).hom ≫ (mapComp ηa,(G.map f≫G.map g)).inv
    --   = (mapComp F.map(f≫g),ηc).hom ≫ H.map₂(F.mapComp f g).hom▷ηc ≫ (mapComp F.map f,F.map g).hom▷ηc
    --     ≫ α_(H.map F.map f)(H.map F.map g)(H.map ηc)).hom ≫ H.map(F.map f)◁(mapComp F.map g,ηc).inv
    --     ≫ H.map(F.map f)◁H.map₂(η.naturality g).hom ≫ H.map(F.map f)◁(mapComp ηb,G.map g).hom
    --     ≫ α_(H.map F.map f)(H.map ηb)(H.map G.map g)).inv ≫ (mapComp F.map f,ηb).inv▷H.map(G.map g)
    --     ≫ H.map₂(η.naturality f).hom▷H.map(G.map g) ≫ (mapComp ηa,G.map f).hom▷H.map(G.map g)
    --     ≫ α_(H.map ηa)(H.map G.map f)(H.map G.map g)).hom
    --     ≫ ηa◁(mapComp G.map f,G.map g).inv ≫ (mapComp ηa,G.map f≫G.map g).inv.
    -- The actual goal's LHS ends in `ηa ◁ (mapComp G.map f, G.map g).hom` (from unfolding
    -- `(G.comp H).mapComp f g` via its `Pseudofunctor.comp` definition), not in
    -- `(mapComp ηa, G.map f ≫ G.map g).inv` as `h` does: the two trailing coherence cells are
    -- genuinely different 2-isomorphisms (one whiskers the *split* composite, the other collapses
    -- the *joint* one), and bridging them needs one more instance of Mathlib's `mapComp`
    -- associativity pentagon, `Pseudofunctor.mapComp_assoc_right_hom`/`mapComp_assoc_left_hom`
    -- (`Bicategory/Functor/Pseudofunctor.lean:169,176`), applied at `(η.app a, G.map f, G.map g)`,
    -- the same way `e7` above discharged the *other* leftover associator. That substitution
    -- introduces yet another `H.map₂ (α_ _ _ _)` term and a fresh `mapComp` pair, which then need
    -- the same cancel-by-`apply_fun` treatment as `naturality_naturality`/`naturality_id` above
    -- before it will match the goal. Candidate next step: state that pentagon instance as an
    -- `e8` exactly mirroring `e7`, `simp` it into `h`, then continue the
    -- `apply_fun (· ≫ _)`/`apply_fun (_ ≫ ·)` chain used for the first two fields.
    sorry
/-! ### Lifting into a product

`liftToProd a : B ⥤ᵖ A × B` is the inner component of `curryObj`, packaged on its own, and
`liftToProdMap f` is its action on a 1-cell of `A`.  Together they are what turns `F : A × B ⥤ᵖ C`
into a pseudofunctor `A ⥤ᵖ B ⥤ᵖ C` by composition. -/

/-- The pseudofunctor `b ↦ (a, b)`, the bicategorical `Functor.prodLift` for a fixed first
coordinate.  Both coherence isos are strict here: `𝟙 a ≫ 𝟙 a` and `𝟙 a` differ by a unitor, and
`⊗𝟙` is the tensor unitor that names it. -/
def liftToProd (a : A) : B ⥤ᵖ A × B where
  obj b := (a, b)
  map g := (𝟙 a, g)
  map₂ η := (𝟙 (𝟙 a), η)
  mapId b := Iso.refl (𝟙 a, 𝟙 b)
  mapComp g g' := Iso.prod ⊗𝟙 ⊗𝟙

/-- The action of `liftToProd` on a 1-cell `f : X ⟶ Y` of `A`: a strong transformation
`liftToProd X ⟶ liftToProd Y` whose component at `b` is `(f, 𝟙 b)`.

**Parked 2026-09-07.**  The data (`app`, `naturality`) is complete and elaborates; all three
coherence fields are open.  `cat_disch` fails on each — see the module docstring's note on
`cat_disch` in a product bicategory for why, and for the candidate route (split with `Prod.ext` /
`Iso.prod_hom`, then `bicategory` per coordinate).

The three residual goals, captured verbatim by `trace_state`, are recorded at each field. -/
def liftToProdMap {X Y : A} (f : X ⟶ Y) : StrongTrans (liftToProd (B := B) X) (liftToProd Y) where
  app b := (f, 𝟙 b)
  naturality {b b'} g := Iso.prod ((λ_ f) ≪≫ (ρ_ f).symm) ((ρ_ g) ≪≫ (λ_ g).symm)
  naturality_naturality {a b f' g} θ := by
    -- PARKED. Residual goal (`θ : f' ⟶ g` a 2-cell of `B`):
    --   (liftToProd X).map₂ θ ▷ (f, 𝟙 b) ≫ ((λ_ f ≪≫ (ρ_ f).symm).prod (ρ_ g ≪≫ (λ_ g).symm)).hom
    --     = ((λ_ f ≪≫ (ρ_ f).symm).prod (ρ_ f' ≪≫ (λ_ f').symm)).hom
    --       ≫ (f, 𝟙 a) ◁ (liftToProd Y).map₂ θ
    -- First coordinate is `𝟙 (𝟙 X) ▷ f ≫ λ_ f ≫ (ρ_ f).inv = λ_ f ≫ (ρ_ f).inv ≫ f ◁ 𝟙 (𝟙 Y)`,
    -- which `bicategory` should take; second is the same statement with `θ` in place of the
    -- identity 2-cell. Neither is visible to `cat_disch` while they sit inside `Iso.prod`.
    sorry
  naturality_id b := by
    -- PARKED. Residual goal:
    --   ((λ_ f ≪≫ (ρ_ f).symm).prod (ρ_ (𝟙 b) ≪≫ (λ_ (𝟙 b)).symm)).hom
    --       ≫ (f, 𝟙 b) ◁ ((liftToProd Y).mapId b).hom
    --     = ((liftToProd X).mapId b).hom ▷ (f, 𝟙 b) ≫ (λ_ (f, 𝟙 b)).hom ≫ (ρ_ (f, 𝟙 b)).inv
    -- Both `mapId`s are `Iso.refl`, so after `Iso.refl_hom` and the whisker-of-identity lemmas
    -- this should be pure unitor coherence in each coordinate.
    sorry
  naturality_comp g g' := by
    -- PARKED. Residual goal (`g : a ⟶ b`, `g' : b ⟶ c` in `B`):
    --   ((λ_ f ≪≫ (ρ_ f).symm).prod (ρ_ (g ≫ g') ≪≫ (λ_ (g ≫ g')).symm)).hom
    --       ≫ (f, 𝟙 a) ◁ ((liftToProd Y).mapComp g g').hom
    --     = ((liftToProd X).mapComp g g').hom ▷ (f, 𝟙 c)
    --       ≫ (α_ ((liftToProd X).map g) ((liftToProd X).map g') (f, 𝟙 c)).hom
    --       ≫ (liftToProd X).map g ◁ ((λ_ f ≪≫ (ρ_ f).symm).prod (ρ_ g' ≪≫ (λ_ g').symm)).hom
    --       ≫ (α_ ((liftToProd X).map g) (f, 𝟙 b) ((liftToProd Y).map g')).inv
    --       ≫ ((λ_ f ≪≫ (ρ_ f).symm).prod (ρ_ g ≪≫ (λ_ g).symm)).hom ▷ (liftToProd Y).map g'
    --       ≫ (α_ (f, 𝟙 a) ((liftToProd Y).map g) ((liftToProd Y).map g')).hom
    -- This is the expensive one: six factors, and the associators are `Iso.prod` of `A`'s and
    -- `B`'s. Do the other two fields first — they will show whether the split-then-`bicategory`
    -- route works before it is spent on this.
    sorry

/-! ### Object level

The two directions on a single pseudofunctor.  These are the useful half in practice: they are
what lets a pseudofunctor defined in one form be *used* in the other, which is the whole reason
to want currying here. -/

/-- Curry a pseudofunctor out of a product.

The object action is settled: `curryObj F` sends `a` to `(liftToProd a).comp F`, which is
`b ↦ F.obj (a, b)` with the unitor correction already absorbed into `liftToProd`'s `mapComp`.

**Parked 2026-09-07** from `map` onwards.  What is owed:

* `map f` should be `F` post-whiskered onto `liftToProdMap f`, i.e. the `whiskerRightPseudo`
  above applied to `liftToProdMap f` and `F`.  That is why `whiskerRightPseudo` is in this file.
  It cannot be written yet: `whiskerRightPseudo` needs its `naturality_comp`, and
  `liftToProdMap` needs all three of its coherence fields.  Finish those two first — this
  field is then a one-liner, not a proof.
* `map₂` sends a 2-cell `θ : f ⟶ g` of `A` to a modification; its component at `b` is
  `F.map₂ (θ, 𝟙 (𝟙 b))`.
* `mapId`, `mapComp` and the five coherence laws inherit the unitor correction described in
  the module docstring. -/
def curryObj (F : A × B ⥤ᵖ C) : A ⥤ᵖ B ⥤ᵖ C where
  obj a := (liftToProd a).comp F
  map {X Y} f := whiskerRightPseudo (liftToProdMap f) F
  map₂ := sorry
  mapId := sorry
  mapComp := sorry
  map₂_id := sorry

/-- Uncurry a pseudofunctor into a bicategory of pseudofunctors.

Follow `Functor.uncurry`, and in particular its choice of diagonal:
`map (f, g) := (G.map f.1).app X.2 ≫ (G.obj Y.1).map f.2`.  That choice is made below and
should not be changed without reading `Biyoneda/Evaluation.lean`'s header first. -/
def uncurryObj (G : A ⥤ᵖ B ⥤ᵖ C) : A × B ⥤ᵖ C where
  obj x := (G.obj x.1).obj x.2
  map {X Y} f := (G.map f.1).app X.2 ≫ (G.obj Y.1).map f.2
  map₂ := sorry
  mapId a := by
    -- PARKED 2026-09-07 mid-chain: the two easy steps are taken, the third needs a name.
    -- Goal after the two `refine`s below: `(G.map (𝟙 a.1)).app a.2 ⟶ 𝟙 ((G.obj a.1).obj a.2)`,
    -- and `i3 : G.map (𝟙 a.1) ≅ 𝟙 (G.obj a.1)` is an iso of *strong transformations*, one
    -- level too high. Its component at `a.2` is what is wanted.
    --
    -- Candidate next move: 2-cells of `B ⥤ᵖ C` are a wrapper around `Modification` with field
    -- `as` (see `FunctorBicategory/Pseudo.lean`, where `whiskerLeft` writes `Γ.as.app a`), so
    -- the component should be `(G.mapId a.1).hom.as.app a.2`. Unverified — `#check` it in a
    -- probe before building on it. If it typechecks, the remaining gap to `𝟙` is the
    -- `StrongTrans.id` component, which is `𝟙` up to a unitor.
    have i1 := (G.obj a.1).mapId a.2
    let h := (G.map (𝟙 a.1)).app a.2 ◁ᵢ i1
    refine Iso.trans h ?_
    have i2 := ρ_ ((G.map (𝟙 a.1)).app a.2)
    refine Iso.trans i2 ?_
    sorry
  mapComp := sorry
  map₂_id := sorry

/-! ### Pseudofunctor level

`curryObj`/`uncurryObj` promoted to pseudofunctors between the two bicategories.  Each needs an
action on strong transformations (1-cells) and on modifications (2-cells), plus the coherence
laws.

The coherence fields are spelled out as explicit `sorry`s rather than left to their autoparams.
That is not style: with `map₂ := sorry`, the `map₂_id` autoparam is handed
`sorry (𝟙 f) = 𝟙 (sorry f)`, aesop cannot close it, and the *whole declaration* fails with a
hard error — which in turn suppresses every sorry warning in the file and makes the parked work
above look clean when it is not.  Keep them explicit until `map₂` is real. -/

/-- Currying, as a pseudofunctor between the two bicategories.

**Parked: type only.**  Blocked on `curryObj`, and on `curryObj`'s action on strong
transformations, which needs the same unitor correction one level up. -/
def curry : (A × B ⥤ᵖ C) ⥤ᵖ (A ⥤ᵖ B ⥤ᵖ C) where
  obj := curryObj
  map := sorry
  map₂ := sorry
  mapId := sorry
  mapComp := sorry
  map₂_id := sorry
  map₂_comp := sorry
  map₂_whisker_left := sorry
  map₂_whisker_right := sorry
  map₂_associator := sorry
  map₂_left_unitor := sorry
  map₂_right_unitor := sorry

/-- Uncurrying, as a pseudofunctor between the two bicategories.

**Parked: type only.**  Blocked on `uncurryObj`. -/
def uncurry : (A ⥤ᵖ B ⥤ᵖ C) ⥤ᵖ (A × B ⥤ᵖ C) where
  obj := uncurryObj
  map := sorry
  map₂ := sorry
  mapId := sorry
  mapComp := sorry
  map₂_id := sorry
  map₂_comp := sorry
  map₂_whisker_left := sorry
  map₂_whisker_right := sorry
  map₂_associator := sorry
  map₂_left_unitor := sorry
  map₂_right_unitor := sorry

/-! ### The round trips

Stated as internal equivalences in the functor bicategories `X ⥤ᵖ X`, which is what Mathlib can
express.  Together these say `curry` and `uncurry` are a biequivalence, without naming one.

**Parked: types only.**  Both are downstream of everything above; there is nothing to attempt
here until `curry` and `uncurry` are real. -/

/-- Uncurrying after currying is the identity, up to internal equivalence. -/
def curryCompUncurry :
    Bicategory.Equivalence (curry.comp uncurry) (Pseudofunctor.id (A × B ⥤ᵖ C)) := sorry

/-- Currying after uncurrying is the identity, up to internal equivalence. -/
def uncurryCompCurry :
    Bicategory.Equivalence (uncurry.comp curry) (Pseudofunctor.id (A ⥤ᵖ B ⥤ᵖ C)) := sorry

end CategoryTheory.Pseudofunctor
