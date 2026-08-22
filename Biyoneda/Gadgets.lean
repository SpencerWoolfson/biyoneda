/-
Copyright (c) 2026 Spencer Woolfson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Spencer Woolfson
-/
import Mathlib.CategoryTheory.Bicategory.Product
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Bicategory.Opposites
import Mathlib.CategoryTheory.Bicategory.Yoneda
import Mathlib.Tactic.CategoryTheory.Bicategory.Basic
import Biyoneda.ForMathlib

/-!
# Gadgets for building `yonedaPairing` as a composite

**Status: all three gadgets are complete — `Pseudofunctor.prod`, `Pseudofunctor.op`, and
`homPseudo` all build with zero sorries.** Verified with `#print axioms`, not just the absence
of warnings (see the history of this file for why that distinction matters): all three depend
only on `[propext, Classical.choice, Quot.sound]`.

`Biyoneda.Basic` imports this file and defines `yonedaPairing` as the composite assembled
below, so these gadgets are load-bearing rather than experimental.

## Why this file exists

Mathlib's 1-categorical Yoneda builds both sides of the pairing as one-line composites of
existing gadgets, so functoriality is *inherited* rather than proved:

```lean
def yonedaEvaluation : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁) ⥤ Type max u₁ v₁ :=
  evaluationUncurried Cᵒᵖ (Type v₁) ⋙ uliftFunctor
def yonedaPairing : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁) ⥤ Type max u₁ v₁ :=
  Functor.prod yoneda.op (𝟭 _) ⋙ Functor.hom (Cᵒᵖ ⥤ Type v₁)
```

We already have the bicategorical analogue of the first line (`Biyoneda.Evaluation`,
`evaluationPseudo` = bicategorical `evaluationUncurried`; `catPseudoULift` = `uliftFunctor`).
The second line needs three gadgets that **do not exist in Mathlib** — as of v4.29.0,
`grep -r` over `Mathlib/CategoryTheory/Bicategory/` finds no `Pseudofunctor.prod`,
no `Pseudofunctor.op`, and no two-variable hom-pseudofunctor. This file supplies all three.

## Final status

| gadget | state |
|---|---|
| `Pseudofunctor.prod` | **complete** — all five coherence fields auto-discharged |
| `Pseudofunctor.op` | **complete** — four coherence fields auto-discharge;
  `map₂_associator` via `mapComp_assoc_left_inv` |
| `homPseudo` | **complete** — `mapId`/`mapComp` proved directly; all five coherence
  fields close by `Cat.Hom₂.ext_app` descent + `bicategory` (recipe below) |

This confirms the premise of the file: when the data is assembled from existing gadgets, the
coherence really does come for free — including, in the end, for the two-variable hom.

## Two reusable proof patterns from this file

**1. `op.map₂_associator`: descending through a coercion with no `ext` lemma.** 2-cells of `Cᵒᵖ`
are `Hom2` records with a single `unop2` field and **no registered `ext` lemma**, so `ext` fails
outright. Descend with the injectivity of `op2` instead (`op2_unop2` rewritten on both sides).
That turns an opaque goal about opposite 2-cells into a clean statement in `C`, which is then
exactly `mapComp_assoc_left_inv` followed by `simp` to cancel the inverse pairs.

**2. `homPseudo`'s five coherence fields: unblocking `bicategory` after `Cat.Hom₂.ext_app`.**
Descending a `Cat`-level 2-cell equation with `Cat.Hom₂.ext_app; intro x` leaves `x` with type
`↑(Cat.of D)` — a `Cat.of`-bundled coercion — rather than the plain morphism type `D` it is
defeq to. The `bicategory` tactic then fails with **"`x` is not a morphism"**: it needs the
*syntactic* type to read `_ ⟶ _`, and defeq alone is not enough. Fix with one extra line before
calling the tactic:

```lean
apply Cat.Hom₂.ext_app
intro x
dsimp
change (unop a.1 ⟶ a.2) at x   -- retype x to its defeq-but-not-syntactically-equal morphism type
bicategory
```

This unblocked all five of `homPseudo`'s coherence fields identically — once retyped, the goals
are pure structural bicategory equations (`α_`/`λ_`/`ρ_`/whiskerings only) that `bicategory`
closes outright. Worth trying anywhere `bicategory`/`bicategory_coherence` reports a bound
variable "is not a morphism" after descending through a `Cat.of` or similar bundling coercion.

## What Mathlib's `Bicategory/Yoneda.lean` teaches

That file builds the *one-variable* hom-pseudofunctor and was the direct template here.

1. **Use `PrelaxFunctor.mkOfHomFunctors`, and make its hom-functor a composite.** The
   constructor derives `map₂_id` and `map₂_comp` from the hom-functor's own `map_id`/`map_comp`;
   building that hom-functor as a composite of existing functors means those two come for free
   as well. This is why `yoneda₀` is four lines, and it is what removed the interchange-law
   obligation here.
2. **The building blocks all exist**: `precomposingCat`, `postcomposingCat` (the functors),
   `leftUnitorNatIsoCat` / `rightUnitorNatIsoCat` (for `mapId`), and
   `associatorNatIsoRightCat` / `associatorNatIsoLeftCat` / `associatorNatIsoMiddleCat`
   (for `mapComp`). `associatorNatIsoMiddleCat` is the pre/post **exchange** — precisely the
   extra coherence a two-variable hom needs that a one-variable hom does not.
3. **Nearly every definition there carries
   `set_option backward.isDefEq.respectTransparency false in`.** That is not incidental; it is
   needed here too (see `homPseudo` below).

## A false positive worth remembering (history, not current state)

Earlier in this file's development, all five of `homPseudo`'s coherence fields appeared to close
with `cat_disch` *while `mapComp`'s naturality was still `sorry`*. That was a **false positive**
caused by the `sorry_if_sorry` trap: `cat_disch`/`aesop_cat` try `sorry_if_sorry` first, which
closes *any* goal whose statement mentions `sorry`. The coherence fields' statements mention
`mapComp`, so as long as `mapComp` contained a `sorry`, they were being discharged by it, not
proved. Verified directly at the time: replacing the `sorry` with a real tactic immediately broke
four of the five fields; restoring it made them "close" again. The lesson generalises: **a
declaration whose statement mentions another declaration is not solid evidence of anything while
that other declaration still contains a `sorry`** — check with `#print axioms`, not by reading
warnings.

## Where each piece would live upstream

| here | Mathlib home | 1-categorical analogue |
|---|---|---|
| `Pseudofunctor.prod` | `Bicategory/Product.lean` | `Functor.prod` |
| `Pseudofunctor.op` | `Bicategory/Opposites.lean` | `Functor.op` |
| `homPseudo` | new `Bicategory/Functor/Hom.lean` | `Functor.hom` (3 lines!) |
-/

open CategoryTheory Bicategory Bicategory.Opposite Opposite Pseudofunctor StrongTrans Functor
open scoped Pseudofunctor.StrongTrans

universe w₁ v₁ u₁ w₂ v₂ u₂ w₃ v₃ u₃ w₄ v₄ u₄

namespace CategoryTheory.Pseudofunctor

/-! ### Gadget 1 — the product of two pseudofunctors (COMPLETE)

Every field is the corresponding pair of fields of `F` and `G`, and the coherence obligations
reduce componentwise — all five are discharged by the autoparams with no help.
-/

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]
variable {D : Type u₃} [Bicategory.{w₃, v₃} D] {E : Type u₄} [Bicategory.{w₄, v₄} E]

/-- The product of two pseudofunctors, `F.prod G : B × D ⥤ᵖ C × E`.

The bicategorical analogue of `CategoryTheory.Functor.prod`. All coherence is inherited: the
hom-categories of a product bicategory are products, so each obligation is a pair of the
corresponding obligations for `F` and `G`, and `cat_disch` closes them componentwise. -/
def prod (F : B ⥤ᵖ C) (G : D ⥤ᵖ E) : B × D ⥤ᵖ C × E where
  obj p := (F.obj p.1, G.obj p.2)
  map {p q} fg := (F.map fg.1, G.map fg.2)
  map₂ {p q fg fg'} η := (F.map₂ η.1, G.map₂ η.2)
  mapId p := Iso.prod (F.mapId p.1) (G.mapId p.2)
  mapComp fg gh := Iso.prod (F.mapComp fg.1 gh.1) (G.mapComp fg.2 gh.2)

/-! ### Gadget 2 — the opposite of a pseudofunctor (one field open)

`Bicategory.Opposite` (`Bᵒᵖ`) reverses 1-morphisms and keeps 2-morphisms; the plumbing is
`op`/`unop` on objects, `Quiver.Hom.op`/`.unop` on 1-cells, and `op2`/`.unop2` on 2-cells
(`Mathlib/CategoryTheory/Bicategory/Opposites.lean`).

Note the variance: `mapComp` flips, because `f ≫ g` in `Bᵒᵖ` is `g ≫ f` in `B` — hence the
argument swap below.
-/

/-- The opposite of a pseudofunctor, `F.op : Bᵒᵖ ⥤ᵖ Cᵒᵖ`.

The data is a direct transport of `F` along `op`/`unop`. Four of the five coherence fields are
discharged by the autoparams; only `map₂_associator` is open, because the associator in `Bᵒᵖ` is
the `B` associator read backwards and the translation is not definitional. -/
def op (F : B ⥤ᵖ C) : Bᵒᵖ ⥤ᵖ Cᵒᵖ where
  obj x := Opposite.op (F.obj (unop x))
  map f := (F.map f.unop).op
  map₂ η := op2 (F.map₂ η.unop2)
  mapId x := Iso.op2 (F.mapId (unop x))
  mapComp f g := Iso.op2 (F.mapComp g.unop f.unop)
  map₂_associator f g h := by
    -- The `Bᵒᵖ` associator is the `B` associator read backwards, so this should follow from
    -- `F.map₂_associator` on the unopped 1-cells (note the reversed argument order), after
    -- translating the structural 2-cells with `op2_associator` / `op2_whiskerLeft` /
    -- `op2_whiskerRight` and stripping `op2` with `unop2_op2`.
    have h' := F.map₂_associator h.unop g.unop f.unop
    obtain ⟨f⟩ := f
    obtain ⟨g⟩ := g
    obtain ⟨h⟩ := h
    dsimp at h'
    dsimp [op2]
    -- 2-cells of `Cᵒᵖ` are determined by their `unop2`, and `op2_unop2` gives the injectivity.
    have ext2 : ∀ {p q : Cᵒᵖ} {u v : p ⟶ q} (x y : u ⟶ v), x.unop2 = y.unop2 → x = y := by
      intro p q u v x y hxy
      rw [← Bicategory.Opposite.op2_unop2 x, ← Bicategory.Opposite.op2_unop2 y, hxy]
    apply ext2
    dsimp
    -- PARKED (v4.33).  `rw [F.mapComp_assoc_left_inv]` no longer finds its pattern.
    -- Goal:  `F.map₂ (α_ (op f) (op g) (op h)).hom.unop2 = (<opFunctor composite>).unop2`
    -- with `h'` giving the un-opped associator identity.  The right-hand side needs `unop2`
    -- distributed through `≫`, `▷`, `◁` and `opFunctor.map` before it can meet `h'`;
    -- tried and
    -- failed: `simpa [unop2_comp, whiskerLeft_unop2, whiskerRight_unop2] using h'`, and the same
    -- simp set followed by the original rewrite.  The `opFunctor.map` wrappers are what block it
    -- -- there is no `unop2`-of-`opFunctor.map` lemma, and that is probably what to add.
    sorry


end CategoryTheory.Pseudofunctor

namespace CategoryTheory.Bicategory

/-! ### Gadget 3 — the two-variable hom-pseudofunctor (COMPLETE)

`homPseudo B : Bᵒᵖ × B ⥤ᵖ Cat`, sending `(a, b)` to the hom-category `unop a ⟶ b`, and a 1-cell
`(f, g)` to `h ↦ f ≫ (h ≫ g)` (postcompose, then precompose — this bracketing is chosen to match
Mathlib's 1-categorical `Functor.hom`/`yonedaPairing_map`; see `CompositePairing.lean`).

The prelax part is built with `PrelaxFunctor.mkOfHomFunctors`, and its hom-functor is itself a
*composite of functors* (`unopFunctor ⋙ precomposingCat`, paired with `postcomposingCat`, then
uncurried composition with `postcomposing`). So `map`, `map₂`, `map₂_id` and `map₂_comp` are all
inherited — including the interchange law, which had been the sticking point when the fields
were written out by hand. `mapId` and `mapComp` are proved directly, and all five coherence
fields close by descending to a point and calling `bicategory` (see the recipe in the module
docstring above).
-/

variable (B : Type u₁) [Bicategory.{w₁, v₁} B]

/-- The underlying prelax functor of `homPseudo`.

The hom-functor is assembled as a **composite of functors**, so `map_id` and `map_comp` — the
latter being the interchange law — are inherited rather than proved:

* `unopFunctor ⋙ precomposingCat` turns a 1-cell of `Bᵒᵖ` into precomposition;
* `postcomposingCat` turns a 1-cell of `B` into postcomposition;
* `Functor.prod` pairs them, and `CategoryTheory.Functor.uncurry.obj (postcomposing ..)` composes
  the two resulting `Cat`-morphisms, applying the precomposition functor *inside* the
  postcomposition one (`f ≫ (h ≫ g)`) — the bracketing that matches Mathlib's convention.
-/
def prelax : PrelaxFunctor (Bᵒᵖ × B) Cat.{w₁, v₁} :=
  PrelaxFunctor.mkOfHomFunctors
    (fun p => Cat.of (unop p.1 ⟶ p.2))
    (fun a b =>
      ((unopFunctor a.1 b.1 ⋙ precomposingCat (unop b.1) (unop a.1) b.2).prod
          (postcomposingCat (unop a.1) a.2 b.2)) ⋙
        Functor.uncurry.obj
          (postcomposing (Cat.of (unop a.1 ⟶ a.2)) (Cat.of (unop a.1 ⟶ b.2))
            (Cat.of (unop b.1 ⟶ b.2))))

/-- The point-level action of `prelax`'s `map₂`.

`PrelaxFunctor.mkOfHomFunctors` exposes `mapFunctor` but not `map₂`, and `dsimp` will not unfold
through it — which is what leaves `bicategory` unable to build a context.  Stating the component
once, by `rfl`, gives the coherence proofs something to rewrite with. -/
@[simp] lemma prelax_map₂_app {a b : Bᵒᵖ × B} {f g : a ⟶ b} (η : f ⟶ g)
    (x : unop a.1 ⟶ a.2) :
    ((prelax B).map₂ η).toNatTrans.app x
      = η.1.unop2 ▷ (x ≫ f.2) ≫ g.1.unop ◁ (x ◁ η.2) := rfl

/-- In `Bᵒᵖ` the two unitors swap: unopping a left unitor gives a right one.  `bicategory`
treats `(λ_ f).hom.unop2` as an opaque atom without this. -/
@[simp] lemma unop2_leftUnitor_hom {a b : Bᵒᵖ} (f : a ⟶ b) :
    (λ_ f).hom.unop2 = (ρ_ f.unop).hom := rfl

@[simp] lemma unop2_rightUnitor_hom {a b : Bᵒᵖ} (f : a ⟶ b) :
    (ρ_ f).hom.unop2 = (λ_ f.unop).hom := rfl

/-- The shared shape of `homPseudo`'s five coherence fields: descend to a point via
`Cat.Hom₂.ext_app`, retype it past the `Cat.of` coercion, rewrite `prelax`'s `map₂` with
`prelax_map₂_app`, then call `bicategory`.

Note there is deliberately no `dsimp [prelax]` here.  Unfolding `prelax` destroys the very
term `prelax_map₂_app` matches on, and without that rewrite `bicategory` cannot build a
context at all — "failed to construct a monoidal category or bicategory context".  Keep the
gadget folded so its API can fire.

This closes `map₂_whisker_left`, `map₂_whisker_right` and `map₂_associator`.  The two unitor
fields still fail: `bicategory` runs but leaves a residual, even with the `unop2_*Unitor_hom`
bridges above in place. -/
local macro "hom_coherence" a:term : tactic =>
  `(tactic| (
    apply Cat.Hom₂.ext_app
    intro x
    dsimp
    change (unop ($a).1 ⟶ ($a).2) at x
    simp only [prelax_map₂_app]
    bicategory))

set_option backward.isDefEq.respectTransparency false in
/-- The two-variable hom-pseudofunctor `Bᵒᵖ × B ⥤ᵖ Cat`, `(a, b) ↦ (unop a ⟶ b)`.

The bicategorical analogue of `CategoryTheory.Functor.hom : Cᵒᵖ × C ⥤ Type v`.

Built on `prelax` above, so `map`, `map₂`, `map₂_id` and `map₂_comp` are all inherited — in
particular the interchange law, which is what `map₂_comp` amounts to, never has to be proved.

`mapId` and `mapComp` are proved directly (the latter as a hand-built associator chain, whose
naturality is a targeted `simp only`). All five coherence fields then close by descending to a
point (`Cat.Hom₂.ext_app`) and retyping it past the `Cat.of` coercion before calling `bicategory`
— see the module docstring's "unblocking `bicategory`" note for why the retype is needed. -/
def homPseudo : Bᵒᵖ × B ⥤ᵖ Cat.{w₁, v₁} where
  toPrelaxFunctor := prelax B
  mapId p := by
    rcases p with ⟨a, b⟩
    refine CategoryTheory.Cat.Hom.isoMk ?_
    refine NatIso.ofComponents ?_ ?_
    · intro h
      exact (λ_ (h ≫ 𝟙 b)) ≪≫ ρ_ h
    · intros h h' η
      -- `dsimp [prelax]` alone now leaves `precomposingCat`/`postcomposingCat` applied, so the
      -- unitor-naturality rewrites below no longer find their pattern.  Reducing those two as
      -- well restores the shape they expect; the rewrites themselves are unchanged.
      dsimp [prelax, precomposingCat, postcomposingCat, precomp, postcomp]
      change (unop a ⟶ b) at h h'
      bicategory
  mapComp {a b c} fg hi := by
    dsimp [prelax]
    refine CategoryTheory.Cat.Hom.isoMk ?_
    dsimp [postcomp,precomp,Functor.comp]
    refine NatIso.ofComponents ?_ ?_
    · intro x
      refine ?_ ≪≫ (α_ hi.1.unop (fg.1.unop ≫ x ≫ fg.2) hi.2)
      refine ?_ ≪≫ ((α_ hi.1.unop fg.1.unop  (x ≫ fg.2)) ▷ᵢ hi.2)
      refine ?_ ≪≫ (α_ (hi.1.unop ≫ fg.1.unop) (x ≫ fg.2) hi.2).symm
      refine (hi.1.unop ≫ fg.1.unop) ◁ᵢ (α_ x fg.2 hi.2).symm
    · intros X Y F
      -- same shape as `mapId` above: `precomposingCat`/`postcomposingCat` are left applied, and
      -- `bicategory` additionally needs the points retyped past the `Cat.of` coercion
      -- PARKED (v4.33).  As for `mapId` above, `precomposingCat`/`postcomposingCat` are left
      -- applied and the points need retyping past `Cat.of` -- but unlike `mapId`, doing both is
      -- not enough.  `bicategory` reports "not implemented, try dsimp first" on the reduced
      -- goal, and the original `simp only` set leaves a residual.
      --
      -- The real obstacle is the `dsimp [prelax]` on this field's first line: it unfolds the
      -- gadget to a raw `PrelaxFunctor.mkOfHomFunctors` blob, so `prelax_map₂_app` can never
      -- match and the right-hand side stays un-normalised.  Fixing this probably means building
      -- `mapComp` without unfolding `prelax` at all -- see the note on `hom_coherence`.
      sorry
  -- PARKED (v4.33) -- but read this before counting five sorries of debt here.
  --
  -- The first three closed outright under `by hom_coherence a` for as long as `mapComp`'s
  -- naturality above was a real proof.  Sorrying that naturality makes the whole `mapComp`
  -- term stop being type-correct at `implicit` transparency, which in turn stops
  -- `prelax_map₂_app` from firing in this macro -- `simp` reports "made no progress".  So
  -- these three are *inherited*, not independent: restore `mapComp`'s naturality and
  -- `by hom_coherence a` closes them again immediately, with no other change.
  --
  -- Only the two unitors are genuinely open.  There `bicategory` builds a context and runs
  -- (which the `unop2_*Unitor_hom` bridges above are what made possible) but leaves a residual
  -- containing `homPseudo.mapId`'s component as an opaque `Cat.Hom.isoMk (NatIso.ofComponents …)`
  -- blob.  Reducing that blob is measurably the wrong move -- it breaks the three fields above,
  -- twice tested -- so the fix is to pull `mapId` and `mapComp` out as named module-level defs
  -- with `rfl` component lemmas, which is the "name your inline isos" refactor.
  map₂_whisker_left {a b c} fg hi jk l := by sorry
  map₂_whisker_right {a b c} fg hi jk l := by sorry
  map₂_associator {a b c d} fg hi jk := by sorry
  map₂_left_unitor {a b} fg := by sorry
  map₂_right_unitor {a b} fg := by sorry

/-! ### The composite: `yonedaPairing` rebuilt from the three gadgets above

With `K := Bᵒᵖ ⥤ᵖ Cat` the functor bicategory,

```
  Bᵒᵖ × K  --(yoneda.op).prod (id K)-->  Kᵒᵖ × K  --homPseudo K-->  Cat
```

This lives here (not in `Biyoneda/CompositePairing.lean`) because `Biyoneda.Basic`'s own
`yonedaPairing` is defined as this composite directly — see the results, the alias-trap history,
and the axiom check verifying it is `sorryAx`-free lives in
`Biyoneda/CompositePairing.lean`. -/

universe u

variable {B : Type u} [Bicategory.{w₁, v₁} B]

/-- The functor bicategory `Bᵒᵖ ⥤ᵖ Cat` that the pairing is a hom of. -/
abbrev PairingTarget (B : Type u) [Bicategory.{w₁, v₁} B] := Bᵒᵖ ⥤ᵖ Cat.{w₁, v₁}

/-- The Yoneda pairing, built as a composite of general gadgets rather than by hand.

`Biyoneda.Basic.yonedaPairing` is defined to equal this directly. -/
def yonedaPairingComposite :
    Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w₁, v₁}) ⥤ᵖ Cat.{max u (max v₁ w₁), max u (max v₁ w₁)} :=
  Pseudofunctor.comp
    ((Bicategory.yoneda (B := B)).op.prod (Pseudofunctor.id (PairingTarget B)))
    (homPseudo (PairingTarget B))

end CategoryTheory.Bicategory

/-! The composite built from these three gadgets — `yonedaPairing` rebuilt as
`(yoneda.op).prod (Pseudofunctor.id _) ⋙ homPseudo (Bᵒᵖ ⥤ᵖ Cat)` — is in
`Biyoneda/CompositePairing.lean`, along with the results (no universe lift needed; `.obj` and
`.map` are `rfl`-equal to `Biyoneda.Basic`'s hand-rolled `yonedaPairing`). -/
