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
import Biyoneda.UniverseLift
import Mathlib.CategoryTheory.Bicategory.Modification.Pseudo

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

attribute [local instance] uliftCategory

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
    rw [F.mapComp_assoc_left_inv]
    simp


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

/-- All five of `homPseudo`'s coherence fields close identically: descend to a point via
`Cat.Hom₂.ext_app`, retype it past the `Cat.of` coercion so `bicategory` sees a genuine morphism
(see the module docstring's "unblocking `bicategory`" note), then call `bicategory`. Factored
into one local tactic so the five fields below don't repeat the same six lines verbatim. -/
local macro "hom_coherence" a:term : tactic =>
  `(tactic| (
    dsimp [prelax]
    apply Cat.Hom₂.ext_app
    intro x
    dsimp
    change (unop ($a).1 ⟶ ($a).2) at x
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
      dsimp [prelax]
      rw [Bicategory.leftUnitor_naturality_assoc, Bicategory.rightUnitor_naturality,
        Category.assoc]
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
      simp only [whiskerRight_comp, whiskerLeft_comp, comp_whiskerLeft, Category.assoc,
        Iso.inv_hom_id_assoc, Iso.trans_assoc, Iso.trans_hom, whiskerLeftIso_hom,
        Iso.symm_hom, whiskerRightIso_hom, pentagon_inv_hom_hom_hom_inv,
        whiskerLeft_whiskerLeft_hom_inv_assoc, whisker_assoc, whiskerLeft_inv_hom_assoc]
  map₂_whisker_left {a b c} fg hi jk l := by hom_coherence a
  map₂_whisker_right {a b c} fg hi jk l := by hom_coherence a
  map₂_associator {a b c d} fg hi jk := by hom_coherence a
  map₂_left_unitor {a b} fg := by hom_coherence a
  map₂_right_unitor {a b} fg := by hom_coherence a

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

/-! ### Gadget 4 — strong transformations between `Cat`-valued pseudofunctors

`StrongTrans F G` requires `F` and `G` to land in the *same* bicategory, so two `Cat`-valued
pseudofunctors whose fibres sit in different universes cannot be related by one, even when the
data is perfectly well defined. `StrongTransIntoCats` is that data, with the two universes left
independent: `app a : F.obj a ⥤ G.obj a` typechecks across universes even though
`F ⟶ G` does not.

The coherence obligations are stated *pointwise*, which is the form fibre-level lemmas are
usually already in.

The universe relationship is deliberately absent from this type. It belongs to whatever consumes
the data: `StrongTransIntoCats.lift` and `.liftDom`, below, each
lift one side, and when the two universes happen to agree the transformation can be read off
directly with no lift at all. That is the improvement over carrying `catPseudoULift` in the
type: nothing is forced to be the bigger side. -/
structure StrongTransIntoCats {B : Type u} [Bicategory.{w₁, v₁} B]
    (F : B ⥤ᵖ Cat.{w₂, v₂}) (G : B ⥤ᵖ Cat.{w₃, v₃}) where
  /-- The component functor at each object. Its source and target may live in different
  universes — this is what `StrongTrans` cannot express. -/
  app : (b : B) → (F.obj b ⥤ G.obj b)
  /-- The naturality isomorphism, as a functor iso rather than a `Cat` 2-cell. -/
  naturality : {a b : B} → (f : a ⟶ b) →
    ((F.map f).toFunctor ⋙ app b) ≅ (app a ⋙ (G.map f).toFunctor)
  naturality_naturality' {a b : B} {f g : a ⟶ b} (η : f ⟶ g) (x : F.obj a) :
      (app b).map ((F.map₂ η).toNatTrans.app x) ≫ (naturality g).hom.app x =
      (naturality f).hom.app x ≫ (G.map₂ η).toNatTrans.app ((app a).obj x) := by cat_disch
  naturality_id' (a : B) (x : F.obj a) :
      (naturality (𝟙 a)).hom.app x ≫ (G.mapId a).hom.toNatTrans.app ((app a).obj x) =
      (app a).map ((F.mapId a).hom.toNatTrans.app x) := by cat_disch
  naturality_comp' {a b c : B} (f : a ⟶ b) (g : b ⟶ c) (x : F.obj a) :
      (naturality (f ≫ g)).hom.app x ≫ (G.mapComp f g).hom.toNatTrans.app ((app a).obj x) =
      (app c).map ((F.mapComp f g).hom.toNatTrans.app x) ≫
        (naturality g).hom.app ((F.map f).toFunctor.obj x) ≫
        (G.map g).toFunctor.map ((naturality f).hom.app x) := by cat_disch

structure ModificationIntoCats {B : Type u} [Bicategory.{w₁, v₁} B]
    {F : B ⥤ᵖ Cat.{w₂, v₂}} {G : B ⥤ᵖ Cat.{w₃, v₃}} (η θ : StrongTransIntoCats F G) where
    app (a : B) : NatTrans (η.app a) (θ.app a)
    naturality {a b : B} (f : a ⟶ b) :
      Functor.whiskerLeft (F.map f).toFunctor (app b) ≫ (θ.naturality f).hom =
        (η.naturality f).hom ≫ (Functor.whiskerRight (app a) (G.map f).toFunctor) := by cat_disch

/-! ### Turning the data into an actual `StrongTrans`

`StrongTransIntoCats` deliberately says nothing about how the two universes relate.  The three
constructions below are where that gets decided: `lift` lifts the codomain, `liftDom` the
domain, and `toStrongTransMax` both.  `lift` and `liftDom` are the useful ones in practice
because they leave one side alone — which is what lets them land on a pseudofunctor you can
still destructure.
-/

section CatLiftCodomain

variable {A : Type u} [Bicategory A]

variable {F : Pseudofunctor A Cat.{max v₁ v₂, max u₁ u₂}} {G : Pseudofunctor A Cat.{v₁, u₁}}
  (data : StrongTransIntoCats F G)

/-- Whiskered form of `naturality_naturality'`, in the shape `StrongTrans` asks for. -/
lemma StrongTransIntoCats.naturality_naturality {a b : A} {f g : a ⟶ b} (η : f ⟶ g) :
    Functor.whiskerRight (F.map₂ η).toNatTrans (data.app b) ≫ (data.naturality g).hom =
      (data.naturality f).hom ≫ Functor.whiskerLeft (data.app a) (G.map₂ η).toNatTrans := by
  ext x
  simpa using data.naturality_naturality' η x

/-- Whiskered form of `naturality_id'`, in the shape `StrongTrans` asks for. -/
lemma StrongTransIntoCats.naturality_id (a : A) :
    (data.naturality (𝟙 a)).hom ≫ Functor.whiskerLeft (data.app a) (G.mapId a).hom.toNatTrans =
      Functor.whiskerRight (F.mapId a).hom.toNatTrans (data.app a) ≫
        (Functor.leftUnitor (data.app a)).hom ≫ (Functor.rightUnitor (data.app a)).inv := by
  ext x
  dsimp [Functor.whiskerLeft]
  simpa only [Category.comp_id] using data.naturality_id' a x

/-- Whiskered form of `naturality_comp'`, in the shape `StrongTrans` asks for. -/
lemma StrongTransIntoCats.naturality_comp {a b c : A} (f : a ⟶ b) (g : b ⟶ c) :
    (data.naturality (f ≫ g)).hom ≫
        Functor.whiskerLeft (data.app a) (G.mapComp f g).hom.toNatTrans =
      Functor.whiskerRight (F.mapComp f g).hom.toNatTrans (data.app c) ≫
        (Functor.associator (F.map f).toFunctor (F.map g).toFunctor (data.app c)).hom ≫
        Functor.whiskerLeft (F.map f).toFunctor (data.naturality g).hom ≫
        (Functor.associator (F.map f).toFunctor (data.app b) (G.map g).toFunctor).inv ≫
        Functor.whiskerRight (data.naturality f).hom (G.map g).toFunctor ≫
        (Functor.associator (data.app a) (G.map f).toFunctor (G.map g).toFunctor).hom := by
  ext x
  simpa [Functor.associator, Functor.whiskerRight] using data.naturality_comp' f g x

set_option backward.isDefEq.respectTransparency false in
/-- Assemble `StrongTransIntoCats` into a genuine strong transformation into the lift. -/
def StrongTransIntoCats.lift : StrongTrans F (G.comp catPseudoULift) where
  app a := { toFunctor := data.app a ⋙ catLiftUnit (G.obj a) }
  naturality {a b} f :=
    Cat.Hom.isoMk (Functor.isoWhiskerRight (data.naturality f) (catLiftUnit (G.obj b)) ≪≫
      Iso.refl ((data.app a ⋙ (G.map f).toFunctor) ⋙ catLiftUnit (G.obj b)))
  naturality_naturality {a b f g} η := by
    apply catLift_hom₂_ext; intro X
    dsimp [catLiftUnit]
    simpa only [Category.comp_id] using NatTrans.congr_app (data.naturality_naturality η) X
  naturality_id a := by
    apply catLift_hom₂_ext; intro X
    dsimp [catLiftUnit, catPseudoULift, catLift, ULiftHom.up]
    simpa using NatTrans.congr_app (data.naturality_id a) X
  naturality_comp {a b c} f g := by
    apply catLift_hom₂_ext; intro X
    have h := NatTrans.congr_app (data.naturality_comp f g) X
    simp at h
    -- reduce the Cat-level structure and unfold the composite pseudofunctor's projections,
    -- but keep `catLiftUnit` folded so the stripping lemmas above can fire
    dsimp only [Pseudofunctor.comp, Functor.comp_map]
    -- every factor becomes `catLiftUnit.map _`; combine through the functor and apply `h`
    simpa [Cat.Hom.isoMk_hom, Iso.trans_hom, isoWhiskerRight_hom,
      Cat.Hom.toNatTrans_comp, NatTrans.comp_app,
      Cat.whiskerLeft_toNatTrans, Cat.whiskerRight_toNatTrans, whiskerLeft_app,
      whiskerRight_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      catPseudoULift_map_catLiftUnit_map, catPseudoULift_map₂_app_catLiftUnit,
      catPseudoULift_mapComp_hom_app, Category.comp_id]
      using congrArg (catLiftUnit.{v₁, u₁, v₂, u₂} (G.obj c)).map h

end CatLiftCodomain

section LiftSimp
variable {A : Type u} [Bicategory A] {F : Pseudofunctor A Cat.{max v₁ v₂, max u₁ u₂}}
  {G : Pseudofunctor A Cat.{v₁, u₁}} (data : StrongTransIntoCats F G)

/-- The lifted transformation's component, at the **functor** level: it is the unlifted
component followed by the (strict, transparent) unit.  Downstream reasoning should translate
through this rather than unfolding the lift to `ULift.up`/`.down`. -/
@[simp] lemma StrongTransIntoCats.lift_app_toFunctor (a : A) :
    ((StrongTransIntoCats.lift data).app a).toFunctor
      = data.app a ⋙ catLiftUnit (G.obj a) := rfl

/-- `Cat.Hom`-level form of `lift_app_toFunctor`. -/
lemma StrongTransIntoCats.lift_app (a : A) :
    (StrongTransIntoCats.lift data).app a
      = Functor.toCatHom (data.app a ⋙ catLiftUnit (G.obj a)) := rfl

end LiftSimp

/-! ### The dual gadget: a lifted *domain*

`StrongTransIntoCats` / `StrongTransIntoCats.lift` handle a transformation *into* a lifted
codomain, `StrongTrans F (G.comp catPseudoULift)`.  The Yoneda development also needs the other
side — `yonedaLemmaBackwards : yonedaEvaluation ⟶ yonedaPairing` has the lift in its **domain**.
The data is the same shape; only the plumbing moves from `catLiftUnit` to `catLiftCounit`.
-/

set_option linter.flexible false in
set_option backward.isDefEq.respectTransparency false in
/-- Assemble `StrongTransIntoCats` into a genuine strong transformation out of the lift. -/
def StrongTransIntoCats.liftDom {A : Type u} [Bicategory A]
    {G : Pseudofunctor A Cat.{v₁, u₁}} {F : Pseudofunctor A Cat.{max v₁ v₂, max u₁ u₂}}
    (data : StrongTransIntoCats G F) : StrongTrans (G.comp catPseudoULift) F where
  app a := { toFunctor := catLiftCounit (G.obj a) ⋙ data.app a }
  naturality {a b} f :=
    Cat.Hom.isoMk (Functor.isoWhiskerLeft (catLiftCounit (G.obj a)) (data.naturality f))
  naturality_naturality {a b f g} η := by
    apply catLift_hom₂_dom_ext; intro x
    exact data.naturality_naturality' η x
  naturality_id a := by
    apply catLift_hom₂_dom_ext; intro x
    simpa using data.naturality_id' a x
  naturality_comp {a b c} f g := by
    apply catLift_hom₂_dom_ext; intro x
    -- unfold the composite pseudofunctor's projections, then let the domain-side stripping
    -- lemmas above bring every factor back down through `catLiftCounit`
    dsimp only [Pseudofunctor.comp, Functor.comp_map]
    simp [Cat.Hom.isoMk_hom, isoWhiskerLeft_hom, Cat.Hom.toNatTrans_comp, NatTrans.comp_app,
      Cat.whiskerLeft_toNatTrans, Cat.whiskerRight_toNatTrans, whiskerLeft_app, whiskerRight_app,
      Cat.associator_hom_toNatTrans, Cat.associator_inv_toNatTrans, associator_hom_app,
      associator_inv_app, Functor.whiskerLeft_app, catPseudoULift_mapComp_hom_app,
      Category.comp_id]
    -- the residual `𝟙` sits at a different spelling of the fibre category, so `id_comp` needs
    -- to match up to unfolding
    erw [Category.id_comp]
    exact data.naturality_comp' f g x

/-- Precompose the data with the counit, turning a transformation out of `F` into one out of
the *lifted* `F`.  `catLiftCounit`'s interaction with `catPseudoULift` is definitional, so each
obligation is `d`'s own at the lowered point.

`naturality_naturality'` closes outright.  The other two reduce to `d`'s field modulo a single
residual `≫ 𝟙` that `Category.comp_id` will not collapse reducibly and `erw` does not bridge
either -- see the note on `toStrongTransMax`. -/
def StrongTransIntoCats.precomposeCounit {A : Type u} [Bicategory A]
    {F : Pseudofunctor A Cat.{v₁, u₁}} {G : Pseudofunctor A Cat.{v₂, u₂}}
    (d : StrongTransIntoCats F G) :
    StrongTransIntoCats (F.comp catPseudoULift.{v₁, v₂, u₁, u₂}) G where
  app a := catLiftCounit (F.obj a) ⋙ d.app a
  naturality {a b} f := Functor.isoWhiskerLeft (catLiftCounit (F.obj a)) (d.naturality f)
  naturality_naturality' {a b} {f g} η x :=
    d.naturality_naturality' η ((catLiftCounit (F.obj a)).obj x)
  naturality_id' a x := by
    -- PARKED.  The reduction that gets closest is
    --   dsimp only [Pseudofunctor.comp, Functor.comp_map, Functor.comp_obj]
    --   simp only [Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.trans_hom,
    --     PrelaxFunctor.map₂Iso_hom, Cat.Hom.toNatTrans_comp, NatTrans.comp_app,
    --     catLiftCounit_map_catPseudoULift_map₂', catPseudoULift_mapId_hom_app']
    -- after which the goal is `d`'s own `naturality_id'` at `(catLiftCounit _).obj x`, except
    -- for a residual `≫ 𝟙` on the right that neither `Category.comp_id` nor `erw` collapses:
    --   (d.app a).map ((counit).map ((map₂ (F.mapId a).hom).app x ≫ 𝟙 _))
    -- versus
    --   (d.app a).map ((F.mapId a).hom.app (counit.obj x))
    sorry
  naturality_comp' {a b c} f g x := by
    -- PARKED.  Same shape as `naturality_id'` above, with more factors.
    sorry

/-- The symmetric lift: a strong transformation between the *lifted copies* of both sides, so
neither is privileged.

This is the general form.  `lift` and `liftDom` are the cases where one side is already at the
target universe and can be left alone -- which is what makes them land on `yonedaPairing` and
`yonedaEvaluation` themselves rather than on lifted copies.

The construction is modular rather than hand-rolled: lower the domain with `precomposeCounit`,
then reuse the already-proven `lift`.  The universe arithmetic works because Lean's `max` is
commutative, so `F.comp catPseudoULift.{v₁, v₂, u₁, u₂}` and
`G.comp catPseudoULift.{v₂, v₁, u₂, u₁}` land in the same universe.  **That part typechecks**;
what is open is two of `precomposeCounit`'s three coherence fields. -/
def StrongTransIntoCats.toStrongTransMax {A : Type u} [Bicategory A]
    {F : Pseudofunctor A Cat.{v₁, u₁}} {G : Pseudofunctor A Cat.{v₂, u₂}}
    (d : StrongTransIntoCats F G) :
    StrongTrans (F.comp catPseudoULift.{v₁, v₂, u₁, u₂})
                (G.comp catPseudoULift.{v₂, v₁, u₂, u₁}) :=
  d.precomposeCounit.lift

end CategoryTheory.Bicategory

/-! The composite built from these three gadgets — `yonedaPairing` rebuilt as
`(yoneda.op).prod (Pseudofunctor.id _) ⋙ homPseudo (Bᵒᵖ ⥤ᵖ Cat)` — is in
`Biyoneda/CompositePairing.lean`, along with the results (no universe lift needed; `.obj` and
`.map` are `rfl`-equal to `Biyoneda.Basic`'s hand-rolled `yonedaPairing`). -/
