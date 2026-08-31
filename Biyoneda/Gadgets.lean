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
| `homPseudo` | **complete** — `mapId`/`mapComp` are named module-level defs; all five
  coherence fields close by `Cat.Hom₂.ext_app` descent + `bicategory` (recipe below) |

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
**Order matters**: do the `change` *after* the `simp only`, never before — see `hom_coherence`.

**3. Name the inline isos, or the coherence fields cannot be proved at all.** `mapId` and
`mapComp` were originally `where`-block tactic blocks. That made the five coherence fields
depend on how those two *elaborate* rather than on what they *are*, and the dependency was
mutual: sorrying `mapComp`'s naturality stopped the whole `mapComp` term being type-correct at
`implicit` transparency, which stopped `prelax_map₂_app` firing, which broke the three fields
that had nothing to do with `mapComp` — while restoring those three changed `mapComp`'s own
goal enough that `bicategory` stopped applying. Neither end could be fixed alone.

Pulling them out as `homMapId`/`homMapComp`, with the component of each an explicit iso in `B`
and a `rfl` component lemma for each, breaks the cycle: the fields now rewrite with a lemma
instead of unfolding a definition, so nothing downstream depends on anyone's elaboration. That
is the whole reason this gadget is finished. It is the same "name your inline isos" move the
skill recommends, and here it was not a cleanup — it was the proof.

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
    dsimp [opFunctor]
    simp [F.map₂_iso_inv (α_ h g f)]

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

/-! `unopFunctor` is strictly (contra)functorial.  Naming that as `rfl` bridges matters for the
same reason `catLift_map_comp` does in UniverseLift: without them the coherence goals below
carry the same 1-cell spelled two ways -- `(unopFunctor a c).obj (f ≫ g)` on one side,
`g.unop ≫ f.unop` on the other -- and nothing can match across the two. -/

@[simp] lemma unopFunctor_obj_comp {a b c : Bᵒᵖ} (f : a ⟶ b) (g : b ⟶ c) :
    (unopFunctor a c).obj (f ≫ g) = g.unop ≫ f.unop := rfl

@[simp] lemma unopFunctor_obj_id {a : Bᵒᵖ} :
    (unopFunctor a a).obj (𝟙 a) = 𝟙 (unop a) := rfl

/-- In `Bᵒᵖ` the two unitors swap: unopping a left unitor gives a right one.  `bicategory`
treats `(λ_ f).hom.unop2` as an opaque atom without this. -/
@[simp] lemma unop2_leftUnitor_hom {a b : Bᵒᵖ} (f : a ⟶ b) :
    (λ_ f).hom.unop2 = (ρ_ f.unop).hom := rfl

@[simp] lemma unop2_rightUnitor_hom {a b : Bᵒᵖ} (f : a ⟶ b) :
    (ρ_ f).hom.unop2 = (λ_ f.unop).hom := rfl

/-- Whiskering in `Bᵒᵖ` unops to whiskering on the other side.  Mathlib generates these from
the instance via `@[simps!]`, but under names that are not in scope here; both are `rfl`. -/
@[simp] lemma unop2_whiskerLeft {a b c : Bᵒᵖ} {f : a ⟶ b} {g g' : b ⟶ c} (η : g ⟶ g') :
    (f ◁ η).unop2 = η.unop2 ▷ f.unop := rfl

@[simp] lemma unop2_whiskerRight {a b c : Bᵒᵖ} {f f' : a ⟶ b} {g : b ⟶ c} (η : f ⟶ f') :
    (η ▷ g).unop2 = g.unop ◁ η.unop2 := rfl

/-- The associator of `Bᵒᵖ` is the `B` associator read backwards -- so unopping its `hom` gives
an `inv`.  `map₂_associator` is the only field that meets it. -/
@[simp] lemma unop2_associator_hom {a b c d : Bᵒᵖ} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (α_ f g h).hom.unop2 = (α_ h.unop g.unop f.unop).inv := rfl

@[simp] lemma unop2_associator_inv {a b c d : Bᵒᵖ} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (α_ f g h).inv.unop2 = (α_ h.unop g.unop f.unop).hom := rfl

/-- The composite of Mathlib's generated `prod_associator_hom_fst` with `unop2_associator_hom`.
Stated in one step because neither fires on `(α_ fg hi jk).hom.1.unop2` on its own -- simp needs
a single syntactic match for the projection-then-unop chain. -/
@[simp] lemma prod_associator_hom_fst_unop2 {a b c d : Bᵒᵖ × B} (fg : a ⟶ b) (hi : b ⟶ c)
    (jk : c ⟶ d) :
    (α_ fg hi jk).hom.1.unop2 = (α_ jk.1.unop hi.1.unop fg.1.unop).inv := rfl

/-- The unitor analogues of `prod_associator_hom_fst_unop2`.  In `Bᵒᵖ` the two unitors swap,
so a left unitor on the first (opposite) factor unops to a right unitor. -/
@[simp] lemma prod_leftUnitor_hom_fst_unop2 {a b : Bᵒᵖ × B} (fg : a ⟶ b) :
    (λ_ fg).hom.1.unop2 = (ρ_ fg.1.unop).hom := rfl

@[simp] lemma prod_rightUnitor_hom_fst_unop2 {a b : Bᵒᵖ × B} (fg : a ⟶ b) :
    (ρ_ fg).hom.1.unop2 = (λ_ fg.1.unop).hom := rfl


/-- The object action of `prelax`'s `map`, as a `rfl` bridge.  Companion to
`prelax_map₂_app`: without it the coherence goals carry `((prelax B).map f).toFunctor.obj x`
un-normalised and `bicategory` sees an atom where a composite should be. -/
@[simp] lemma prelax_map_obj {a b : Bᵒᵖ × B} (f : a ⟶ b) (x : unop a.1 ⟶ a.2) :
    ((prelax B).map f).toFunctor.obj x = f.1.unop ≫ (x ≫ f.2) := rfl

/-- The morphism action of `prelax`'s `map`.  `map₂_whisker_right` is the one field that whiskers
a 2-cell *through* a 1-cell's image, so it is the only one that needs this. -/
@[simp] lemma prelax_map_map {a b : Bᵒᵖ × B} (f : a ⟶ b) {x y : unop a.1 ⟶ a.2} (η : x ⟶ y) :
    ((prelax B).map f).toFunctor.map η = f.1.unop ◁ (η ▷ f.2) := rfl

/-! ### `homPseudo`'s two coherence isos, as named module-level definitions

Both were originally written inline in `homPseudo`'s `where` block.  That made the five
coherence fields depend on how `mapId`/`mapComp` *elaborate* rather than on what they *are*:
sorrying `mapComp`'s naturality stopped the whole `mapComp` term being type-correct at
`implicit` transparency, which stopped `prelax_map₂_app` firing in `hom_coherence`, which broke
the three fields that had nothing to do with `mapComp`.  The dependency was mutual and neither
end could be fixed alone.

Naming them breaks that cycle.  The component of each is an explicit iso in `B` -- no `Cat`, no
`prelax` -- and each gets a `rfl` component lemma, so the coherence fields below rewrite with a
lemma instead of unfolding a definition.
-/

/-- The component of `homPseudo`'s unit coherence: `ᵽ ≫ (h ≫ ᵽ) ≅ h`. -/
def homMapIdApp {p : Bᵒᵖ × B} (h : unop p.1 ⟶ p.2) :
    𝟙 (unop p.1) ≫ (h ≫ 𝟙 p.2) ≅ h :=
  λ_ (h ≫ 𝟙 p.2) ≪≫ ρ_ h

/-- The component of `homPseudo`'s composition coherence, as an explicit chain of associators
in `B`.  Reading it off the two sides: `prelax` sends `x` to `f.unop ≫ (x ≫ g)`, so composing
`fg` then `hi` gives `hi₁ ≫ ((fg₁ ≫ (x ≫ fg₂)) ≫ hi₂)`, while the composite 1-cell
`fg ≫ hi` gives `(hi₁ ≫ fg₁) ≫ (x ≫ (fg₂ ≫ hi₂))`.  Four associator moves connect them. -/
def homMapCompApp {a b c : Bᵒᵖ × B} (fg : a ⟶ b) (hi : b ⟶ c) (x : unop a.1 ⟶ a.2) :
    (hi.1.unop ≫ fg.1.unop) ≫ (x ≫ (fg.2 ≫ hi.2)) ≅
      hi.1.unop ≫ ((fg.1.unop ≫ (x ≫ fg.2)) ≫ hi.2) :=
  ((hi.1.unop ≫ fg.1.unop) ◁ᵢ (α_ x fg.2 hi.2).symm) ≪≫
    (α_ (hi.1.unop ≫ fg.1.unop) (x ≫ fg.2) hi.2).symm ≪≫
      ((α_ hi.1.unop fg.1.unop (x ≫ fg.2)) ▷ᵢ hi.2) ≪≫
        α_ hi.1.unop (fg.1.unop ≫ x ≫ fg.2) hi.2

/-- Naturality of `homMapIdApp`.  A pure structural goal in `B`: no `Cat`, no `prelax`. -/
lemma homMapIdApp_naturality {p : Bᵒᵖ × B} {h h' : unop p.1 ⟶ p.2} (η : h ⟶ h') :
    𝟙 (unop p.1) ◁ (η ▷ 𝟙 p.2) ≫ (homMapIdApp B (p := p) h').hom
      = (homMapIdApp B (p := p) h).hom ≫ η := by
  dsimp [homMapIdApp]
  bicategory

/-- Naturality of `homMapCompApp`.  Likewise pure structural data in `B`. -/
lemma homMapCompApp_naturality {a b c : Bᵒᵖ × B} (fg : a ⟶ b) (hi : b ⟶ c)
    {x y : unop a.1 ⟶ a.2} (F : x ⟶ y) :
    (hi.1.unop ≫ fg.1.unop) ◁ (F ▷ (fg.2 ≫ hi.2)) ≫ (homMapCompApp B fg hi y).hom
      = (homMapCompApp B fg hi x).hom ≫ hi.1.unop ◁ ((fg.1.unop ◁ (F ▷ fg.2)) ▷ hi.2) := by
  dsimp [homMapCompApp]
  simp only [Iso.symm_hom, Bicategory.whiskerLeftIso_hom, Bicategory.whiskerRightIso_hom]
  bicategory

/-- `homPseudo`'s unit coherence iso. -/
def homMapId (p : Bᵒᵖ × B) : (prelax B).map (𝟙 p) ≅ 𝟙 ((prelax B).obj p) :=
  Cat.Hom.isoMk
    (NatIso.ofComponents (fun h ↦ homMapIdApp B (p := p) h) (fun η ↦ homMapIdApp_naturality B η))

/-- `homPseudo`'s composition coherence iso. -/
def homMapComp {a b c : Bᵒᵖ × B} (fg : a ⟶ b) (hi : b ⟶ c) :
    (prelax B).map (fg ≫ hi) ≅ (prelax B).map fg ≫ (prelax B).map hi :=
  Cat.Hom.isoMk
    (NatIso.ofComponents (fun x ↦ homMapCompApp B fg hi x)
      (fun F ↦ homMapCompApp_naturality B fg hi F))

/-- The point form of `homMapId`.  This is what the coherence fields rewrite with, instead of
unfolding the definition -- which is the whole reason these two are named. -/
@[simp] lemma homMapId_hom_app (p : Bᵒᵖ × B) (h : unop p.1 ⟶ p.2) :
    (homMapId B p).hom.toNatTrans.app h = (homMapIdApp B (p := p) h).hom := rfl

/-- The point form of `homMapComp`. -/
@[simp] lemma homMapComp_hom_app {a b c : Bᵒᵖ × B} (fg : a ⟶ b) (hi : b ⟶ c)
    (x : unop a.1 ⟶ a.2) :
    (homMapComp B fg hi).hom.toNatTrans.app x = (homMapCompApp B fg hi x).hom := rfl

@[simp] lemma homMapId_inv_app (p : Bᵒᵖ × B) (h : unop p.1 ⟶ p.2) :
    (homMapId B p).inv.toNatTrans.app h = (homMapIdApp B (p := p) h).inv := rfl

@[simp] lemma homMapComp_inv_app {a b c : Bᵒᵖ × B} (fg : a ⟶ b) (hi : b ⟶ c)
    (x : unop a.1 ⟶ a.2) :
    (homMapComp B fg hi).inv.toNatTrans.app x = (homMapCompApp B fg hi x).inv := rfl

/-- The shared shape of `homPseudo`'s five coherence fields: descend to a point via
`Cat.Hom₂.ext_app`, retype it past the `Cat.of` coercion, rewrite `prelax`'s `map₂` with
`prelax_map₂_app`, then call `bicategory`.

Note there is deliberately no `dsimp [prelax]` here.  Unfolding `prelax` destroys the very
term `prelax_map₂_app` matches on, and without that rewrite `bicategory` cannot build a
context at all — "failed to construct a monoidal category or bicategory context".  Keep the
gadget folded so its API can fire.

Two details are load-bearing and were both found the hard way:

* **No `dsimp [prelax]`.**  Unfolding `prelax` destroys the very term `prelax_map₂_app` matches
  on, and without that rewrite `bicategory` cannot build a context at all.  Keep the gadget
  folded so its API can fire.
* **The `change` goes AFTER the `simp only`, not before.**  `bicategory` needs `x`'s
  *syntactic* type to read `_ ⟶ _` rather than `↑(Cat.of _)`, so the retype is required -- but
  performing it first makes the goal not type-correct at `implicit` transparency and `simp`
  reports "made no progress" on every field.

With those, all five fields close. -/
local macro "hom_coherence" a:term : tactic =>
  `(tactic| (
    apply Cat.Hom₂.ext_app
    intro x
    dsimp
    simp only [homMapIdApp, homMapCompApp, prod_associator_hom_fst_unop2,
      prod_leftUnitor_hom_fst_unop2, prod_rightUnitor_hom_fst_unop2,
      prod_associator_hom_snd, prod_leftUnitor_hom_snd, prod_rightUnitor_hom_snd,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      Bicategory.whiskerLeftIso_hom, Bicategory.whiskerLeftIso_inv,
      Bicategory.whiskerRightIso_hom, Bicategory.whiskerRightIso_inv]
    change (unop ($a).1 ⟶ ($a).2) at x
    bicategory))

set_option backward.isDefEq.respectTransparency false in
/-- The two-variable hom-pseudofunctor `Bᵒᵖ × B ⥤ᵖ Cat`, `(a, b) ↦ (unop a ⟶ b)`.

The bicategorical analogue of `CategoryTheory.Functor.hom : Cᵒᵖ × C ⥤ Type v`.

Built on `prelax` above, so `map`, `map₂`, `map₂_id` and `map₂_comp` are all inherited — in
particular the interchange law, which is what `map₂_comp` amounts to, never has to be proved.

`mapId` and `mapComp` are the named module-level defs `homMapId`/`homMapComp` above rather than
inline `where`-block terms — see the note there for why that distinction decides whether the
five coherence fields can be proved at all. All five then close by descending to a point
(`Cat.Hom₂.ext_app`), rewriting with the component `rfl` bridges, and retyping the point past
the `Cat.of` coercion before calling `bicategory` — see the module docstring's "unblocking
`bicategory`" note for why the retype is needed. -/
def homPseudo : Bᵒᵖ × B ⥤ᵖ Cat.{w₁, v₁} where
  toPrelaxFunctor := prelax B -- prelax here needs a better name
  mapId p := homMapId B p
  mapComp fg hi := homMapComp B fg hi
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

end CategoryTheory.Bicategory

/-! The composite built from these three gadgets — `yonedaPairing` rebuilt as
`(yoneda.op).prod (Pseudofunctor.id _) ⋙ homPseudo (Bᵒᵖ ⥤ᵖ Cat)` — is in
`Biyoneda/CompositePairing.lean`, along with the results (no universe lift needed; `.obj` and
`.map` are `rfl`-equal to `Biyoneda.Basic`'s hand-rolled `yonedaPairing`). -/
