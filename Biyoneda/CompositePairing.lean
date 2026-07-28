/-
Copyright (c) 2026 Spencer Woolfson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Spencer Woolfson
-/
import Biyoneda.Gadgets
import Biyoneda.UniverseLift
import Biyoneda.Basic

/-!
# `yonedaPairing` as a composite of gadgets (branch `composite-pairing`)

**Experiment. Not imported by `Biyoneda.Basic`.**

`Biyoneda.Basic` defines `yonedaPairing` by hand, with its coherence fields written out and one
still `sorry`-ed (`mapComp`'s `map₂` naturality). Mathlib's 1-categorical `yonedaPairing` is
instead a one-line composite, so functoriality is inherited:

```lean
def yonedaPairing : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁) ⥤ Type max u₁ v₁ :=
  Functor.prod yoneda.op (𝟭 _) ⋙ Functor.hom (Cᵒᵖ ⥤ Type v₁)
```

`Biyoneda.Gadgets` now supplies the three bicategorical analogues:

| gadget | status |
|---|---|
| `Pseudofunctor.prod` | complete |
| `Pseudofunctor.op` | complete |
| `homPseudo` | one open obligation (naturality inside `mapComp`) |

so the composite can be attempted. The plan, with `K := Bᵒᵖ ⥤ᵖ Cat` the functor bicategory:

```
  Bᵒᵖ × K  --(yoneda.op).prod (id K)-->  Kᵒᵖ × K  --homPseudo K-->  Cat
```

## The two things to find out

1. **Does it typecheck at all?** `homPseudo` is generic in its bicategory, so it applies to `K`;
   but `K`'s hom-categories are `StrongTrans` with modifications, which is the heavy instance —
   `precomp`/`postcomp` there are whiskering of strong transformations. This is the first real
   test of `homPseudo` outside a toy setting.
2. **Universes.** `Basic.lean`'s `yonedaPairing` lands in `Cat.{max u (max v w), max u (max v w)}`,
   whereas `homPseudo K` lands in `Cat.{w₁, v₁}` for `K`'s own bicategory universes. Expect to
   need `catPseudoULift` (`Biyoneda.UniverseLift`) in the composite, exactly as
   `yonedaEvaluation` does — that is why this file imports it.

Start by uncommenting the definition below and reading the error; the mismatch it reports is the
actual specification of what still has to be bridged. Do not "fix" it by weakening the target
type — the point is to land on the *same* statement `Basic.lean` uses, so that
`yonedaPairing` can be replaced and its `sorry` retired.
-/

open CategoryTheory Bicategory Bicategory.Opposite Opposite Pseudofunctor StrongTrans Functor

universe w v u

namespace CategoryTheory.Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

/-- Abbreviation for the functor bicategory the pairing is a hom of. -/
abbrev PairingTarget (B : Type u) [Bicategory.{w, v} B] := Bᵒᵖ ⥤ᵖ Cat.{w, v}

def yonedaPairingComposite :
    Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v}) ⥤ᵖ Cat.{max u (max v w), max u (max v w)} :=
  Pseudofunctor.comp
    ((Bicategory.yoneda (B := B)).op.prod (Pseudofunctor.id (PairingTarget B)))
    (homPseudo (PairingTarget B))

/-!
## Results so far

**1. The composite typechecks.** `yonedaPairingComposite` above elaborates with no errors, at
exactly the target type `Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v}) ⥤ᵖ Cat.{max u (max v w), max u (max v w)}`.

Two things about that are better than expected:

* **No universe lift was needed.** The prediction was that `homPseudo` would land in the wrong
  universe and need `catPseudoULift` inserted, mirroring `yonedaEvaluation`. It does not — the
  universes line up on their own. (`UniverseLift` is still imported in case a later step wants it.)
* **`homPseudo` survives its first real instance.** Up to now it had only been exercised
  abstractly; here it is applied to `K = Bᵒᵖ ⥤ᵖ Cat`, whose hom-categories are `StrongTrans` with
  modifications, so `precomp`/`postcomp` are whiskering of strong transformations. That is the
  heavy case, and it went through.

**2. It is NOT definitionally equal to the hand-rolled `yonedaPairing`.**

```lean
example : yonedaPairingComposite (B := B) = yonedaPairing := rfl   -- FAILS: type mismatch
```

So the two are different terms that should be isomorphic, not the same term. This is the real
specification of the remaining work.

## Next steps

1. Establish the relationship. Either prove `yonedaPairingComposite ≅ yonedaPairing` (an
   iso of pseudofunctors), or — more useful — **replace** `Basic.lean`'s `yonedaPairing` with the
   composite outright, which is what actually retires its `mapComp` `sorry`.
2. If replacing: budget for the **alias trap**. Every `simp`/`dsimp` unfold list naming
   `yonedaPairing` will stop one delta short and downstream ordered `erw` chains will break in
   confusing, far-away places. `grep` for `yonedaPairing` inside `simp`/`dsimp`/`unfold` brackets
   *first* and plan a fix per site. See `notes/level2_refactor.md` — this exact failure cost
   several build cycles when `yonedaEvaluation'` was aliased.
3. `homPseudo` still owes the naturality square inside its `mapComp` (`Biyoneda/Gadgets.lean`).
   That is inherited by anything built on it, so the composite is only as finished as that.

## Does this help with the six sorries? Measured answer: not yet, and here is exactly why

An axiom check settles it:

```
#print axioms yonedaPairingComposite
  -- depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
#print axioms yonedaPairing
  -- depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

**Both depend on `sorryAx`.** The composite does not reduce the sorry burden — it *relocates* it.
`Basic.lean`'s `yonedaPairing` carries its own `mapComp` `sorry`; the composite instead inherits
`homPseudo`'s open naturality square. Net zero.

So the whole payoff of this branch is gated on exactly one obligation: **the naturality square in
`homPseudo.mapComp`.** Close that, and:

* the composite becomes `sorryAx`-free,
* replacing `yonedaPairing` with it retires sorry #1 of the six for real,
* and the ~100 lines of hand-rolled `yonedaPairing` fields collapse to a three-line definition.

Until then the branch is a strictly-nicer *definition* with the same proof debt, and nothing
downstream gets easier. That is worth knowing before investing in rewriting the other five
sorries against it.

### What is and is not established

| claim | status |
|---|---|
| composite typechecks at Basic's exact target type | **verified** |
| no `catPseudoULift` needed (universes line up) | **verified** — contrary to the initial guess |
| `homPseudo` works at the heavy instance `K = Bᵒᵖ ⥤ᵖ Cat` | **verified** |
| `.obj` agrees definitionally with the hand-rolled pairing | **verified** (`rfl`) |
| `.map` agrees definitionally | **false**, and the reason is now pinned down: a *bracketing* difference only — the composite gives `(postcomp₂ f ≫ η) ≫ f.2`, the hand-rolled gives `postcomp₂ f ≫ (η ≫ f.2)`. They differ by one associator. |
| composite admits Mathlib's `rfl` API lemma (`yonedaPairing_map` analogue) | **verified** — see `yonedaPairingComposite_map` |
| composite reduces sorry count | **false today** — both sides hit `sorryAx` |
| the other five sorries get easier | **untested**, and untestable until the square closes |
-/

section Diagnostic


-- Where exactly do the composite and the hand-rolled pairing diverge?
example (x : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})) :
    (yonedaPairingComposite (B := B)).obj x = yonedaPairing.obj x := rfl

-- `map` does NOT match (type mismatch on `rfl`).

end Diagnostic

/-! ## The Mathlib-style API lemma

Mathlib does not leave a composite definition opaque. In `CategoryTheory/Yoneda.lean` it defines
`yonedaPairing` as a composite and then immediately characterises it:

```lean
@[simp]
theorem yonedaPairing_map (P Q) (α : P ⟶ Q) (β : (yonedaPairing C).obj P) :
    (yonedaPairing C).map α β = yoneda.map α.1.unop ≫ β ≫ α.2 := rfl
```

so downstream code uses the lemma and never unfolds the definition. Our composite admits exactly
the same treatment — the lemma below is `rfl`.
-/

/-- Characterisation of `yonedaPairingComposite` on 1-morphisms; the bicategorical analogue of
Mathlib's `yonedaPairing_map`.

**Note the bracketing.** This is `(postcomp₂ f ≫ η) ≫ f.2`, whereas `Basic.lean`'s hand-rolled
`yonedaPairing` uses `postcomp₂ f ≫ (η ≫ f.2)`. In a 1-category these coincide (composition is
strictly associative, which is why Mathlib's version can be stated either way); in a bicategory
they differ by an associator. **This single bracketing choice is the entire reason
`yonedaPairingComposite.map ≠ yonedaPairing.map` definitionally.** -/
@[simp]
theorem yonedaPairingComposite_map {x y : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : x ⟶ y)
    (η : ↑((yonedaPairingComposite (B := B)).obj x)) :
    ((yonedaPairingComposite (B := B)).map f).toFunctor.obj η
      = (Bicategory.postcomp₂ f.1.unop ≫ η) ≫ f.2 := rfl

