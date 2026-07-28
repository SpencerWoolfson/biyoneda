/-
Copyright (c) 2026 Spencer Woolfson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Spencer Woolfson
-/
import Biyoneda.Gadgets
import Biyoneda.Basic

/-!
# `yonedaPairing` as a composite of gadgets

**What this file is.** An alternative definition of the Yoneda pairing, assembled from the
general gadgets in `Biyoneda.Gadgets` instead of written out by hand as in `Biyoneda.Basic`.
It is an experiment, kept on the `composite-pairing` branch. Nothing else imports it.

**Status: `yonedaPairingComposite` is `sorryAx`-free** — see `#print axioms` below, which the
build itself checks (not just a claim in this comment). All three gadgets it is built from
(`Pseudofunctor.prod`, `Pseudofunctor.op`, `homPseudo`) are complete; see `Biyoneda.Gadgets`.

**Why.** Mathlib's 1-categorical Yoneda defines the pairing as a one-line composite, so
functoriality is inherited rather than proved:

```lean
def yonedaPairing : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁) ⥤ Type max u₁ v₁ :=
  Functor.prod yoneda.op (𝟭 _) ⋙ Functor.hom (Cᵒᵖ ⥤ Type v₁)
```

`Biyoneda.Basic` instead hand-rolls `yonedaPairing`, writing out every coherence field, one of
which is still `sorry`-ed. This file shows the composite works and closes that gap independently.

With `K := Bᵒᵖ ⥤ᵖ Cat` the functor bicategory, the composite is

```
  Bᵒᵖ × K  --(yoneda.op).prod (id K)-->  Kᵒᵖ × K  --homPseudo K-->  Cat
```

## Established (each checked, not assumed)

* **It typechecks**, at exactly the type `Biyoneda.Basic` uses —
  `Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v}) ⥤ᵖ Cat.{max u (max v w), max u (max v w)}`.
* **No universe lift is needed.** The initial expectation was that `catPseudoULift` would have to
  be inserted, mirroring `yonedaEvaluation`. It does not: the universes line up on their own.
* **`homPseudo` works at the heavy instance.** Here it is applied to `K`, whose hom-categories are
  `StrongTrans` with modifications, so `precomp`/`postcomp` are whiskering of strong
  transformations. That was the main feasibility risk and it went through.
* **`.obj` and `.map` BOTH agree definitionally** with the hand-rolled `yonedaPairing` — see
  `yonedaPairingComposite_obj` / `_map` below, both `rfl`. This was not always true: an earlier
  version of `homPseudo` composed in the other bracketing order and only `.obj` matched. Once
  `Biyoneda.Gadgets`'s `homPseudo` was reshaped to match Mathlib's associativity convention
  (composing postcompose-then-precompose), `.map` started matching too, with no extra work here.
* **`yonedaPairingComposite` is `sorryAx`-free** — `homPseudo`'s one open obligation (its
  `mapComp` naturality square) is now proved; see `Biyoneda.Gadgets` for the recipe (descend with
  `Cat.Hom₂.ext_app`, retype past the `Cat.of` coercion with `change`, then `bicategory`). This
  was gated for a while on exactly that square; closing it is what makes the axiom check below go
  from `sorryAx` to the standard three.

## Next: replacing `Basic`'s `yonedaPairing` with this

Not yet done in this file. Since `.obj` and `.map` are already `rfl`-equal to the original, the
replacement should be safer than a typical alias swap — but still budget for the **alias trap**:
every `simp`/`dsimp` unfold list naming `yonedaPairing` will stop one delta short once it is
redefined, and downstream ordered `erw` chains can then fail in confusing, distant places. `grep`
for `yonedaPairing` inside `simp`/`dsimp`/`unfold` brackets *first*. This exact failure cost
several build cycles when `yonedaEvaluation'` was aliased — see `notes/level2_refactor.md`.

Also untested: whether replacing `yonedaPairing` makes `Basic`'s other five sorries any easier
to close. It retires one sorry outright (the `mapComp` naturality one) but the other five are in
unrelated obligations (`naturality_id`/`naturality_comp` for both directions, and the unit/counit
isos) that this composite does not touch.
-/

open CategoryTheory Bicategory Bicategory.Opposite Opposite Pseudofunctor StrongTrans Functor

universe w v u

namespace CategoryTheory.Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

/-- The functor bicategory `Bᵒᵖ ⥤ᵖ Cat` that the pairing is a hom of. -/
abbrev PairingTarget (B : Type u) [Bicategory.{w, v} B] := Bᵒᵖ ⥤ᵖ Cat.{w, v}

/-- The Yoneda pairing, built as a composite of general gadgets rather than by hand.

Compare `Biyoneda.Basic.yonedaPairing`, which spells out every coherence field. This version
inherits them from `Pseudofunctor.prod`, `Pseudofunctor.op` and `homPseudo`. -/
def yonedaPairingComposite :
    Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v}) ⥤ᵖ Cat.{max u (max v w), max u (max v w)} :=
  Pseudofunctor.comp
    ((Bicategory.yoneda (B := B)).op.prod (Pseudofunctor.id (PairingTarget B)))
    (homPseudo (PairingTarget B))

/-- On objects, the composite agrees with the hand-rolled pairing definitionally. -/
theorem yonedaPairingComposite_obj (x : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})) :
    (yonedaPairingComposite (B := B)).obj x = yonedaPairing.obj x := rfl

/-- On 1-morphisms, the composite agrees with the hand-rolled pairing definitionally too. -/
theorem yonedaPairingComposite_map {x y : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : x ⟶ y) :
    (yonedaPairingComposite (B := B)).map f = yonedaPairing.map f := rfl

end CategoryTheory.Bicategory

-- `#print axioms CategoryTheory.Bicategory.yonedaPairingComposite` reports
-- `[propext, Classical.choice, Quot.sound]` — no `sorryAx`. Checked at every build, not just
-- once: if any gadget it depends on regains a `sorry`, this line's output changes and is visible
-- in the build log (though it does not fail the build; grep for "sorryAx" if you want a hard
-- gate).
#print axioms CategoryTheory.Bicategory.yonedaPairingComposite
