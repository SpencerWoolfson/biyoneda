/-
Copyright (c) 2026 Spencer Woolfson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Spencer Woolfson
-/
import Biyoneda.Gadgets
import Biyoneda.Basic

/-!
# `yonedaPairing` as a composite of gadgets

**What this file is.** A comparison between `Biyoneda.Basic.yonedaPairing` (hand-rolled, with a
parked `sorry` in its `mapComp` naturality) and `Bicategory.yonedaPairingComposite`
(`Biyoneda/Gadgets.lean`, built from general gadgets, **fully proven, zero sorries**). It is an
experiment, kept on the `composite-pairing` branch. Nothing else imports it.

## Established (each checked, not assumed)

* **`yonedaPairingComposite` typechecks**, at exactly the type `Biyoneda.Basic` uses —
  `Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v}) ⥤ᵖ Cat.{max u (max v w), max u (max v w)}` — and is
  **`sorryAx`-free** (`#print axioms` below).
* **`.obj` and `.map` agree definitionally** with `Basic`'s hand-rolled `yonedaPairing` — see
  `yonedaPairingComposite_obj` / `_map` below, both `rfl`.

## Attempted and reverted: replacing `Basic.yonedaPairing` with this composite

Since `.obj`/`.map` are `rfl`-equal and the composite is `sorryAx`-free, the natural next step is
`Basic.yonedaPairing := Bicategory.yonedaPairingComposite`, which would retire `Basic`'s parked
`mapComp` sorry outright. **This was tried and reverted** — the alias trap here is much larger
than the `yonedaEvaluation'` precedent (`notes/level2_refactor.md`), and did not converge in a
reasonable number of iterations. Recorded honestly so the attempt is not repeated blindly:

* **The composite is many layers deeper than a simple alias.** `yonedaEvaluation'` was replaced
  by one extra layer (`evaluationPseudo (C := Bᵒᵖ)`); `yonedaPairingComposite` goes through
  `Pseudofunctor.comp` → `.prod`/`.op` → `homPseudo` → `prelax` → `mkOfHomFunctors` →
  `Functor.uncurry`. Roughly 15 downstream declarations in `Basic.lean` broke when the swap was
  made (found by mapping error lines back to their owning declaration), each because a `dsimp`/
  `simp only` unfold list that used to reach the hand-rolled term's shape at reducible
  transparency no longer does — the composite's intermediate terms (e.g.
  `((yoneda.op.prod (Pseudofunctor.id K)).obj a).2` instead of the collapsed `a.2`) are defeq to
  the old shape but not *syntactically* the same, and `dsimp`/`rw`/`simp only` match syntactically.
* **Per-site retyping fixes work, but they do not compose cleanly.** Restating a lemma's `Z`
  parameter with an explicit unfolded type (`↑(Pseudofunctor.StrongTrans (yoneda₀ …) a.2)` instead
  of `↑(yonedaPairing.obj a)`) fixed the sites that used it as an *input* — but the SAME retyping
  then broke a *different* site (a bridge lemma for `mapId`'s point-level component), because
  that site's `bicategoricalIso`/`≫` instance resolution picked up a different (still-defeq, but
  differently-presented) `Category` instance once `Z`'s type was written the "clean" way. Point
  fixes at this depth are not independent of each other in an obvious way — the instance-diamond
  documented in `references/instance-diamonds.md` recurs, differently shaped, at multiple layers.
* **What *did* verify cleanly, and is worth keeping**: `.obj`, `.map`, `.map₂` bridge to the old
  hand-rolled shape by `rfl` with no caveats. `.mapId`'s `.hom.toNatTrans.app` component also
  bridges by `rfl` *in isolation* (verified in a standalone probe) — it only broke once folded
  into the same file as the other retyped sites, which is the "does not compose cleanly" finding
  above.

**If this is attempted again**: budget substantially more than a normal alias swap (this is not
one `dsimp`-list fix per site; several sites need genuine re-derivation), and expect to find
*more* than the ~15 sites identified here once each is actually fixed (fixing one can perturb a
sibling, as observed). A narrower, likely cheaper alternative: leave `Basic.yonedaPairing`'s
*shape* untouched and instead transport just the missing `mapComp` naturality proof from
`yonedaPairingComposite.mapComp`'s (proven) naturality via a targeted `congrArg`/cast — this
keeps every downstream site's term shape exactly as it was, at the cost of a more intricate
single proof rather than many small site fixes.
-/

open CategoryTheory Bicategory Bicategory.Opposite Opposite Pseudofunctor StrongTrans Functor

universe u v w

variable {B : Type u} [Bicategory.{w, v} B]

/-- On objects, the composite agrees with the hand-rolled pairing definitionally. -/
theorem yonedaPairingComposite_obj (x : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})) :
    (Bicategory.yonedaPairingComposite (B := B)).obj x = yonedaPairing.obj x := rfl

/-- On 1-morphisms, the composite agrees with the hand-rolled pairing definitionally too. -/
theorem yonedaPairingComposite_map {x y : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : x ⟶ y) :
    (Bicategory.yonedaPairingComposite (B := B)).map f = yonedaPairing.map f := rfl

-- `#print axioms CategoryTheory.Bicategory.yonedaPairingComposite` reports
-- `[propext, Classical.choice, Quot.sound]` — no `sorryAx`. Checked at every build.
#print axioms CategoryTheory.Bicategory.yonedaPairingComposite
