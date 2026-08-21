/-
Copyright (c) 2026 Spencer Woolfson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Spencer Woolfson
-/
import Biyoneda.Gadgets
import Biyoneda.Basic

/-!
# Regression check: the load-bearing declarations are `sorryAx`-free

`Biyoneda.Basic.yonedaPairing` is defined as `Bicategory.yonedaPairingComposite`, so its five
`Pseudofunctor` coherence laws are inherited from the gadget layer (`Biyoneda/Gadgets.lean`)
rather than proved by hand.

That inheritance is the load-bearing property of the whole development: it is what makes the
pairing's coherence real rather than discharged by `sorry_if_sorry`. This file exists solely to
assert it at every build. A green build is not evidence on its own — a coherence field can be
silently closed by an autoparam riding on a `sorry` elsewhere — so the axiom list is checked
directly, and the build output records it.

The same argument now covers `CatLiftStrongTransData.lift` and `.liftDom`: both directions of the
Yoneda equivalence are assembled through them, so a `sorry` reaching either would be inherited
by everything downstream while each individual definition still looked clean.

`scripts/verify-build.sh` gates on these four; keep the two lists in step.
-/

open CategoryTheory Bicategory

universe u v w

variable {B : Type u} [Bicategory.{w, v} B]

-- All four must report `[propext, Classical.choice, Quot.sound]` with no `sorryAx`.
#print axioms CategoryTheory.Bicategory.yonedaPairingComposite
#print axioms yonedaPairing
#print axioms CatLiftStrongTransData.lift
#print axioms CatLiftStrongTransDomData.lift
