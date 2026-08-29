/-
Copyright (c) 2026 Spencer Woolfson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Spencer Woolfson
-/
import Biyoneda.Gadgets
import Biyoneda.Yoneda

/-!
# Regression check: the load-bearing declarations are `sorryAx`-free

`Biyoneda.Pairing.yonedaPairing` is defined as `Bicategory.yonedaPairingComposite`, so its five
`Pseudofunctor` coherence laws are inherited from the gadget layer (`Biyoneda/Gadgets.lean`)
rather than proved by hand.

That inheritance is the load-bearing property of the whole development: it is what makes the
pairing's coherence real rather than discharged by `sorry_if_sorry`. This file exists solely to
assert it at every build. A green build is not evidence on its own — a coherence field can be
silently closed by an autoparam riding on a `sorry` elsewhere — so the axiom list is checked
directly, and the build output records it.

The same argument now covers `StrongTransIntoCats.lift` and `.liftDom`: both directions of the
Yoneda equivalence are assembled through them, so a `sorry` reaching either would be inherited
by everything downstream while each individual definition still looked clean.

`scripts/verify-build.sh` gates on all of these; keep the two lists in step.
-/

open CategoryTheory Bicategory Biyoneda

universe u v w

variable {B : Type u} [Bicategory.{w, v} B]

-- Two lists, matching `CLEAN_DECLS` / `CONTAMINATED_DECLS` in `scripts/verify-build.sh`.
--
-- Known-contaminated: these still ride on `homPseudo`'s parked coherence fields.
#print axioms CategoryTheory.Bicategory.yonedaPairingComposite
#print axioms yonedaPairing

-- Must be `sorryAx`-free.  `lift`/`liftDom` came clean when `catPseudoULift` was finished;
-- `appFunctor`, `evalHom` and `evalAt` are the sorry-free half of the evaluation rebuild
-- (2026-08-29).  Note `evaluationPseudo` itself is deliberately NOT here: its five coherence
-- fields are still parked, so it -- and every `rfl` bridge stated about it -- is contaminated
-- by construction until Phase 2 lands.
#print axioms StrongTransIntoCats.lift
#print axioms StrongTransIntoCats.liftDom
#print axioms CategoryTheory.Pseudofunctor.StrongTrans.appFunctor
#print axioms CategoryTheory.Bicategory.evalHom
#print axioms CategoryTheory.Bicategory.evalAt
