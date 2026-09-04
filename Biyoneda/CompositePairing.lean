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

It covers the rest of the `TransIntoCats` gadget too.  `comp`, `Id`, `toStrongTrans`,
`toModification`, `isoMk` and the bridge lemmas are all proved, and the backwards direction is
now assembled out of them -- but none of them was gated, so any of them could have rotted
silently.  They are asserted here as well.  As of 2026-08-30 the gadget has no sorry left at
all, `ModificationIntoCats.lift` included.

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

-- `homPseudo` and the two named coherence isos it is now built from.  These went clean on
-- 2026-08-30 and are what took the two pairings above clean with them; the gate asserts it so
-- neither can silently rot back.
#print axioms CategoryTheory.Bicategory.homMapIdApp
#print axioms CategoryTheory.Bicategory.homMapCompApp
#print axioms CategoryTheory.Bicategory.homMapIdApp_naturality
#print axioms CategoryTheory.Bicategory.homMapCompApp_naturality
#print axioms CategoryTheory.Bicategory.homMapId
#print axioms CategoryTheory.Bicategory.homMapComp
#print axioms CategoryTheory.Bicategory.homPseudo

-- Must be `sorryAx`-free.  `lift`/`liftDom` came clean when `catPseudoULift` was finished;
-- `appFunctor`, `evalHom` and `evalAt` are the sorry-free half of the evaluation rebuild
-- (2026-08-29).  `evaluationPseudo` used to be excluded here because two of its coherence fields
-- were parked; both closed on 2026-09-02, so it is asserted below with the rest.
#print axioms StrongTransIntoCats.lift
#print axioms StrongTransIntoCats.liftDom
#print axioms CategoryTheory.Pseudofunctor.StrongTrans.appFunctor
#print axioms CategoryTheory.Bicategory.evalHom
#print axioms CategoryTheory.Bicategory.evalAt
#print axioms CategoryTheory.Bicategory.strongTrans_id_app
#print axioms CategoryTheory.Bicategory.evalMapComp_hom
#print axioms CategoryTheory.Bicategory.evalMapComp_inv

-- The rest of the `TransIntoCats` gadget.  Every declaration in it is now proved.
#print axioms StrongTransIntoCats.comp
#print axioms StrongTransIntoCats.Id
#print axioms StrongTransIntoCats.toStrongTrans
#print axioms StrongTransIntoCats.precomposeCounit
#print axioms StrongTransIntoCats.toStrongTransMax
#print axioms StrongTransIntoCats.lift_comp_liftDom_naturality_app
#print axioms StrongTransIntoCats.Id_naturality_app
#print axioms CategoryTheory.Bicategory.ModificationIntoCats.toModification
#print axioms CategoryTheory.Bicategory.ModificationIntoCats.isoMk
#print axioms CategoryTheory.Bicategory.ModificationIntoCats.lift
#print axioms CategoryTheory.Bicategory.lift_modification_lhs
#print axioms CategoryTheory.Bicategory.lift_modification_rhs
#print axioms StrongTransIntoCats.ofStrongTrans
#print axioms CategoryTheory.Bicategory.strongTrans_naturality_id_lhs_app
#print axioms CategoryTheory.Bicategory.strongTrans_naturality_id_rhs_app
#print axioms CategoryTheory.Bicategory.strongTrans_naturality_comp_lhs_app
#print axioms CategoryTheory.Bicategory.strongTrans_naturality_comp_rhs_app

-- The two evaluation unitors, closed 2026-08-30 by writing `Cat`'s unitors and associators into
-- the statement as the identities they definitionally are rather than normalising them away.
#print axioms CategoryTheory.Bicategory.eval_left_unitor
#print axioms CategoryTheory.Bicategory.eval_right_unitor
#print axioms CategoryTheory.Bicategory.eval_left_unitor_rhs_app
#print axioms CategoryTheory.Bicategory.eval_right_unitor_rhs_app
#print axioms CategoryTheory.Bicategory.strongTrans_naturality_id_app
#print axioms CategoryTheory.Bicategory.eval_whisker_left
#print axioms CategoryTheory.Bicategory.eval_whisker_right
#print axioms CategoryTheory.Bicategory.map_comp_cancel
#print axioms CategoryTheory.Bicategory.strongTrans_naturality_comp_inv_app

-- Phase 1 complete (2026-09-02): `evaluationPseudo`'s last two coherence fields closed, so the
-- evaluation side is clean too.  With the pairing already clean, the project now has NO root of
-- `sorryAx` -- every remaining one is in the assembly layers.
#print axioms CategoryTheory.Bicategory.eval_associator
#print axioms CategoryTheory.Bicategory.eval_associator_rhs_app
#print axioms CategoryTheory.Bicategory.strongTrans_comp_naturality_app
#print axioms CategoryTheory.Bicategory.map_map_comp
#print axioms CategoryTheory.Bicategory.strongTrans_naturality_slide
#print axioms CategoryTheory.Bicategory.evaluationPseudo
#print axioms Biyoneda.yonedaEvaluation'
#print axioms Biyoneda.yonedaEvaluation
#print axioms CategoryTheory.Bicategory.evalMapComp_hom_app
#print axioms CategoryTheory.Bicategory.evalMapComp_inv_app
#print axioms CategoryTheory.Bicategory.strongTrans_naturality_conj
#print axioms CategoryTheory.Bicategory.modification_naturality_conj

-- The backwards component chain, decoupled from `yonedaEvaluation'` and rebuilt on the gadget
-- (2026-08-30).  `backwardsTrans` is the Yoneda element itself, so its cleanliness is the
-- statement that the backward direction's *data* is real, independent of the parked coherence.
#print axioms Biyoneda.backwardsFibreFunctor
#print axioms Biyoneda.backwardsTransData
#print axioms Biyoneda.backwardsTrans
#print axioms Biyoneda.mapComp_assoc_app'

-- The backwards naturality isomorphism, rebuilt on 2026-09-02 (Phase 2).  Every square is now
-- reached by a `rfl` bridge that names the distributed form of each side, so the content lives
-- in `*_core` lemmas stated in the fibre, where the ordinary tactics work.  With these,
-- `BackwardsNaturality.lean` is sorry-free.
#print axioms Biyoneda.backwards_inner_core
#print axioms Biyoneda.backwards_app_core
#print axioms Biyoneda.backwardsNaturalityIsoApp
#print axioms Biyoneda.backwardsNaturalityIsoApp_hom_app
#print axioms Biyoneda.backwards_square_lhs_app
#print axioms Biyoneda.backwards_square_rhs_app
#print axioms Biyoneda.backwards_square_tail_app
#print axioms Biyoneda.backwards_square_core
#print axioms Biyoneda.backwards_naturality_square
#print axioms Biyoneda.backwardsNaturalityIso
#print axioms Biyoneda.backwards_natural_lhs_app
#print axioms Biyoneda.backwards_natural_rhs_app
#print axioms Biyoneda.backwards_natural_core
#print axioms Biyoneda.backwards_naturality_iso_natural

-- The forward direction's three coherence cores, rebuilt on 2026-09-03 (Phase 3).  All three
-- were blocked on the same thing: their goals are not type-correct at `implicit` transparency,
-- so no `rw` or `simp` can fire on them.  `forwards_naturality_id_core` is closed by the padding
-- trick (name the chain's value at the point, identities included); the other two are assembled
-- as terms, with the mathematics factored into `unitor_conj_pad` and the two `rfl` bridges.
#print axioms Biyoneda.unitor_conj_pad
#print axioms Biyoneda.forwards_naturality_naturality_unitor
#print axioms Biyoneda.forwards_naturality_naturality_lhs_app
#print axioms Biyoneda.forwards_naturality_naturality_rhs_app
#print axioms Biyoneda.forwards_naturality_naturality_core
#print axioms Biyoneda.forwards_naturality_id_core

-- Phase 4, 2026-09-03: the assembly layer.  `yonedaLemmaForwardsData` and
-- `yonedaLemmaBackwardsData` are the two `StrongTransIntoCats` records the Yoneda
-- transformations are lifted from.  Their supporting lemmas are clean; the records themselves
-- are still `sorryAx`-dependent through the two `mapComp` obligations, and are asserted as
-- such in `CONTAMINATED_DECLS` -- `yonedaLemmaForwardsData` no longer emits a `sorry`
-- *warning* (its own fields are all proved), so without that assertion the remaining debt
-- would be invisible to the gate.
#print axioms Biyoneda.map_map_comp_dist
#print axioms Biyoneda.backwards_naturality_naturality_core
#print axioms Biyoneda.backwards_nn_lhs_app
#print axioms Biyoneda.backwards_nn_rhs_app
#print axioms Biyoneda.backwards_nn_slide
#print axioms Biyoneda.yonedaPairing_mapId_app
#print axioms Biyoneda.backwards_id_core
#print axioms Biyoneda.backwards_id_lhs_app
#print axioms Biyoneda.backwards_id_rhs_app
#print axioms Biyoneda.yonedaLemmaForwardsData
#print axioms Biyoneda.yonedaLemmaForwards
#print axioms Biyoneda.yonedaLemmaBackwardsData
#print axioms Biyoneda.yonedaLemmaBackwards

-- The composite pairing's own unit and composition constraints, evaluated at a point
-- (`Biyoneda/Pairing.lean`).  `mapId`/`mapComp` are the two projections that do NOT bridge to
-- the hand-rolled spelling by `rfl`, so these are the only places in the development where the
-- composite had to be computed rather than re-spelled.  Both come out as pure structural data:
-- a right unitor and an associator, transported.
#print axioms Biyoneda.yonedaPairing_mapId_app
#print axioms Biyoneda.yonedaPairing_mapComp_app
