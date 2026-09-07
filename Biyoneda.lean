module

-- General, Yoneda-independent material (all upstream candidates).
-- All sorry-free as of 2026-09-02: `evaluationPseudo`'s last two coherence fields closed, so
-- `yonedaEvaluation` is clean and nothing in this group roots a `sorryAx`.
public import Biyoneda.ForMathlib
public import Biyoneda.UniverseLift
public import Biyoneda.StrongTransLemmas
public import Biyoneda.Evaluation
-- General gadgets the development is built on. `Pairing` imports both, so despite the
-- "experimental" label these once carried, everything below depends on them. Both are now
-- sorry-free; `homPseudo` (in Gadgets) closed on 2026-08-30 and took `yonedaPairing` with it.
public import Biyoneda.Gadgets
public import Biyoneda.TransIntoCats
-- The bicategorical Yoneda development itself, in dependency order.
public import Biyoneda.Pairing
public import Biyoneda.Forwards
public import Biyoneda.BackwardsFunctor
public import Biyoneda.BackwardsNaturality
public import Biyoneda.Backwards
public import Biyoneda.Unit
public import Biyoneda.Yoneda
-- The axiom-check regression file for the composite pairing.
public import Biyoneda.CompositePairing
