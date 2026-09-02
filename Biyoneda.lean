-- General, Yoneda-independent material (all upstream candidates).
-- All sorry-free as of 2026-09-02: `evaluationPseudo`'s last two coherence fields closed, so
-- `yonedaEvaluation` is clean and nothing in this group roots a `sorryAx`.
import Biyoneda.ForMathlib
import Biyoneda.UniverseLift
import Biyoneda.BiEquiv
import Biyoneda.Evaluation
-- General gadgets the development is built on. `Pairing` imports both, so despite the
-- "experimental" label these once carried, everything below depends on them. Both are now
-- sorry-free; `homPseudo` (in Gadgets) closed on 2026-08-30 and took `yonedaPairing` with it.
import Biyoneda.Gadgets
import Biyoneda.TransIntoCats
-- The bicategorical Yoneda development itself, in dependency order.
import Biyoneda.Pairing
import Biyoneda.Forwards
import Biyoneda.BackwardsFunctor
import Biyoneda.BackwardsNaturality
import Biyoneda.Backwards
import Biyoneda.Unit
import Biyoneda.Yoneda
-- The axiom-check regression file for the composite pairing.
import Biyoneda.CompositePairing
