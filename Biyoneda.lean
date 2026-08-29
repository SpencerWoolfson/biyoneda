-- General, Yoneda-independent material (all upstream candidates).
-- NOTE: no longer sorry-free. `evaluationPseudo` carries five parked coherence fields as of
-- the Mathlib v4.33 bump and the diagonal switch; see README "Status".
import Biyoneda.ForMathlib
import Biyoneda.UniverseLift
import Biyoneda.BiEquiv
import Biyoneda.Evaluation
-- The bicategorical Yoneda development itself, in dependency order.
import Biyoneda.Pairing
import Biyoneda.Forwards
import Biyoneda.BackwardsFunctor
import Biyoneda.BackwardsNaturality
import Biyoneda.Backwards
import Biyoneda.Unit
import Biyoneda.Yoneda
-- Gadgets for rebuilding `yonedaPairing` as a composite, and that composite.
-- Experimental; nothing above depends on them.
import Biyoneda.Gadgets
import Biyoneda.TransIntoCats
import Biyoneda.CompositePairing
