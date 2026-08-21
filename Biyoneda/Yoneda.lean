/-
Copyright (c) 2026 Spencer Woolfson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Spencer Woolfson
-/
import Biyoneda.Unit

/-!
# The bicategorical Yoneda lemma

The headline theorem: `yonedaPairing` and `yonedaEvaluation` are internally equivalent in the
bicategory of pseudofunctors `Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat) ⥤ᵖ Cat`, which unpacks to

  `StrongTrans (yoneda₀ b) F  ≃  F.obj b`

natural in `b` and `F`.
-/

namespace Biyoneda

open CategoryTheory Bicategory Bicategory.Opposite Opposite Pseudofunctor StrongTrans Functor
open scoped Pseudofunctor.StrongTrans

universe u v w v₁ v₂ u₁ u₂

attribute [local instance] uliftCategory


variable {B : Type u} [Bicategory.{w, v} B]

universe w₁

/--
The *bicategorical Yoneda lemma*: an internal equivalence in the bicategory of pseudofunctors

  `yonedaPairing  ≃  yonedaEvaluation`

which unpacks to the natural equivalence of categories

  `StrongTrans (yoneda₀ b) F  ≃  F.obj b`

for all `b : Bᵒᵖ` and `F : Bᵒᵖ ⥤ᵖ Cat`.

The equivalence is witnessed by:
* `map` (`yonedaLemmaForwards`): evaluate a strong transformation at the identity morphism.
* `inv` (`yonedaLemmaBackwards`): send an element `s : F.obj b` to the strong transformation
  `(a, f) ↦ (F.map f).obj s`.
* `homInvId` (`yonedaHomInvId`): the unit iso, `backwards ∘ forwards ≅ id` on the pairing side.
* `invHomId` (`yonedaInvHomId`): the counit iso, `forwards ∘ backwards ≅ id` on evaluation.
-/
def yonedaLemma : BiEquiv (@yonedaPairing B _) (@yonedaEvaluation B _) where
  map := yonedaLemmaForwards
  inv := yonedaLemmaBackwards
  homInvId := yonedaHomInvId
  invHomId := yonedaInvHomId

end Biyoneda
