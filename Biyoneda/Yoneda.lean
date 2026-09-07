/-
Copyright (c) 2026 Spencer Woolfson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Spencer Woolfson
-/
module

public import Biyoneda.Unit

/-!
# The bicategorical Yoneda lemma

The headline theorem: `yonedaPairing` and `yonedaEvaluation` are internally equivalent in the
bicategory of pseudofunctors `Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat) ⥤ᵖ Cat`, which unpacks to

  `StrongTrans (yoneda₀ b) F  ≃  F.obj b`

natural in `b` and `F`.
-/

@[expose] public section

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

This is Mathlib's `Bicategory.Equivalence` (notation `≌`), an *adjoint* equivalence: it carries
a `left_triangle` law relating the unit and the counit.  The two round-trip isomorphisms proved
in `Biyoneda/Unit.lean` satisfy no such law on their own, so they are fed to
`Equivalence.mkOfAdjointifyCounit`, which repairs the counit until the triangle holds.

The equivalence is witnessed by:
* `hom` (`yonedaLemmaForwards`): evaluate a strong transformation at the identity morphism.
* `inv` (`yonedaLemmaBackwards`): send an element `s : F.obj b` to the strong transformation
  `(a, f) ↦ (F.map f).obj s`.
* `unit` (`yonedaHomInvId.symm`): `id ≅ forwards ≫ backwards` on the pairing side.  The `.symm`
  is orientation: Mathlib writes the unit as `𝟙 a ≅ hom ≫ inv`, while `yonedaHomInvId` is
  proved in the other direction.
* `counit` (`yonedaInvHomId`): `backwards ≫ forwards ≅ id` on evaluation.
-/
def yonedaLemma : (@yonedaPairing B _) ≌ (@yonedaEvaluation B _)
  := Equivalence.mkOfAdjointifyCounit yonedaHomInvId.symm yonedaInvHomId


end Biyoneda
