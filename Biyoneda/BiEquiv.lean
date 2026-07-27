/-
Copyright (c) 2026 Spencer Woolfson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Spencer Woolfson
-/
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic

/-!
# Internal equivalences in a bicategory, without the triangle law

An object-level notion of equivalence inside a bicategory: two 1-morphisms together with
2-isomorphisms `map ≫ inv ≅ 𝟙` and `inv ≫ map ≅ 𝟙`, and **no** triangle identity.

## Relationship to `CategoryTheory.Bicategory.Equivalence`

Mathlib already has `Bicategory.Equivalence` (notation `≌`, in
`Mathlib/CategoryTheory/Bicategory/Adjunction/Basic.lean`). It is *not* the same notion: it is an
**adjoint** equivalence, carrying an extra `left_triangle` field relating the unit and counit.
It also orients the unit the other way (`unit : 𝟙 a ≅ hom ≫ inv`, where `BiEquiv` has
`homInvId : map ≫ inv ≅ 𝟙 x`).

`BiEquiv` is the weaker, un-adjointed notion, which is what you get directly when you construct
an equivalence by exhibiting the two composites as isomorphic to identities — no coherence
between the two isomorphisms is required.

**The two are interchangeable**, because Mathlib provides
`Bicategory.Equivalence.mkOfAdjointifyCounit`, which repairs the counit so that the triangle law
holds. `BiEquiv.toEquivalence` below is that upgrade, and `BiEquiv.ofEquivalence` forgets back.
So a result stated with `BiEquiv` immediately yields the stronger Mathlib statement.

If this were ever upstreamed, the honest thing would be to state results directly as `≌` and drop
`BiEquiv` entirely; it exists here because it is the form the Yoneda construction produces.
-/

open CategoryTheory Bicategory

universe w v u

namespace CategoryTheory.Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

/--
The data of an internal equivalence in a bicategory `B` between objects `x` and `y`.

* `map : x ⟶ y` — the forward 1-morphism.
* `inv : y ⟶ x` — the backward 1-morphism.
* `homInvId : map ≫ inv ≅ 𝟙 x` — a 2-isomorphism witnessing that `inv` is a left inverse
  of `map` up to isomorphism.
* `invHomId : inv ≫ map ≅ 𝟙 y` — a 2-isomorphism witnessing that `inv` is a right inverse
  of `map` up to isomorphism.

This is weaker than an adjoint equivalence (no triangle identity is required), but by
`BiEquiv.toEquivalence` it upgrades to one.
-/
structure BiEquiv (x y : B) where
  /-- The forward 1-morphism. -/
  map : x ⟶ y
  /-- The backward 1-morphism. -/
  inv : y ⟶ x
  /-- `inv` is a left inverse of `map`, up to a 2-isomorphism. -/
  homInvId : map ≫ inv ≅ 𝟙 x
  /-- `inv` is a right inverse of `map`, up to a 2-isomorphism. -/
  invHomId : inv ≫ map ≅ 𝟙 y

namespace BiEquiv

variable {x y z : B}

/-- The identity 1-morphism is an equivalence. -/
@[simps]
def refl (x : B) : BiEquiv x x where
  map := 𝟙 x
  inv := 𝟙 x
  homInvId := λ_ (𝟙 x)
  invHomId := λ_ (𝟙 x)

instance : Inhabited (BiEquiv x x) := ⟨refl x⟩

/-- An equivalence read backwards: swap the two 1-morphisms and the two witnesses. -/
@[simps]
def symm (e : BiEquiv x y) : BiEquiv y x where
  map := e.inv
  inv := e.map
  homInvId := e.invHomId
  invHomId := e.homInvId

@[simp]
theorem symm_symm (e : BiEquiv x y) : e.symm.symm = e := rfl

/-- Upgrade to Mathlib's *adjoint* equivalence `x ≌ y`.

The witnesses of a `BiEquiv` need not satisfy the triangle law, but
`Bicategory.Equivalence.mkOfAdjointifyCounit` repairs the counit so that it does. Note the
`.symm`: Mathlib orients the unit as `𝟙 x ≅ map ≫ inv`. -/
def toEquivalence (e : BiEquiv x y) : Bicategory.Equivalence x y :=
  Bicategory.Equivalence.mkOfAdjointifyCounit e.homInvId.symm e.invHomId

/-- Forget the triangle law of a Mathlib adjoint equivalence. -/
@[simps]
def ofEquivalence (e : Bicategory.Equivalence x y) : BiEquiv x y where
  map := e.hom
  inv := e.inv
  homInvId := e.unit.symm
  invHomId := e.counit

@[simp]
theorem ofEquivalence_toEquivalence_map (e : BiEquiv x y) :
    (ofEquivalence e.toEquivalence).map = e.map := rfl

@[simp]
theorem ofEquivalence_toEquivalence_inv (e : BiEquiv x y) :
    (ofEquivalence e.toEquivalence).inv = e.inv := rfl

/-- Equivalences compose.

TODO. `map := e.map ≫ f.map`, `inv := f.inv ≫ e.inv`; the two witnesses are the usual pastings,
`(e.map ≫ f.map) ≫ (f.inv ≫ e.inv) ≅ 𝟙` obtained by re-associating, cancelling `f.homInvId` in
the middle, then `e.homInvId`. The `bicategory` tactic should handle the re-association; the
cancellations are `Iso` composition. -/
def trans (e : BiEquiv x y) (f : BiEquiv y z) : BiEquiv x z := sorry

end BiEquiv

end CategoryTheory.Bicategory
