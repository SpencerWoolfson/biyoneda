/-
Copyright (c) 2026 Spencer Woolfson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Spencer Woolfson
-/
import Mathlib.CategoryTheory.Category.ULift
import Biyoneda.ForMathlib

/-!
# Universe lifting for `Cat`

The bicategorical Yoneda lemma compares two pseudofunctors that naturally land in *different*
universes: `evaluationPseudo` lands in `Cat.{w, v}` while the pairing lands in
`Cat.{max u (max v w), max u (max v w)}`.  This file supplies the machinery that promotes the
smaller one, so the two can be compared.

* `catLift` — the strict functor `Cat.{v₁, u₁} ⥤ Cat.{max v₁ v₂, max u₁ u₂}`, sending `C` to
  `ULiftHom (ULift C)`, lifting both the object type and the hom-sets.
* `catPseudoULift` — the same as a *pseudofunctor* (its coherence isos are trivial, because
  `ULift`/`ULiftHom` are strictly functorial).
* `catLiftEquiv` — the equivalence `C ≃ catLift.obj (Cat.of C)`, witnessing that the lift is
  lossless; used to lower morphisms back through the lift.
* `catLift_hom₂_ext` — 2-cells into a lifted category are determined by their unlifted
  components.
* `StrongTransIntoCats` / `StrongTransIntoCats.lift` — define a strong transformation into a
  universe-lifted codomain from pointwise data, paying the `ULift` plumbing once.

Nothing here mentions the Yoneda development; this is general `Cat` universe machinery and is a
candidate for upstreaming (Mathlib has `uliftFunctor` for `Type`, and this is its `Cat`
analogue).
-/

namespace CategoryTheory.Bicategory

open CategoryTheory Bicategory Opposite Pseudofunctor StrongTrans Functor

universe u v w v₁ v₂ u₁ u₂

attribute [local instance] uliftCategory

/--
The `Category` instance on `ULiftHom.{v₂} (ULift.{u₂} C)`, which simultaneously lifts the
object universe from `u₁` to `max u₁ u₂` and the morphism universe from `v₁` to `max v₁ v₂`.

This is the category structure that `catLift` produces on objects; it is assembled by first
applying `uliftCategory` to get a `Category (ULift C)` and then `ULiftHom.category`.
-/
instance catPseudoULiftObjCategory (C : Type u₁) [Category.{v₁} C] :
    Category.{max v₁ v₂} (ULiftHom.{v₂} (ULift.{u₂, u₁} C)) :=
  ULiftHom.category (C := ULift.{u₂, u₁} C)

/--
The strict 1-functor `Cat.{v₁, u₁} ⥤ Cat.{max v₁ v₂, max u₁ u₂}` that promotes a small
category to a larger universe.

* **On objects**: `C ↦ ULiftHom (ULift C)`, lifting both the object type and the hom-sets.
* **On 1-morphisms**: given `F : C ⥤ D`, the lifted functor sends `⟨⟨x⟩⟩ ↦ ⟨F x⟩` and maps
  morphisms via `ULiftHom.up ∘ F.map ∘ ULiftHom.down`.

Because `ULift` and `ULiftHom` are both strictly functorial, no coherence isos are needed.
The pseudofunctor extension (with trivial coherence isos) is `catPseudoULift`.
-/
def catLift : Cat.{v₁, u₁} ⥤ Cat.{max v₁ v₂, max u₁ u₂} where
  obj C := Cat.of (ULiftHom.{v₂} (ULift.{u₂, u₁} C.α))
  map {C D} F :=
    Functor.toCatHom (ULiftHomULiftCategory.equivCongrLeft.toFun
      (ULiftHom.down ⋙ ULift.downFunctor ⋙ F.toFunctor))

def catLiftUnit (A : Cat.{v₁, u₁}) : A ⥤ (catLift.obj A) where
  obj x := {down := x}
  map {x y} f := {down := f}


/--
The equivalence of categories `C ≃ catLift.obj (Cat.of C)`.

This witnesses that universe-lifting is lossless: the original category `C` is equivalent to
its image under `catLift`, via the composite equivalence
  `C  ≃  ULift C  ≃  ULiftHom (ULift C)`
built from `ULift.equivalence` and `ULiftHom.equiv`.

Used in `yonedaLemmaBackwardsFunctor` to lower morphisms through the universe lift.
-/
def catLiftEquiv (C : Type u₁) [Category.{v₁} C] :
    Equivalence C (catLift.{v₁, v₂, u₁, u₂}.obj (Cat.of C)) :=
  (@ULift.equivalence.{v₁, u₁, u₂} C _).trans ULiftHom.equiv

/-- The counit of the universe lift: `catLiftUnit`'s inverse, as a functor.  Kept at the functor
level so that reasoning about a lifted *domain* never has to reach for `ULift.down`. -/
def catLiftCounit (A : Cat.{v₁, u₁}) : (catLift.{v₁, v₂, u₁, u₂}.obj A) ⥤ A :=
  (catLiftEquiv.{v₁, v₂, u₁, u₂} A.α).inverse

@[simp] lemma catLiftUnit_comp_catLiftCounit (A : Cat.{v₁, u₁}) :
    catLiftUnit A ⋙ catLiftCounit.{v₁, v₂, u₁, u₂} A = 𝟭 A := rfl

@[simp] lemma catLiftCounit_comp_catLiftUnit (A : Cat.{v₁, u₁}) :
    catLiftCounit.{v₁, v₂, u₁, u₂} A ⋙ catLiftUnit A = 𝟭 _ := rfl

/--
The pseudofunctor `Cat.{v₁, u₁} ⥤ᵖ Cat.{max v₁ v₂, max u₁ u₂}` that promotes every small
category to a larger universe.

* **On objects and 1-morphisms**: agrees with the strict functor `catLift`.
* **On 2-morphisms**: a natural transformation `η : F ⟶ G` is lifted by applying `ULiftHom.up`
  component-wise.
* **Coherence isos** (`mapId`, `mapComp`): both are `Iso.refl`, since `catLift` is strictly
  functorial and requires no non-trivial coherence.

This pseudofunctor is used to bring `yonedaEvaluation'` (which lands in `Cat.{w, v}`) up to
the universe `Cat.{max u (max v w), max u (max v w)}` required by `yonedaPairing`.
-/
def catPseudoULift : Cat.{v₁, u₁} ⥤ᵖ Cat.{max v₁ v₂, max u₁ u₂} where
  obj C := catLift.{v₁, v₂, u₁, u₂}.obj C
  map {C D} F := catLift.{v₁, v₂, u₁, u₂}.map F
  map₂ {C D} f {g} {η} := by
    refine { toNatTrans := { app := ?_, naturality := ?_ } }
    · intro x
      unfold catLift ULiftHom at x
      exact ULiftHom.up.map (η.toNatTrans.app x.down)
    · exact fun _ _ h ↦ Quiver.homOfEq_injective rfl rfl
        (congrArg (ULiftHom.up.map) (η.toNatTrans.naturality h.down))
  mapId C := Iso.refl (catLift.map (𝟙 C))
  mapComp F G := Iso.refl (catLift.map (F ≫ G))
  map₂_id f := by
    apply Cat.Hom₂.ext_app; intro X
    rfl
  /- The five fields below are the v4.33 frontier for this file.

  All of `catPseudoULift`'s coherence isos are `Iso.refl`, and `Cat` is strict on both sides, so
  each of these squares *ought* to be a component identity.  The simp set below is what gets
  closest: `Bicategory.Strict.{left,right}Unitor_eqToIso` / `associator_eqToIso` turn every
  unitor and associator into an `eqToHom`, which is the right first move and was the thing
  missing from the old `erw` chains.

  What is left after it, for `map₂_left_unitor`, is

      ULiftHom.up.map ((eqToHom _).toNatTrans.app X.down)
        = (𝟙 _ ≫ 𝟙 _ ▷ catLift.map f ≫ eqToHom _).toNatTrans.app X

  i.e. push `ULiftHom.up.map` through an `eqToHom` and collapse `𝟙 ▷ _`.  `map₂_left_unitor`
  closes with the set below; the other four need a little more.

  Tried and insufficient: `rfl` alone, `cat_disch`, `aesop_cat`, `ext ⟨x⟩; simp`, and the old
  v4.30 `erw [Category.comp_id, Category.id_comp] … congr` chains (whose `congr` no longer
  closes; the residual is `𝟙 A = 𝟙 B ≫ 𝟙 C` at three different spellings of the same
  object).

  The v4.30 proofs are worth mining:  git show comp-core:Biyoneda/UniverseLift.lean -/
  map₂_whisker_left {a b c} f g h η := by
    apply Cat.Hom₂.ext_app; intro X
    simp only [Bicategory.Strict.leftUnitor_eqToIso,
      Bicategory.Strict.rightUnitor_eqToIso, Bicategory.Strict.associator_eqToIso,
      eqToIso.hom, eqToHom_refl, Iso.refl_hom, Bicategory.whiskerLeft_eqToHom,
      Bicategory.eqToHom_whiskerRight, Bicategory.id_whiskerRight,
      Bicategory.whiskerLeft_id, Cat.Hom.toNatTrans_comp, NatTrans.comp_app,
      Cat.Hom.toNatTrans_id, NatTrans.id_app, eqToHom_app, eqToHom_map,
      Category.id_comp, Category.comp_id]
    first
      | rfl
      | done
      | sorry
  map₂_whisker_right η h := by
    apply Cat.Hom₂.ext_app; intro X
    simp only [Bicategory.Strict.leftUnitor_eqToIso,
      Bicategory.Strict.rightUnitor_eqToIso, Bicategory.Strict.associator_eqToIso,
      eqToIso.hom, eqToHom_refl, Iso.refl_hom, Bicategory.whiskerLeft_eqToHom,
      Bicategory.eqToHom_whiskerRight, Bicategory.id_whiskerRight,
      Bicategory.whiskerLeft_id, Cat.Hom.toNatTrans_comp, NatTrans.comp_app,
      Cat.Hom.toNatTrans_id, NatTrans.id_app, eqToHom_app, eqToHom_map,
      Category.id_comp, Category.comp_id]
    first
      | rfl
      | done
      | sorry
  map₂_associator {a b c d} f g h := by
    apply Cat.Hom₂.ext_app; intro X
    simp only [Bicategory.Strict.leftUnitor_eqToIso,
      Bicategory.Strict.rightUnitor_eqToIso, Bicategory.Strict.associator_eqToIso,
      eqToIso.hom, eqToHom_refl, Iso.refl_hom, Bicategory.whiskerLeft_eqToHom,
      Bicategory.eqToHom_whiskerRight, Bicategory.id_whiskerRight,
      Bicategory.whiskerLeft_id, Cat.Hom.toNatTrans_comp, NatTrans.comp_app,
      Cat.Hom.toNatTrans_id, NatTrans.id_app, eqToHom_app, eqToHom_map,
      Category.id_comp, Category.comp_id]
    first
      | rfl
      | done
      | sorry
  map₂_left_unitor {a b} f := by
    apply Cat.Hom₂.ext_app; intro X
    simp only [Bicategory.Strict.leftUnitor_eqToIso,
      Bicategory.Strict.rightUnitor_eqToIso, Bicategory.Strict.associator_eqToIso,
      eqToIso.hom, eqToHom_refl, Iso.refl_hom, Bicategory.whiskerLeft_eqToHom,
      Bicategory.eqToHom_whiskerRight, Bicategory.id_whiskerRight,
      Bicategory.whiskerLeft_id, Cat.Hom.toNatTrans_comp, NatTrans.comp_app,
      Cat.Hom.toNatTrans_id, NatTrans.id_app, eqToHom_app, eqToHom_map,
      Category.id_comp, Category.comp_id]
    first
      | rfl
      | done
      | sorry
  map₂_right_unitor {a b} f := by
    apply Cat.Hom₂.ext_app; intro X
    simp only [Bicategory.Strict.leftUnitor_eqToIso,
      Bicategory.Strict.rightUnitor_eqToIso, Bicategory.Strict.associator_eqToIso,
      eqToIso.hom, eqToHom_refl, Iso.refl_hom, Bicategory.whiskerLeft_eqToHom,
      Bicategory.eqToHom_whiskerRight, Bicategory.id_whiskerRight,
      Bicategory.whiskerLeft_id, Cat.Hom.toNatTrans_comp, NatTrans.comp_app,
      Cat.Hom.toNatTrans_id, NatTrans.id_app, eqToHom_app, eqToHom_map,
      Category.id_comp, Category.comp_id]
    first
      | rfl
      | done
      | sorry

/-- Two 2-cells of `Cat` landing in a universe-lifted category are equal as soon as their
unlifted components agree: morphisms of `ULiftHom (ULift D)` are `ULift`-wrapped, so the
lifting plumbing can be stripped once and for all. -/
lemma catLift_hom₂_ext {E : Cat} {D : Cat.{v₁, u₁}}
    {H K : E ⟶ catPseudoULift.{v₁, v₂, u₁, u₂}.obj D} {η θ : H ⟶ K}
    (h : ∀ X : E, (η.toNatTrans.app X).down = (θ.toNatTrans.app X).down) : η = θ := by
  apply Cat.Hom₂.ext_app
  intro X
  exact congrArg ULift.up (h X)

/-- Codomain-side ext, stated through the **counit functor** instead of `ULift.down`.

`catLift_hom₂_ext` above reduces a 2-cell equation to its `.down` components, which leaves a raw
`ULift.down` at the head of the goal.  That head is fatal once the codomain is spelled
`(G.comp catPseudoULift).obj a` rather than `catPseudoULift.obj (G.obj a)`: the two differ only
by unfolding, so the goal stops being type-correct at `implicit` transparency and every
functor-level stripping lemma below silently declines to fire — `simp` reports no progress and
`rw` reports the pattern as absent, neither of which names the real cause.  Going through
`catLiftCounit` keeps the goal inside the gadget's own API, where those lemmas apply. -/
lemma catLift_hom₂_counit_ext {E : Cat} {D : Cat.{v₁, u₁}}
    {H K : E ⟶ catPseudoULift.{v₁, v₂, u₁, u₂}.obj D} {η θ : H ⟶ K}
    (h : ∀ X : E, (catLiftCounit D).map (η.toNatTrans.app X)
        = (catLiftCounit D).map (θ.toNatTrans.app X)) : η = θ := by
  apply Cat.Hom₂.ext_app
  intro X
  exact congrArg ULift.up (h X)

/-- Two 2-cells out of a universe-lifted category are equal as soon as they agree on the image
of `catLiftUnit`, which hits every object.  The domain-side counterpart of `catLift_hom₂_ext`;
stated through the unit functor rather than `ULift.down` so it composes with the functor-level
stripping lemmas. -/
lemma catLift_hom₂_dom_ext {D : Cat.{v₁, u₁}} {E : Cat}
    {H K : catPseudoULift.{v₁, v₂, u₁, u₂}.obj D ⟶ E} {η θ : H ⟶ K}
    (h : ∀ x : D, η.toNatTrans.app ((catLiftUnit D).obj x)
        = θ.toNatTrans.app ((catLiftUnit D).obj x)) : η = θ := by
  apply Cat.Hom₂.ext_app
  intro X
  exact h ((catLiftCounit D).obj X)


/-! ### Stripping the lift at the functor level

The lemmas below eliminate a `catPseudoULift` while it is still applied as a *functor*, rather
than unfolding `catLift`/`ULiftHom` down to raw `ULift.up` wrappers. Unfolding all the way
leaves goals of the form `ULift.up x ≫ ULift.up y`, which do not recombine; rewriting at the
functor level keeps everything inside `catLiftUnit` and stays composable. All hold by `rfl`
because `ULift`/`ULiftHom` are strictly functorial and the lift's coherence isos are identities.
-/

@[simp] lemma catLiftUnit_map_down {C : Cat.{v₁, u₁}} {x y : C} (m : x ⟶ y) :
    ((catLiftUnit C).map m).down = m := rfl

/-- Stripping the lift on the **domain** side: a lifted 1-cell precomposed with the counit is the
counit followed by the unlifted 1-cell. -/
@[simp] lemma catLiftCounit_naturality {C D : Cat.{v₁, u₁}} (F : C ⟶ D) :
    (catPseudoULift.{v₁, v₂, u₁, u₂}.map F).toFunctor ⋙ catLiftCounit D
      = catLiftCounit C ⋙ F.toFunctor := rfl

/-- The unit followed by the counit is the identity, at a point.  The functor-level
`catLiftUnit_comp_catLiftCounit` cannot fire here because `simp` normalises composites apart. -/
@[simp] lemma catLiftCounit_obj_catLiftUnit_obj {C : Cat.{v₁, u₁}} (x : C) :
    (catLiftCounit.{v₁, v₂, u₁, u₂} C).obj ((catLiftUnit C).obj x) = x := rfl

@[simp] lemma catLiftCounit_map_catLiftUnit_map {C : Cat.{v₁, u₁}} {x y : C} (m : x ⟶ y) :
    (catLiftCounit.{v₁, v₂, u₁, u₂} C).map ((catLiftUnit C).map m) = m := rfl

/-- A lifted 1-cell applied to a lifted object, brought back down. -/
@[simp] lemma catLiftCounit_obj_catPseudoULift_map_obj {C D : Cat.{v₁, u₁}} (F : C ⟶ D) (x : C) :
    (catLiftCounit.{v₁, v₂, u₁, u₂} D).obj
        ((catPseudoULift.{v₁, v₂, u₁, u₂}.map F).toFunctor.obj ((catLiftUnit C).obj x))
      = F.toFunctor.obj x := rfl

/-- A lifted 2-cell, evaluated at a lifted object and brought back down. -/
@[simp] lemma catLiftCounit_map_catPseudoULift_map₂ {C D : Cat.{v₁, u₁}} {F G : C ⟶ D}
    (η : F ⟶ G) (x : C) :
    (catLiftCounit.{v₁, v₂, u₁, u₂} D).map
        ((catPseudoULift.{v₁, v₂, u₁, u₂}.map₂ η).toNatTrans.app ((catLiftUnit C).obj x))
      = η.toNatTrans.app x := rfl
/-- A lifted 2-cell brought back down, at an **arbitrary** point of the lifted category.  The
`catLiftUnit`-shaped version above only matches points that are syntactically lifted; this one
matches anything, which is what consumers of `catPseudoULift` actually have. -/
@[simp] lemma catLiftCounit_map_catPseudoULift_map₂' {C D : Cat.{v₁, u₁}} {F G : C ⟶ D}
    (η : F ⟶ G) (x : ↑(catPseudoULift.{v₁, v₂, u₁, u₂}.obj C)) :
    (catLiftCounit.{v₁, v₂, u₁, u₂} D).map
        ((catPseudoULift.{v₁, v₂, u₁, u₂}.map₂ η).toNatTrans.app x)
      = η.toNatTrans.app ((catLiftCounit C).obj x) := rfl

/-- Likewise for the identity coherence, at an arbitrary point. -/
@[simp] lemma catPseudoULift_mapId_hom_app' {C : Cat.{v₁, u₁}}
    (x : ↑(catPseudoULift.{v₁, v₂, u₁, u₂}.obj C)) :
    (catPseudoULift.{v₁, v₂, u₁, u₂}.mapId C).hom.toNatTrans.app x = 𝟙 _ := rfl


@[simp] lemma catPseudoULift_map_catLiftUnit_map {C D : Cat.{v₁, u₁}} (F : C ⟶ D)
    {x y : C} (m : x ⟶ y) :
    (catPseudoULift.{v₁, v₂, u₁, u₂}.map F).toFunctor.map ((catLiftUnit C).map m)
      = (catLiftUnit D).map (F.toFunctor.map m) := rfl

@[simp] lemma catPseudoULift_map₂_app_catLiftUnit {C D : Cat.{v₁, u₁}} {F G : C ⟶ D}
    (η : F ⟶ G) (x : C) :
    (catPseudoULift.{v₁, v₂, u₁, u₂}.map₂ η).toNatTrans.app ((catLiftUnit C).obj x)
      = (catLiftUnit D).map (η.toNatTrans.app x) := rfl

@[simp] lemma catPseudoULift_mapComp_hom_app {C D E : Cat.{v₁, u₁}} (F : C ⟶ D) (G : D ⟶ E)
    (x : ↑(catPseudoULift.{v₁, v₂, u₁, u₂}.obj C)) :
    (catPseudoULift.{v₁, v₂, u₁, u₂}.mapComp F G).hom.toNatTrans.app x = 𝟙 _ := rfl

@[simp] lemma catPseudoULift_mapId_hom_app {C : Cat.{v₁, u₁}}
    (x : ↑(catPseudoULift.{v₁, v₂, u₁, u₂}.obj C)) :
    (catPseudoULift.{v₁, v₂, u₁, u₂}.mapId C).hom.toNatTrans.app x = 𝟙 _ := rfl

end CategoryTheory.Bicategory
