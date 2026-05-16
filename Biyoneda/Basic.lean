import Mathlib.CategoryTheory.Bicategory.Product
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Bicategory.Yoneda
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.Tactic.CategoryTheory.Bicategory.Basic

/-!
# Bicategorical Yoneda Lemma

This file formalises the Yoneda lemma for bicategories.  Given a bicategory `B` with Yoneda
embedding `yoneda : B ⥤ᵖ Bᵒᵖ ⥤ᵖ Cat` (see `Bicategory.yoneda`), we construct a bicategorical
equivalence

  `StrongTrans (yoneda₀ b) F  ≃  F.obj b`

natural in `b : Bᵒᵖ` and `F : Bᵒᵖ ⥤ᵖ Cat`.

## Main definitions

* `yonedaPairing : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat) ⥤ᵖ Cat` — the pseudofunctor sending `(b, F)` to
  the category of strong transformations `StrongTrans (yoneda₀ b) F`.
* `yonedaEvaluation : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat) ⥤ᵖ Cat` — the pseudofunctor sending `(b, F)`
  to the category `F.obj b`.
* `yonedaLemmaForwards : yonedaPairing ⟶ yonedaEvaluation` — the "evaluate at identity"
  strong transformation, sending `η : yoneda₀ b ⟶ F` to `η.app b (𝟙 b)`.
* `yonedaLemmaBackwards : yonedaEvaluation ⟶ yonedaPairing` — the inverse strong
  transformation, sending `s : F.obj b` to the strong transformation `(a, f) ↦ F.map f s`.
* `yonedaLemma : BiEquiv yonedaPairing yonedaEvaluation` — the Yoneda lemma assembled as
  a `BiEquiv` (an internal equivalence in the bicategory of pseudofunctors).

## Universe notes

`yonedaEvaluation'` lands in `Cat.{w, v}` while `yonedaPairing` lands in
`Cat.{max u (max v w), max u (max v w)}`.  The auxiliary pseudofunctor `CatPseudoULift` is
used to promote `yonedaEvaluation'` to the correct universe level, yielding `yonedaEvaluation`.
-/

open CategoryTheory Bicategory Bicategory.Opposite Opposite Pseudofunctor StrongTrans Functor
open scoped Pseudofunctor.StrongTrans

universe u v w v₁ v₂ u₁ u₂

/--
The `Category` instance on `ULiftHom.{v₂} (ULift.{u₂} C)`, which simultaneously lifts the
object universe from `u₁` to `max u₁ u₂` and the morphism universe from `v₁` to `max v₁ v₂`.

This is the category structure that `CatLift` produces on objects; it is assembled by first
applying `uliftCategory` to get a `Category (ULift C)` and then `ULiftHom.category`.
-/
instance catPseudoULiftObjCategory (C : Type u₁) [Category.{v₁} C] :
    Category.{max v₁ v₂} (ULiftHom.{v₂} (ULift.{u₂, u₁} C)) := by
  letI : Category (ULift.{u₂, u₁} C) := uliftCategory C
  exact ULiftHom.category (C := ULift.{u₂, u₁} C)

/--
The strict 1-functor `Cat.{v₁, u₁} ⥤ Cat.{max v₁ v₂, max u₁ u₂}` that promotes a small
category to a larger universe.

* **On objects**: `C ↦ ULiftHom (ULift C)`, lifting both the object type and the hom-sets.
* **On 1-morphisms**: given `F : C ⥤ D`, the lifted functor sends `⟨⟨x⟩⟩ ↦ ⟨F x⟩` and maps
  morphisms via `ULiftHom.up ∘ F.map ∘ ULiftHom.down`.

Because `ULift` and `ULiftHom` are both strictly functorial, no coherence isos are needed.
The pseudofunctor extension (with trivial coherence isos) is `CatPseudoULift`.
-/
def CatLift : Cat.{v₁, u₁} ⥤ Cat.{max v₁ v₂, max u₁ u₂} where
  obj C := Cat.of (ULiftHom.{v₂} (ULift.{u₂, u₁} C.α))
  map {C D} F := by
    refine Functor.toCatHom ?_
    apply ULiftHomULiftCategory.equivCongrLeft.toFun
    letI : Category (ULift.{u₂, u₁} C) := uliftCategory C
    exact ULiftHom.down ⋙ ULift.downFunctor ⋙ F.toFunctor

/--
The equivalence of categories `C ≃ CatLift.obj (Cat.of C)`.

This witnesses that universe-lifting is lossless: the original category `C` is equivalent to
its image under `CatLift`, via the composite equivalence
  `C  ≃  ULift C  ≃  ULiftHom (ULift C)`
built from `ULift.equivalence` and `ULiftHom.equiv`.

Used in `yonedaLemmaBackwardsFunctor` to lower morphisms through the universe lift.
-/
def CatLiftIso (C : Type u₁) [Category.{v₁} C] :
    Equivalence C (CatLift.{v₁, v₂, u₁, u₂}.obj (Cat.of C)) := by
  let uLiftEquiv := @ULift.equivalence.{v₁, u₁, u₂} C _
  letI : Category (ULift.{u₂, u₁} C) := uliftCategory C
  exact uLiftEquiv.trans ULiftHom.equiv

/--
The pseudofunctor `Cat.{v₁, u₁} ⥤ᵖ Cat.{max v₁ v₂, max u₁ u₂}` that promotes every small
category to a larger universe.

* **On objects and 1-morphisms**: agrees with the strict functor `CatLift`.
* **On 2-morphisms**: a natural transformation `η : F ⟶ G` is lifted by applying `ULiftHom.up`
  component-wise.
* **Coherence isos** (`mapId`, `mapComp`): both are `Iso.refl`, since `CatLift` is strictly
  functorial and requires no non-trivial coherence.

This pseudofunctor is used to bring `yonedaEvaluation'` (which lands in `Cat.{w, v}`) up to
the universe `Cat.{max u (max v w), max u (max v w)}` required by `yonedaPairing`.
-/
def CatPseudoULift : Cat.{v₁, u₁} ⥤ᵖ Cat.{max v₁ v₂, max u₁ u₂} where
  obj C := CatLift.{v₁, v₂, u₁, u₂}.obj C
  map {C D} F := CatLift.{v₁, v₂, u₁, u₂}.map F
  map₂ { C D } f { g } { η } := by
    refine {toNatTrans := {app := ?_, naturality := ?_}}
    · intro x
      unfold CatLift ULiftHom at x
      letI : Category.{v₁, max u₁ u₂} (ULift.{u₂, u₁} ↑D) := uliftCategory ↑D
      exact (ULiftHom.up.map (η.toNatTrans.app x.down))
    · intros X Y h
      rcases X with ⟨X⟩
      rcases Y with ⟨Y⟩
      apply (Quiver.homOfEq_injective rfl rfl (congrArg (ULiftHom.up.map) (η.toNatTrans.naturality h.down)))
  mapId C := Iso.refl (CatLift.map (𝟙 C))
  mapComp F G := Iso.refl (CatLift.map (F ≫ G))
  map₂_id f := by congr
  map₂_whisker_left { a b c } f g h η := by ext x; erw [Category.comp_id, Category.id_comp] ; congr
  map₂_whisker_right η h:= by
    congr
    ext ⟨x⟩
    erw [Category.comp_id, Category.id_comp]
    exact eq_of_comp_right_eq fun {Z} ↦ congrFun rfl
  map₂_associator f g h := by
    ext ⟨x⟩
    erw [Category.comp_id, Category.id_comp]
    sorry
  map₂_left_unitor {a b} f := by
    ext ⟨x⟩
    erw [Category.comp_id]
    sorry
  map₂_right_unitor {a b} f := by
    ext ⟨x⟩
    simp
    sorry

variable {B : Type u} [Bicategory.{w, v} B]

/--
To prove two morphisms `m1 m2 : η ⟶ θ` in the hom-category of strong transformations are
equal, it suffices to show their underlying modifications agree: `m1.as = m2.as`.

In the `Pseudofunctor.StrongTrans` bicategory, a 2-morphism `η ⟶ θ` is a `StrongTrans.Hom`,
a one-field structure wrapping a `Modification`.  This lemma peels off that wrapper.
-/
lemma StrongTrans.Hom.ext {X : Type u₁} {Y : Type u₂}
    [Bicategory.{w₁, v₁} X] [Bicategory.{w₂, v₂} Y]
    {F G : X ⥤ᵖ Y} {η θ : F ⟶ G} {m1 m2 : η ⟶ θ} (h : m1.as = m2.as) : m1 = m2 := by
  cases m1
  cases m2
  congr

/--
The *pairing pseudofunctor* `Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat) ⥤ᵖ Cat`.

This is the left-hand side of the Yoneda equivalence, encoding "strong transformations out of
the Yoneda embedding":

* **On objects**: `(b, F) ↦ StrongTrans (yoneda₀ b) F` — the category whose objects are strong
  transformations `yoneda₀ b ⟶ F` and whose morphisms are modifications between them.
* **On 1-morphisms**: a pair `(f : b' ⟶ b, α : F ⟶ G)` acts on a strong transformation `η`
  by `η ↦ postcomp₂ f ≫ η ≫ α` — precomposing with the Yoneda image of `f` and
  postcomposing with `α`.
* **On 2-morphisms**: a pair `(σ : f ⟶ f', τ : α ⟶ β)` acts by left- and right-whiskering
  the corresponding postcomposing transformations.
-/
def yonedaPairing : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v}) ⥤ᵖ Cat.{max u (max v w), max u (max v w)} where
  obj x := @Cat.of (Pseudofunctor.StrongTrans (yoneda₀ x.fst.unop) x.snd)
    (Pseudofunctor.StrongTrans.homCategory)
  map {x y} f := by
    -- I should figure out why exact will not work and fix that. I think it is an isue with useing ⟶ instead of strongtrans
    let sol := Functor.toCatHom { obj η := Bicategory.postcomp₂ f.1.unop ≫ (η ≫ f.2), map m := StrongTrans.whiskerLeft (Bicategory.postcomp₂ f.1.unop) (StrongTrans.whiskerRight m f.2)}
    dsimp [Quiver.Hom] at sol
    exact sol
  map₂ { x y f g } η := by
    let h1 : postcomp₂ f.1.unop ⟶ postcomp₂ g.1.unop := (postcomposing₂ y.1.unop x.1.unop).map (Hom2.unop2 η.1)
    let h2 : f.2 ⟶ g.2 := η.2
    refine { toNatTrans := { app := ?_, naturality := ?_ } }
    · exact fun a => (h1 ▷ (a ≫ f.2)) ≫ (postcomp₂ g.1.unop) ◁ (a ◁ h2)
    · intros X Y h
      -- apply homCategory.ext
      -- intro b
      -- refine Cat.Hom₂.ext_iff.mpr ?_
      -- ext c
      -- simp [StrongTrans.whiskerLeft,postcomp₂]
      sorry
  mapId x := by
    refine Cat.Hom.isoMk ?_
    refine NatIso.ofComponents ?_ ?_
    · intro X
      let lem1 : postcomp₂ (𝟙 (unop x.1)) ≅ 𝟙 (yoneda₀ (unop x.1)) := by
        sorry
      let lem2 := (lem1 ▷ᵢ (X ≫ 𝟙 x.2))
      refine Iso.trans lem2 ?_
      exact (bicategoricalIso X (𝟙 (yoneda₀ (unop x.1)) ≫ X ≫ 𝟙 x.2)).symm
    · sorry
  mapComp f g := by
    refine Cat.Hom.isoMk ?_
    refine NatIso.ofComponents ?_ ?_
    · sorry
    · sorry
  map₂_id {a b} X := by
    ext ⟨x⟩
    simp
    sorry


/--
The *evaluation pseudofunctor* `Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat) ⥤ᵖ Cat.{w, v}`.

This is the right-hand side of the Yoneda equivalence (before universe promotion):

* **On objects**: `(b, F) ↦ F.obj b` — evaluate the pseudofunctor `F` at the object `b`.
* **On 1-morphisms**: `(f : b' ⟶ b, α : F ⟶ G) ↦ α.app b' ≫ G.map f`, i.e., apply the
  component of the natural transformation `α` at `b'`, then map along `f` using `G`.
* **On 2-morphisms**: `(σ, τ) ↦ (σ.as.app b' ▷ G.map f) ≫ (_ ◁ G.map₂ τ)`.
* **Coherence iso `mapId`**: `F.mapId b`, the identity coherence of `F`.
* **Coherence iso `mapComp`**: built from the associator and `G.mapComp` and `G.naturality`.

Note: this pseudofunctor lands in the smaller universe `Cat.{w, v}`.  Use `yonedaEvaluation`
(which post-composes with `CatPseudoULift`) for the universe-matched version.
-/
def yonedaEvaluation' : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v}) ⥤ᵖ Cat.{w, v} where
  obj x := x.snd.obj x.fst
  map {x y} f := f.2.app x.1 ≫ (y.2.map f.1)
  map₂ { x y f g } η := (η.2.as.app x.1 ▷ y.2.map f.1) ≫ (_ ◁ y.2.map₂ η.1)
  mapId x := (_root_.id (x.2.mapId x.1))
  mapComp {a b c} f g := by
    refine (α_ (f.2.app a.1) (g.2.app a.1) (c.2.map (f.1 ≫ g.1))) ≪≫ ?_ ≪≫ (α_ (f.2.app a.1) (b.2.map f.1) (g.2.app b.1 ≫ c.2.map g.1)).symm
    refine (f.2.app a.1) ◁ᵢ ((g.2.app a.1 ◁ᵢ (c.2.mapComp f.1 g.1)) ≪≫ ?_)
    refine (α_ (g.2.app a.1) (c.2.map f.1) (c.2.map g.1)).symm ≪≫ ?_ ≪≫ (α_ (b.2.map f.1) (g.2.app b.1) (c.2.map g.1))
    exact (g.2.naturality f.1).symm ▷ᵢ (c.2.map g.1)
  map₂_whisker_left {a b c} f { g h } { η }:= by sorry
  map₂_whisker_right := by sorry
  map₂_associator := by sorry
  map₂_left_unitor a := by sorry
  map₂_right_unitor := by sorry

/--
The *evaluation pseudofunctor* at the correct universe level,
`Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat) ⥤ᵖ Cat.{max u (max v w), max u (max v w)}`.

Defined as the composite `yonedaEvaluation' ⋙ CatPseudoULift`, which promotes the smaller
pseudofunctor `yonedaEvaluation'` (landing in `Cat.{w, v}`) to match the universe of
`yonedaPairing`.
-/
def yonedaEvaluation : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v}) ⥤ᵖ Cat.{max u (max v w), max u (max v w)} := by
  refine (Pseudofunctor.comp yonedaEvaluation' CatPseudoULift)

/--
At a fixed pair `x = (b, F)`, the *evaluate-at-identity functor*
`StrongTrans (yoneda₀ b) F ⥤ F.obj b`.

This is the core of the Yoneda equivalence at the level of individual categories:
* **On objects**: a strong transformation `η : yoneda₀ b ⟶ F` maps to
  `η.app b (𝟙 b) : F.obj b` — apply the component at `b`, then evaluate at `𝟙 b`.
* **On morphisms**: a modification `m : η ⟶ θ` maps to
  `m.as.app b (𝟙 b) : η.app b (𝟙 b) ⟶ θ.app b (𝟙 b)`.
-/
@[simp]
def yonedaLemmaForwardsFunctor (x : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat)) : (yonedaPairing.obj x) ⥤ (yonedaEvaluation.obj x) where
  obj pair := by
    fconstructor
    exact (pair.app x.1).toFunctor.obj (𝟙 (unop x.1))
  map {a b} f := by
    fconstructor
    exact (f.as.app x.1).toNatTrans.app (𝟙 (unop x.1))

-- set_option trace.Meta.synthInstance true
/--
The *forward strong transformation* `yonedaPairing ⟶ yonedaEvaluation` for the Yoneda lemma.

At each pair `x = (b, F)`, the component functor is `yonedaLemmaForwardsFunctor x`, which
sends a strong transformation `η : yoneda₀ b ⟶ F` to the element `η.app b (𝟙 b) : F.obj b`.

Mathematically, this is the "evaluate at identity" direction of the equivalence
  `StrongTrans(yoneda₀ b, F)  ≃  F.obj b`.
-/
def yonedaLemmaForwards : StrongTrans (@yonedaPairing B _) (@yonedaEvaluation B _) where
  app x := {toFunctor := yonedaLemmaForwardsFunctor x}
  naturality {a b} f := by
    refine Cat.Hom.isoMk ?_
    refine NatIso.ofComponents ?_ ?_
    · intro X
      dsimp [CatPseudoULift,CatLift,ULiftHomULiftCategory.equivCongrLeft,ULiftHom.objUp,yonedaEvaluation,ULiftHom.objDown]
      -- refine (ULift.upFunctor.mapIso ?_)
      sorry
    · sorry



/--
At a fixed pair `x = (b₀, F)`, an evaluation point `eval : F.obj b₀`, and a component
`a : Bᵒᵖ`, the functor `(unop a ⟶ b₀) ⥤ F.obj a` sending `f ↦ (F.map f).obj eval`.

In terms of `yoneda₀ b₀`, the source category at `a` is the hom-category `(unop a ⟶ b₀)`:
* **On objects**: `f : unop a ⟶ b₀` maps to `(F.map (Quiver.Hom.op f)).obj eval : F.obj a`.
* **On morphisms**: a 2-cell `α : f ⟶ g` (a morphism in `Bᵒᵖ`) maps to
  `(F.map₂ (op2 α)).toNatTrans.app eval`.
* **Functoriality**: follows from `F.map₂_id` and `F.map₂_comp` via `erw` through the
  universe-level coercion introduced by `Cat.of`.

This is the functor underlying the `a`-component of `yonedaLemmaBackwardsFunctorObj`.
-/
@[simp]
def yonedaLemmaBackwardsFunctorObjFunctor (x : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat)) (eval : (yonedaEvaluation.obj x)) (a : Bᵒᵖ) : ↑((yoneda₀ (unop x.1)).obj a) ⥤ ↑(x.2.obj a) where
  obj b := by
    refine (x.2.map (Quiver.Hom.op b)).toFunctor.obj ?_
    rcases eval with ⟨eval⟩
    exact eval
  map { X Y } f := by
    rcases eval with ⟨eval⟩
    exact (x.2.map₂ (op2 f)).toNatTrans.app (eval)
  map_id _ := by cases eval; erw [op2_id, PrelaxFunctor.map₂_id]; rfl
  map_comp _ _ := by cases eval; erw [op2_comp, PrelaxFunctor.map₂_comp]; rfl

/--
At a fixed pair `x = (b₀, F)` and an evaluation point `eval : F.obj b₀`, the strong
transformation `yoneda₀ b₀ ⟶ F` corresponding to `eval` under the Yoneda embedding.

* **Component at `a`**: the functor `yonedaLemmaBackwardsFunctorObjFunctor x eval a`, which
  sends `f : unop a ⟶ b₀` to `(F.map f).obj eval`.
* **Naturality at `f : a ⟶ b`**: an isomorphism built from the associativity coherence
  `F.mapComp`, whose hom component at `X` is `(F.mapComp (op X) f).hom.app eval` and whose
  inv component at `X` is `(F.mapComp (op X) f).inv.app eval`.  The inv-hom round-trip uses
  `Cat.Hom₂.comp_app` to convert composition of 2-cells into composition in the fibre.

This is the "Yoneda element" — the object in `yonedaPairing.obj x` that
`yonedaLemmaBackwardsFunctor` sends `eval` to.
-/
@[simp]
def yonedaLemmaBackwardsFunctorObj (x : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat))
  (eval : (yonedaEvaluation.obj x)) : (yonedaPairing.obj x) where
  app a := {toFunctor := yonedaLemmaBackwardsFunctorObjFunctor x eval a}
  naturality {a b} f := by
    rcases eval with ⟨eval⟩
    fconstructor
    · fconstructor
      fconstructor
      · exact fun X => (x.2.mapComp (Quiver.Hom.op X) (f)).hom.toNatTrans.app eval
      · intro X Y g
        simp only [yoneda₀_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj_α,
        yonedaLemmaBackwardsFunctorObjFunctor, op_unop, Cat.Hom.comp_toFunctor, comp_obj,
        yoneda₀_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map_toFunctor_obj, op_comp,
        Quiver.Hom.op_unop, Functor.comp_map,
        yoneda₀_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map_toFunctor_map,
        op2_whiskerLeft, map₂_whisker_right, Cat.Hom.toNatTrans_comp, Cat.whiskerRight_toNatTrans,
        NatTrans.comp_app, whiskerRight_app,
        Category.assoc]
        congr 1
        -- show inv ≫ hom = id by computing the composite using Cat.Hom₂.comp_app
        set mapCompInv_Y := (x.2.mapComp (Quiver.Hom.op Y) f).inv.toNatTrans.app eval
        set mapCompHom_Y := (x.2.mapComp (Quiver.Hom.op Y) f).hom.toNatTrans.app eval
        let invHomComp_Y : mapCompInv_Y ≫ mapCompHom_Y =
            ((x.2.mapComp (Quiver.Hom.op Y) f).inv ≫ (x.2.mapComp (Quiver.Hom.op Y) f).hom).toNatTrans.app eval :=
          Eq.symm (Cat.Hom₂.comp_app (x.2.mapComp (Quiver.Hom.op Y) f).inv (x.2.mapComp (Quiver.Hom.op Y) f).hom eval)
        simp at invHomComp_Y
        simp [invHomComp_Y]
    · fconstructor
      fconstructor
      · exact fun X => (x.2.mapComp (Quiver.Hom.op X) (f)).inv.toNatTrans.app eval
      · intro X Y g
        simp only [yoneda₀_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj_α,
        yonedaLemmaBackwardsFunctorObjFunctor, op_unop, Cat.Hom.comp_toFunctor, comp_obj,
        yoneda₀_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map_toFunctor_obj, op_comp,
        Quiver.Hom.op_unop, Functor.comp_map,
        yoneda₀_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map_toFunctor_map,
        op2_whiskerLeft, map₂_whisker_right, ← Category.assoc, Cat.Hom.toNatTrans_comp,
        Cat.whiskerRight_toNatTrans, NatTrans.comp_app, whiskerRight_app]
        -- same inv-hom cancellation, now at object X
        set mapCompInv_X := ((x.2.mapComp (Quiver.Hom.op X) f).inv.toNatTrans.app eval)
        set mapCompHom_X := ((x.2.mapComp (Quiver.Hom.op X) f).hom.toNatTrans.app eval)
        let invHomComp_X : mapCompInv_X ≫ mapCompHom_X =
            ((x.2.mapComp (Quiver.Hom.op X) f).inv ≫ (x.2.mapComp (Quiver.Hom.op X) f).hom).toNatTrans.app eval :=
          Eq.symm (Cat.Hom₂.comp_app (x.2.mapComp (Quiver.Hom.op X) f).inv (x.2.mapComp (Quiver.Hom.op X) f).hom eval)
        simp at invHomComp_X
        simp [invHomComp_X]
    · ext X
      simp only [yoneda₀_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj_α, yonedaLemmaBackwardsFunctorObjFunctor,
      op_unop, Cat.Hom.comp_toFunctor, comp_obj,
      yoneda₀_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map_toFunctor_obj, op_comp, Quiver.Hom.op_unop,
      Cat.Hom.toNatTrans_comp, Cat.Hom.toNatTrans_id]
      sorry
    · ext X
      -- the inv_hom_id of mapComp, specialised to the evaluation point via congrArg
      let mapCompInvHomId := (x.2.mapComp (Quiver.Hom.op X) f).inv_hom_id
      let mapCompInvHomId_app := congrArg (fun g => g.toNatTrans.app eval) mapCompInvHomId
      dsimp at mapCompInvHomId_app
      erw [NatTrans.vcomp_app, mapCompInvHomId_app]
      congr

/--
At a fixed pair `x = (b₀, F)`, the *Yoneda embedding functor*
`F.obj b₀ ⥤ StrongTrans (yoneda₀ b₀) F`.

* **On objects**: sends an element `eval : F.obj b₀` to the strong transformation
  `yonedaLemmaBackwardsFunctorObj x eval`, whose `a`-component sends
  `f : unop a ⟶ b₀` to `(F.map f).obj eval`.
* **On morphisms**: sends a morphism `g : eval ⟶ eval'` (lowered through `CatLiftIso`) to the
  modification whose `c`-component has, at each `X`, the morphism
  `(F.map (op X)).map ((CatLiftIso (F.obj b₀)).inverse.map g)`.

This is the component functor of the strong transformation `yonedaLemmaBackwards`.
-/
@[simp]
def yonedaLemmaBackwardsFunctor (x : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat)) : (yonedaEvaluation.obj x) ⥤ (yonedaPairing.obj x) where
  obj a := yonedaLemmaBackwardsFunctorObj x a
  map { a b } f := by
    rcases a with ⟨a⟩
    rcases b with ⟨b⟩
    fconstructor
    fconstructor
    · intro c
      fconstructor
      fconstructor
      · exact fun X => (x.2.map (Quiver.Hom.op X)).toFunctor.map ((CatLiftIso ↑(yonedaEvaluation'.obj x)).inverse.map f)
      · intro X Y g
        simp only [yoneda₀_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj_α, yonedaLemmaBackwardsFunctorObj, yonedaLemmaBackwardsFunctorObjFunctor, op_unop, Cat.Hom.comp_toFunctor, Cat.coe_of, NatTrans.naturality]
    · intro t u g
      refine Cat.Hom₂.ext_iff.mpr ?_
      ext c
      rw [Cat.Hom.toNatTrans_comp,Cat.Hom.toNatTrans_comp]
      simp
      sorry

/--
The *backward strong transformation* `yonedaEvaluation ⟶ yonedaPairing` for the Yoneda lemma.

At each pair `x = (b₀, F)`, the component functor is `yonedaLemmaBackwardsFunctor x`, the
Yoneda embedding functor sending `s : F.obj b₀` to the strong transformation
`(a, f) ↦ (F.map f).obj s`.

This is the inverse direction of the Yoneda equivalence.  Together with `yonedaLemmaForwards`
and the unit/counit isos (`yonedaHomInvId`, `yonedaInvHomId`), it forms `yonedaLemma`.
-/
def yonedaLemmaBackwards : StrongTrans (@yonedaEvaluation B _)  (@yonedaPairing B _) where
  app x := by
    exact {toFunctor := yonedaLemmaBackwardsFunctor x}
  naturality f := by
    sorry

/--
The data of an internal equivalence in a bicategory `B` between objects `x` and `y`.

* `map : x ⟶ y` — the forward 1-morphism.
* `inv : y ⟶ x` — the backward 1-morphism.
* `homInvId : map ≫ inv ≅ 𝟙 x` — a 2-isomorphism witnessing that `inv` is a left inverse
  of `map` up to isomorphism.
* `invHomId : inv ≫ map ≅ 𝟙 y` — a 2-isomorphism witnessing that `inv` is a right inverse
  of `map` up to isomorphism.

Note: this is weaker than an adjoint equivalence (no triangle identities are required), but
sufficient to state the Yoneda lemma as a bicategorical equivalence.
-/
structure BiEquiv (x y : B) where
  map : x ⟶ y
  inv : y ⟶ x
  homInvId : map ≫ inv ≅ 𝟙 x
  invHomId : inv ≫ map ≅ 𝟙 y

/--
The canonical isomorphism used to build the unit of the Yoneda equivalence.

Given:
* `a = (b₀, F)` — a pair in `Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat)`,
* `b : Bᵒᵖ` — the component,
* `x : yonedaPairing.obj a` — a strong transformation `yoneda₀ b₀ ⟶ F`,
* `f : unop b ⟶ b₀` — an object of `(yoneda₀ b₀).obj b`,

this is the isomorphism
  `(yonedaLemmaBackwards.app a ∘ yonedaLemmaForwards.app a)(x).app b f  ≅  x.app b f`

built as the composite:
  `(x.naturality (op f)).inv.app (𝟙 b₀)  ≫  (x.app b).map (ρ_ f).hom`

where `ρ_ f : f ≫ 𝟙 b₀ ≅ f` is the right unitor in `B`.
-/
def yonedaUnitAppIso (a : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat)) (b : Bᵒᵖ) (x : ↑(yonedaPairing.obj a))
    (f : ↑((yoneda₀ (unop a.1)).obj b)) :=
  (Iso.trans
    (Iso.symm (Iso.app (Cat.Hom.toNatIso (x.naturality (Quiver.Hom.op f))) (𝟙 (unop a.1))))
    ((x.app b).toFunctor.mapIso (rightUnitor f)))

/--
For a pair `a = (b₀, F)`, a component `b : Bᵒᵖ`, and a strong transformation
`x : yoneda₀ b₀ ⟶ F`, the natural transformation from the `b`-component of the roundtrip
`(yonedaLemmaBackwards ∘ yonedaLemmaForwards)(x)` back to the `b`-component of `x`.

Each component at `f : unop b ⟶ b₀` is `(yonedaUnitAppIso a b x f).hom`.

This is the innermost layer of the unit coherence; it is assembled into a full modification
by `yonedaHomInvIdNatIso` and then into the unit iso by `yonedaHomInvId`.
-/
def yonedaHomInvIdFunctorIso {a : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat)} (b : Bᵒᵖ) (x : ↑(yonedaPairing.obj a)) :
    (((yonedaLemmaBackwards.app a).toFunctor.obj
        ((yonedaLemmaForwards.app a).toFunctor.obj x)).app b).toFunctor ≅
    (x.app b).toFunctor := by
    fapply NatIso.ofComponents
    · exact (fun y => (yonedaUnitAppIso a b x y))
    · intros X Y h
      apply ((yonedaUnitAppIso a b x Y).comp_inv_eq.mp ?_).symm
      simp [yonedaUnitAppIso]
      have lem : ((ρ_ X).hom ≫ h ≫ (ρ_ Y).inv) = h ▷ (𝟙 (unop a.1))  := by
        exact Eq.symm (Bicategory.whiskerRight_id h)
      erw [<- Category.assoc ((x.app b).toFunctor.map h),<- (x.app b).toFunctor.map_comp, Category.assoc, <- Category.assoc ((x.app b).toFunctor.map (ρ_ X).hom),<- (x.app b).toFunctor.map_comp,lem]
      have hy := x.naturality_naturality (op2 h)
      have hy' := congrArg (fun nt => nt.toNatTrans) hy
      have hy'' := congrArg (fun nt=> nt.app (𝟙 (unop a.1))) hy'
      dsimp at hy''
      have lem2 : (Functor.whiskerRight ((yoneda₀ (unop a.1)).map₂ (op2 h)).toNatTrans (x.app b).toFunctor ≫ (x.naturality Y.op).hom.toNatTrans).app (𝟙 (unop a.1)) = (x.app b).toFunctor.map (h ▷ 𝟙 (unop a.1)) ≫ (x.naturality Y.op).hom.toNatTrans.app (𝟙 (unop a.1)) := by
        exact (eq_of_comp_right_eq fun {Z} ↦ congrFun rfl)
      erw [ <- lem2, hy'',<- NatTrans.comp_app,<- Category.assoc,<- Cat.Hom.toNatTrans_comp,(x.naturality X.op).inv_hom_id,<- Cat.Hom.toNatTrans_comp, Category.id_comp]
      simp [yonedaLemmaBackwards,yonedaLemmaForwards]

/--
At a fixed pair `a = (b₀, F)` and a strong transformation `x : yoneda₀ b₀ ⟶ F`, the
isomorphism
  `(yonedaLemmaForwards.app a ≫ yonedaLemmaBackwards.app a).toFunctor.obj x ≅ x`
in `yonedaPairing.obj a`.

This is the component of the unit natural isomorphism `yonedaHomInvIdNatIso` at the object
`x`, assembled by applying `yonedaHomInvIdFunctorIso` at each component `b : Bᵒᵖ`.
-/
def yonedaHomInvIdObjIso (a : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat)) (x : ↑(yonedaPairing.obj a)) :
    (yonedaLemmaForwards.app a ≫ yonedaLemmaBackwards.app a).toFunctor.obj x ≅
    (𝟭 ↑(yonedaPairing.obj a)).obj x where
  hom := by
    fconstructor
    fconstructor
    · intro b
      fconstructor
      exact (yonedaHomInvIdFunctorIso b x).hom
    · intros a b f
      ext e
      erw [NatTrans.comp_app]
      erw [NatTrans.comp_app]
      simp
      sorry
  inv := by
    fconstructor
    fconstructor
    · intro b
      fconstructor
      exact (yonedaHomInvIdFunctorIso b x).inv
    · sorry

/--
For a pair `a = (b₀, F)`, the modification
`(yonedaLemmaForwards.app a ≫ yonedaLemmaBackwards.app a)(x) ⟶ x`
in `yonedaPairing.obj a`, for each `x : yonedaPairing.obj a`.

This is the component of the unit morphism `yonedaHomInvId.hom` at the object `a`, assembled
component-wise using `yonedaHomInvIdObjIso` for each `b : Bᵒᵖ`.
-/
def yonedaHomInvIdNatIso (a : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat)) :
    (yonedaLemmaForwards.app a ≫ yonedaLemmaBackwards.app a).toFunctor ≅
    (𝟭 ↑(yonedaPairing.obj a)) := by
  fapply NatIso.ofComponents
  · intro x
    exact yonedaHomInvIdObjIso a x
  · sorry

/--
The *unit isomorphism* `yonedaLemmaForwards ≫ yonedaLemmaBackwards ≅ 𝟙 yonedaPairing`.

This witnesses that composing the "evaluate at identity" map with the Yoneda embedding returns
the original strong transformation, up to a canonical isomorphism.  It is the `homInvId` field
of `yonedaLemma`.
-/
def yonedaHomInvId : yonedaLemmaForwards ≫ yonedaLemmaBackwards ≅ 𝟙 (@yonedaPairing B _) where
  hom := by
    refine {as := {app := ?_, naturality := ?_}}
    · intro a
      fconstructor
      exact (yonedaHomInvIdNatIso a).hom
    · sorry
  inv := by
    refine {as := {app := ?_, naturality := ?_}}
    · intro a
      fconstructor
      exact (yonedaHomInvIdNatIso a).inv
    · sorry
  inv_hom_id := by sorry
  hom_inv_id := by sorry

/--
For a pair `a = (b₀, F)`, the natural transformation from the roundtrip functor
`(yonedaLemmaBackwards.app a ≫ yonedaLemmaForwards.app a)` to the identity on
`yonedaEvaluation.obj a`.

This is the component of the counit morphism `yonedaInvHomId.hom` at the object `a`,
witnessing that `yonedaLemmaForwards(yonedaLemmaBackwards(s)) ≅ s` for `s : F.obj b₀`.
-/
def yonedaInvHomIdNatTrans (a : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat)) :
    NatTrans (yonedaLemmaBackwards.app a ≫ yonedaLemmaForwards.app a).toFunctor
    (𝟭 ↑(yonedaEvaluation.obj a)) where
  app x := by
    fconstructor
    rcases x with ⟨x⟩
    dsimp [yonedaLemmaForwards,ULiftHom.objDown,yonedaLemmaBackwards,Quiver.Hom]
    refine (a.2.mapId (a.1)).hom.toNatTrans.app x ≫ eqToHom (?_)
    simp
  naturality {x y} f := by
    sorry

/--
At a fixed pair `a = (b₀, F)`, the natural isomorphism from the roundtrip functor
`(yonedaLemmaBackwards.app a ≫ yonedaLemmaForwards.app a)` to the identity on
`yonedaEvaluation.obj a`.

This is the component of the counit `yonedaInvHomId` at the object `a`, witnessing that
`yonedaLemmaForwards(yonedaLemmaBackwards(s)) ≅ s` for `s : F.obj b₀`.
-/
def yonedaInvHomIdNatIso (a : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat)) :
    (yonedaLemmaBackwards.app a ≫ yonedaLemmaForwards.app a).toFunctor ≅
    (𝟭 ↑(yonedaEvaluation.obj a)) := by
  fapply NatIso.ofComponents
  · intro x
    rcases x with ⟨x⟩
    dsimp [yonedaLemmaForwards,ULiftHom.objDown,yonedaLemmaBackwards,Quiver.Hom]
    let I1 := ((Cat.Hom.toNatIso (a.2.mapId (a.1))).app x)
    letI : Category.{w, max (max u v) w} (ULift.{max (max u v) w, v} ↑(yonedaEvaluation'.obj a)) := by
      exact uliftCategory ↑(yonedaEvaluation'.obj a)
    let FF := ((@ULift.upFunctor.{_,_,max (max u v) w} (↑(yonedaEvaluation'.obj a)) _).mapIso I1)
    let FFF := ULiftHom.up.mapIso FF
    exact FFF
  · sorry


/--
The *counit isomorphism* `yonedaLemmaBackwards ≫ yonedaLemmaForwards ≅ 𝟙 yonedaEvaluation`.

This witnesses that composing the Yoneda embedding with "evaluate at identity" returns the
original element of `F.obj b`, up to a canonical isomorphism.  It is the `invHomId` field
of `yonedaLemma`.
-/
def yonedaInvHomId : yonedaLemmaBackwards ≫ yonedaLemmaForwards ≅ 𝟙 (@yonedaEvaluation B _)  where
  hom := by
    refine {as := {app := ?_, naturality := ?_}}
    · intro a
      fconstructor
      exact (yonedaInvHomIdNatIso a).hom
    · intros a b f
      sorry
  inv := by
    refine {as := {app := ?_, naturality := ?_}}
    · intro a
      fconstructor
      exact (yonedaInvHomIdNatIso a).inv
    · intros a b f
      sorry

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
