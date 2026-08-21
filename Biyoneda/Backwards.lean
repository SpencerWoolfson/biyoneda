/-
Copyright (c) 2026 Spencer Woolfson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Spencer Woolfson
-/
import Biyoneda.Pairing

/-!
# The backward direction: transport along the pseudofunctor

`yonedaLemmaBackwards : yonedaEvaluation ⟶ yonedaPairing` sends an object `s : F.obj b` to the
strong transformation `(a, f) ↦ (F.map f).obj s`.

Unlike the forward direction this is still hand-rolled: the `ULift` in its *domain* is
destructured by hand rather than handled by `CatLiftStrongTransDomData.lift`.  Porting it is
what would remove the remaining lift plumbing from the development.

Naming: `_core` lemmas are stated in the unlifted fibre; `backwards_square_lifted` is the one
statement that lives in the lifted world.
-/

namespace Biyoneda

open CategoryTheory Bicategory Bicategory.Opposite Opposite Pseudofunctor StrongTrans Functor
open scoped Pseudofunctor.StrongTrans

universe u v w v₁ v₂ u₁ u₂

attribute [local instance] uliftCategory


variable {B : Type u} [Bicategory.{w, v} B]

universe w₁

/--
At a fixed pair `x = (b₀, F)`, an evaluation point `eval : F.obj b₀`, and a component
`a : Bᵒᵖ`, the functor `(unop a ⟶ b₀) ⥤ F.obj a` sending `f ↦ (F.map f).obj eval`.

In terms of `yoneda₀ b₀`, the source category at `a` is the hom-category `(unop a ⟶ b₀)`:
* **On objects**: `f : unop a ⟶ b₀` maps to `(F.map (Quiver.Hom.op f)).obj eval : F.obj a`.
* **On morphisms**: a 2-cell `α : f ⟶ g` (a morphism in `Bᵒᵖ`) maps to
  `(F.map₂ (op2 α)).toNatTrans.app eval`.
* **Functoriality**: follows from `F.map₂_id` and `F.map₂_comp` via `erw` through the
  universe-level coercion introduced by `Cat.of`.

This is the functor underlying the `a`-component of `backwardsTrans`.
-/
@[simp]
def backwardsFibreFunctor (x : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat))
    (eval : yonedaEvaluation.obj x) (a : Bᵒᵖ) :
    ↑((yoneda₀ (unop x.1)).obj a) ⥤ ↑(x.2.obj a) where
  obj b := (x.2.map (Quiver.Hom.op b)).toFunctor.obj (ULift.down eval)
  map {X Y} f := (x.2.map₂ (op2 f)).toNatTrans.app (ULift.down eval)
  map_id _ := by erw [op2_id, PrelaxFunctor.map₂_id]; rfl
  map_comp _ _ := by erw [op2_comp, PrelaxFunctor.map₂_comp]; rfl

/-- Component form of `mapComp_id_right_hom`, matching the `naturality_id` obligation of
`backwardsTrans`: composing the `mapComp` coherence with the `mapId` coherence
is the image of the (opposite of the) left unitor. -/
lemma mapComp_id_app (F : Bᵒᵖ ⥤ᵖ Cat.{w, v}) {b₀ a : Bᵒᵖ}
    (X : unop a ⟶ unop b₀) (eval : ↑(F.obj b₀)) :
    (F.mapComp (Quiver.Hom.op X) (𝟙 a)).hom.toNatTrans.app eval ≫
      (F.mapId a).hom.toNatTrans.app ((F.map (Quiver.Hom.op X)).toFunctor.obj eval) =
    (F.map₂ (op2 (λ_ X).hom)).toNatTrans.app eval ≫
      𝟙 ((F.map (Quiver.Hom.op X)).toFunctor.obj eval) ≫
        𝟙 ((F.map (Quiver.Hom.op X)).toFunctor.obj eval) := by
  rw [Pseudofunctor.mapComp_id_right_hom]
  simp [op2_leftUnitor_hom]

/-- Component form of `mapComp_assoc_right_hom`, matching the `naturality_comp` obligation of
`backwardsTrans`. -/
lemma mapComp_assoc_app (F : Bᵒᵖ ⥤ᵖ Cat.{w, v}) {b₀ a b c : Bᵒᵖ}
    (f : a ⟶ b) (g : b ⟶ c) (X : unop a ⟶ unop b₀) (eval : ↑(F.obj b₀)) :
    (F.mapComp (Quiver.Hom.op X) (f ≫ g)).hom.toNatTrans.app eval ≫
      (F.mapComp f g).hom.toNatTrans.app ((F.map (Quiver.Hom.op X)).toFunctor.obj eval) =
    (F.map₂ (op2 (α_ g.unop f.unop X).hom)).toNatTrans.app eval ≫
      𝟙 ((F.map ((Quiver.Hom.op X ≫ f) ≫ g)).toFunctor.obj eval) ≫
        (F.mapComp (Quiver.Hom.op X ≫ f) g).hom.toNatTrans.app eval ≫
          𝟙 ((F.map g).toFunctor.obj ((F.map (Quiver.Hom.op X ≫ f)).toFunctor.obj eval)) ≫
            (F.map g).toFunctor.map
              ((F.mapComp (Quiver.Hom.op X) f).hom.toNatTrans.app eval) ≫
              𝟙 ((F.map g).toFunctor.obj ((F.map f).toFunctor.obj
                ((F.map (Quiver.Hom.op X)).toFunctor.obj eval))) := by
  simp only [op2_associator_hom]
  simpa using Cat.Hom₂.congr_app
    (F.mapComp_assoc_right_hom (Quiver.Hom.op X) f g) eval

/--
At a fixed pair `x = (b₀, F)` and an evaluation point `eval : F.obj b₀`, the strong
transformation `yoneda₀ b₀ ⟶ F` corresponding to `eval` under the Yoneda embedding.

* **Component at `a`**: the functor `backwardsFibreFunctor x eval a`, which
  sends `f : unop a ⟶ b₀` to `(F.map f).obj eval`.
* **Naturality at `f : a ⟶ b`**: an isomorphism built from the associativity coherence
  `F.mapComp`, whose hom component at `X` is `(F.mapComp (op X) f).hom.app eval` and whose
  inv component at `X` is `(F.mapComp (op X) f).inv.app eval`.  The inv-hom round-trip uses
  `Cat.Hom₂.comp_app` to convert composition of 2-cells into composition in the fibre.

This is the "Yoneda element" — the object in `yonedaPairing.obj x` that
`yonedaLemmaBackwardsFunctor` sends `eval` to.
-/
@[simp]
def backwardsTrans (x : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat))
    (eval : yonedaEvaluation.obj x) : Pseudofunctor.StrongTrans (yoneda₀ (unop x.1)) x.2 where
  app a := {toFunctor := backwardsFibreFunctor x eval a}
  naturality {a b} f := by
    refine Cat.Hom.isoMk (NatIso.ofComponents ?_ ?_)
    · intro X
      exact (Cat.Hom.toNatIso (x.2.mapComp (Quiver.Hom.op X) f)).app
        (ULift.casesOn eval fun eval ↦ eval)
    · intro X Y g
      rcases eval with ⟨eval⟩
      simp only [yoneda₀_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj_α,
        backwardsFibreFunctor, op_unop, Cat.Hom.comp_toFunctor, comp_obj,
        yoneda₀_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map_toFunctor_obj, op_comp,
        Quiver.Hom.op_unop, Functor.comp_map,
        yoneda₀_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map_toFunctor_map,
        op2_whiskerLeft, map₂_whisker_right, Cat.Hom.toNatTrans_comp, Cat.whiskerRight_toNatTrans,
        NatTrans.comp_app, whiskerRight_app,
        Category.assoc]
      congr 1
      rcases x.2.mapComp (Quiver.Hom.op Y) f with ⟨hom, inv, _, inv_hom⟩
      dsimp [yonedaEvaluation'] at eval
      have : inv.toNatTrans.app eval ≫ hom.toNatTrans.app eval =
          (inv ≫ hom).toNatTrans.app eval := by
        simp
      erw [this, inv_hom]
      simp
  naturality_naturality {a b c} f g := by
    rcases eval with ⟨eval⟩
    exact Cat.Hom₂.ext_app fun X ↦
      Cat.Hom₂.congr_app (x.2.toOplax.mapComp_naturality_right (Quiver.Hom.op X) g) eval
  naturality_id a := by
    rcases eval with ⟨eval⟩
    exact Cat.Hom₂.ext_app fun X ↦ mapComp_id_app x.2 X eval
  naturality_comp {a b c} f g := by
    rcases eval with ⟨eval⟩
    exact Cat.Hom₂.ext_app fun X ↦ mapComp_assoc_app x.2 f g X eval

set_option backward.isDefEq.respectTransparency false in
/--
At a fixed pair `x = (b₀, F)`, the *Yoneda embedding functor*
`F.obj b₀ ⥤ StrongTrans (yoneda₀ b₀) F`.

* **On objects**: sends an element `eval : F.obj b₀` to the strong transformation
  `backwardsTrans x eval`, whose `a`-component sends
  `f : unop a ⟶ b₀` to `(F.map f).obj eval`.
* **On morphisms**: sends a morphism `g : eval ⟶ eval'` (lowered through `catLiftEquiv`) to the
  modification whose `c`-component has, at each `X`, the morphism
  `(F.map (op X)).map ((catLiftEquiv (F.obj b₀)).inverse.map g)`.

This is the component functor of the strong transformation `yonedaLemmaBackwards`.
-/
@[simp]
def yonedaLemmaBackwardsFunctor (x : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat)) :
    yonedaEvaluation.obj x ⥤ yonedaPairing.obj x where
  obj a := backwardsTrans x a
  map {a b} f := by
    rcases a with ⟨a⟩
    rcases b with ⟨b⟩
    refine { as := { app := ?_, naturality := ?_ } }
    · intro c
      refine { toNatTrans := { app := ?_, naturality := ?_ } }
      · exact fun X ↦ (x.2.map (Quiver.Hom.op X)).toFunctor.map
          ((catLiftEquiv.{w, max u v, v, max u (max v w)} ↑(yonedaEvaluation'.obj x)).inverse.map f)
      · intro X Y g
        simp only [yoneda₀_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj_α,
          backwardsTrans, backwardsFibreFunctor, op_unop,
          Cat.Hom.comp_toFunctor, Cat.coe_of, NatTrans.naturality]
    · intro t u g
      refine Cat.Hom₂.ext_iff.mpr ?_
      ext c
      rw [Cat.Hom.toNatTrans_comp, Cat.Hom.toNatTrans_comp]
      simp only [yoneda₀_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj_α,
        backwardsTrans, backwardsFibreFunctor, op_unop,
        Cat.Hom.comp_toFunctor, comp_obj, Cat.coe_of, Cat.whiskerLeft_toNatTrans,
        Cat.Hom.isoMk_hom, NatTrans.toCatHom₂_toNatTrans, Cat.whiskerRight_toNatTrans]
      exact (x.2.mapComp (Quiver.Hom.op c) g).hom.toNatTrans.naturality
        ((catLiftEquiv.{w, max u v, v, max u (max v w)} ↑(yonedaEvaluation'.obj x)).inverse.map f)
  map_id X := by
    obtain ⟨a⟩ := X
    apply homCategory.ext
    intro c
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext W
    exact (congrArg (x.2.map (Quiver.Hom.op W)).toFunctor.map
        ((catLiftEquiv.{w, max u v, v, max u (max v w)}
          ↑(yonedaEvaluation'.obj x)).inverse.map_id _)).trans
      ((x.2.map (Quiver.Hom.op W)).toFunctor.map_id _)
  map_comp {X Y Z} f g := by
    obtain ⟨a⟩ := X
    obtain ⟨b⟩ := Y
    obtain ⟨c'⟩ := Z
    apply homCategory.ext
    intro c
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext W
    exact (congrArg (x.2.map (Quiver.Hom.op W)).toFunctor.map
        ((catLiftEquiv.{w, max u v, v, max u (max v w)}
          ↑(yonedaEvaluation'.obj x)).inverse.map_comp f g)).trans
      ((x.2.map (Quiver.Hom.op W)).toFunctor.map_comp _ _)

/-- The inner naturality square for `yonedaLemmaBackwards`: sliding a 2-cell of the
represented object past the `mapComp` and `naturality` coherence isos.  Assembled from the
inverse forms of `mapComp_naturality_right` (for both pseudofunctors) and
`naturality_naturality` of the strong transformation. -/
lemma backwards_inner_core {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b) {α : Bᵒᵖ}
    {XX YY : ↑((yoneda₀ (unop b.1)).obj α)} (h : XX ⟶ YY) (X : ↑(yonedaEvaluation'.obj a)) :
    (b.2.map₂ (op2 h)).toNatTrans.app
        ((b.2.map f.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj X)) ≫
      (b.2.mapComp f.1 (Quiver.Hom.op YY)).inv.toNatTrans.app
        ((f.2.app a.1).toFunctor.obj X) ≫
        (f.2.naturality (f.1 ≫ Quiver.Hom.op YY)).inv.toNatTrans.app X =
    ((b.2.mapComp f.1 (Quiver.Hom.op XX)).inv.toNatTrans.app
        ((f.2.app a.1).toFunctor.obj X) ≫
        (f.2.naturality (f.1 ≫ Quiver.Hom.op XX)).inv.toNatTrans.app X) ≫
      (f.2.app α).toFunctor.map
        (((a.2.mapComp f.1 (Quiver.Hom.op XX)).hom ≫
            a.2.map f.1 ◁ a.2.map₂ (op2 h) ≫
              (a.2.mapComp f.1 (Quiver.Hom.op YY)).inv).toNatTrans.app X) := by
  have h1 := Cat.Hom₂.congr_app
    (b.2.toOplax.mapComp_naturality_right f.1 (op2 h)) ((f.2.app a.1).toFunctor.obj X)
  have h2 := f.2.naturality_naturality_app (f.1 ◁ op2 h) X
  have h3 := Cat.Hom₂.congr_app
    (a.2.toOplax.mapComp_naturality_right f.1 (op2 h)) X
  dsimp at h1 h2 h3
  -- s1: slide map₂(op2 h) past the b.2.mapComp iso (inverse form of h1)
  have s1 : (b.2.map₂ (op2 h)).toNatTrans.app
        ((b.2.map f.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj X)) ≫
      (b.2.mapComp f.1 (Quiver.Hom.op YY)).inv.toNatTrans.app
        ((f.2.app a.1).toFunctor.obj X) =
      (b.2.mapComp f.1 (Quiver.Hom.op XX)).inv.toNatTrans.app
        ((f.2.app a.1).toFunctor.obj X) ≫
      (b.2.map₂ (f.1 ◁ op2 h)).toNatTrans.app ((f.2.app a.1).toFunctor.obj X) := by
    apply (Iso.comp_inv_eq ((Cat.Hom.toNatIso
      (b.2.mapComp f.1 (Quiver.Hom.op YY))).app ((f.2.app a.1).toFunctor.obj X))).mpr
    erw [Category.assoc]
    apply (Iso.eq_inv_comp ((Cat.Hom.toNatIso
      (b.2.mapComp f.1 (Quiver.Hom.op XX))).app ((f.2.app a.1).toFunctor.obj X))).mpr
    exact h1.symm
  -- s2: slide b.2.map₂ (f.1 ◁ op2 h) past f.2.naturality (inverse form of h2)
  have s2 : (b.2.map₂ (f.1 ◁ op2 h)).toNatTrans.app ((f.2.app a.1).toFunctor.obj X) ≫
      (f.2.naturality (f.1 ≫ Quiver.Hom.op YY)).inv.toNatTrans.app X =
      (f.2.naturality (f.1 ≫ Quiver.Hom.op XX)).inv.toNatTrans.app X ≫
      (f.2.app α).toFunctor.map ((a.2.map₂ (f.1 ◁ op2 h)).toNatTrans.app X) := by
    apply (Iso.comp_inv_eq ((Cat.Hom.toNatIso
      (f.2.naturality (f.1 ≫ Quiver.Hom.op YY))).app X)).mpr
    erw [Category.assoc]
    apply (Iso.eq_inv_comp ((Cat.Hom.toNatIso
      (f.2.naturality (f.1 ≫ Quiver.Hom.op XX))).app X)).mpr
    exact h2.symm
  -- s3: the conjugated 2-cell collapses (component form of h3)
  have s3 : ((a.2.mapComp f.1 (Quiver.Hom.op XX)).hom ≫
        a.2.map f.1 ◁ a.2.map₂ (op2 h) ≫
          (a.2.mapComp f.1 (Quiver.Hom.op YY)).inv).toNatTrans.app X =
      (a.2.map₂ (f.1 ◁ op2 h)).toNatTrans.app X := by
    simp only [Cat.Hom.toNatTrans_comp, NatTrans.comp_app]
    rw [← Category.assoc]
    apply (Iso.comp_inv_eq ((Cat.Hom.toNatIso
      (a.2.mapComp f.1 (Quiver.Hom.op YY))).app X)).mpr
    exact h3.symm
  rw [← Category.assoc, s1]
  erw [Category.assoc, s2]
  rw [← s3]
  erw [← Category.assoc]
  rfl

/-- Component (at `α`) of the naturality iso of `yonedaLemmaBackwards` at `f : a ⟶ b`. -/
def backwardsNaturalityIsoApp {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b)
    (X : ↑(yonedaEvaluation.obj a)) (α : Bᵒᵖ) :
    (((yonedaEvaluation.map f).toFunctor ⋙ yonedaLemmaBackwardsFunctor b).obj X).app α ≅
      ((yonedaLemmaBackwardsFunctor a ⋙ (yonedaPairing.map f).toFunctor).obj X).app α :=
  Cat.Hom.isoMk (NatIso.ofComponents
    (fun XX ↦
      (Cat.Hom.toNatIso (b.2.mapComp f.1 XX.op).symm).app
        ((f.2.app a.1).toFunctor.obj (ULift.down X)) ≪≫
        (Cat.Hom.toNatIso (f.2.naturality (f.1 ≫ XX.op))).symm.app (ULift.down X))
    (fun {XX YY} h ↦ by
      dsimp [yonedaEvaluation, catPseudoULift, catLift, Functor.comp,
        ULiftHomULiftCategory.equivCongrLeft, ULiftHom.objUp, ULift.upFunctor,
        ULiftHom.objDown, yonedaEvaluation']
      erw [Pseudofunctor.map₂_whisker_left]
      exact backwards_inner_core f h (ULift.down X)))

/-- The cancellation core of the backwards naturality square: all atoms in canonical
spelling, `X` unlifted. -/
lemma backwards_square_core {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b)
    (X : ↑(yonedaEvaluation'.obj a)) {a₁ b₁ : Bᵒᵖ} (f₁ : a₁ ⟶ b₁)
    (ZZ : ↑((yoneda₀ (unop b.1)).obj a₁)) :
    (f.2.app b₁).toFunctor.map
        ((a.2.map₂ (α_ f.1 (Quiver.Hom.op ZZ) f₁).inv).toNatTrans.app X) ≫
      (f.2.app b₁).toFunctor.map
        ((a.2.mapComp (f.1 ≫ Quiver.Hom.op ZZ) f₁).hom.toNatTrans.app X) ≫
      (f.2.naturality f₁).hom.toNatTrans.app
        ((a.2.map (f.1 ≫ Quiver.Hom.op ZZ)).toFunctor.obj X) =
    (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ ≫ f₁)).hom.toNatTrans.app X ≫
      (b.2.mapComp f.1 (Quiver.Hom.op ZZ ≫ f₁)).hom.toNatTrans.app
        ((f.2.app a.1).toFunctor.obj X) ≫
      (b.2.mapComp (Quiver.Hom.op ZZ) f₁).hom.toNatTrans.app
        ((b.2.map f.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj X)) ≫
      (b.2.map f₁).toFunctor.map
        ((b.2.mapComp f.1 (Quiver.Hom.op ZZ)).inv.toNatTrans.app
            ((f.2.app a.1).toFunctor.obj X) ≫
          (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app X) := by
  have h3 := Pseudofunctor.mapComp_assoc_right_hom_app b.2 f.1 (Quiver.Hom.op ZZ) f₁
    ((f.2.app a.1).toFunctor.obj X)
  rw [Pseudofunctor.StrongTrans.naturality_naturality_hom_app f.2
      (α_ f.1 (Quiver.Hom.op ZZ) f₁) X,
    Pseudofunctor.StrongTrans.naturality_comp_hom_app f.2 (f.1 ≫ Quiver.Hom.op ZZ) f₁ X]
  simp only [Category.assoc]
  erw [reassoc_of% h3]
  have h1 := Pseudofunctor.StrongTrans.naturality_naturality_hom_app f.2
    (α_ f.1 (Quiver.Hom.op ZZ) f₁) X
  have h2 := Pseudofunctor.StrongTrans.naturality_comp_hom_app f.2
    (f.1 ≫ Quiver.Hom.op ZZ) f₁ X
  have c1 : (b.2.map₂ (α_ f.1 (Quiver.Hom.op ZZ) f₁).hom).toNatTrans.app
        ((f.2.app a.1).toFunctor.obj X) ≫
      (b.2.map₂ (α_ f.1 (Quiver.Hom.op ZZ) f₁).inv).toNatTrans.app
        ((f.2.app a.1).toFunctor.obj X) = 𝟙 _ := by
    rw [← Cat.Hom₂.comp_app, ← PrelaxFunctor.map₂_comp, Iso.hom_inv_id,
      PrelaxFunctor.map₂_id, Cat.Hom₂.id_app]
  have c2 := Cat.Hom.inv_hom_id_toNatTrans_app (b.2.mapComp (f.1 ≫ Quiver.Hom.op ZZ) f₁)
    ((f.2.app a.1).toFunctor.obj X)
  have c3 := Cat.Hom.hom_inv_id_toNatTrans_app (b.2.mapComp f.1 (Quiver.Hom.op ZZ))
    ((f.2.app a.1).toFunctor.obj X)
  have c4 := Cat.Hom.hom_inv_id_toNatTrans_app (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ)) X
  have hN := h1
  rw [h2] at hN
  simp only [Category.assoc] at hN
  rw [← hN]
  erw [reassoc_of% h1]
  rw [reassoc_of% c1]
  rw [reassoc_of% h2]
  erw [reassoc_of% c2]
  rw [← Functor.map_comp, ← Functor.map_comp]
  erw [reassoc_of% c3]
  erw [c4]
  erw [Functor.map_id]
  erw [Category.comp_id]
  rfl

/-- Point form of the naturality square, spelled through the composite strong
transformation (defeq to `yonedaPairing.map`'s literal pasting).

The proof distributes the strong-transformation component through the whiskered/associated
composite from `categoryStruct_comp_naturality_hom`. This is an ordered `erw` chain rather
than a `simp only`: the `≫`/`α_`/`▷` come from the `postcomp₂` bicategory and are only *defeq*
to `Cat`'s operations (an instance diamond), so the `Cat.*_app` distribution lemmas match at
default transparency but not reducible. The order is fixed by the composite's shape. -/
lemma backwards_square_lifted {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b)
    (X : ↑(yonedaEvaluation.obj a)) {a₁ b₁ : Bᵒᵖ} (f₁ : a₁ ⟶ b₁)
    (ZZ : ↑((yoneda₀ (unop b.1)).obj a₁)) :
    ((b.2.mapComp f.1 (Quiver.Hom.op ZZ ≫ f₁)).inv.toNatTrans.app
        ((f.2.app a.1).toFunctor.obj (ULift.down X)) ≫
      (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ ≫ f₁)).inv.toNatTrans.app (ULift.down X)) ≫
      ((postcomp₂ f.1.unop ≫ (backwardsTrans a X ≫ f.2)).naturality
        f₁).hom.toNatTrans.app ZZ =
    (b.2.mapComp (Quiver.Hom.op ZZ) f₁).hom.toNatTrans.app
        ((b.2.map f.1).toFunctor.obj ((f.2.app a.1).toFunctor.obj (ULift.down X))) ≫
      (b.2.map f₁).toFunctor.map
        ((b.2.mapComp f.1 (Quiver.Hom.op ZZ)).inv.toNatTrans.app
            ((f.2.app a.1).toFunctor.obj (ULift.down X)) ≫
          (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app (ULift.down X)) := by
  obtain ⟨X⟩ := X
  simp only [categoryStruct_comp_naturality_hom]
  iterate 4 erw [Cat.Hom₂.comp_app]
  rw [Cat.associator_inv_app]
  rw [Cat.whiskerRight_app]
  rw [Cat.associator_hom_app]
  rw [Cat.whiskerLeft_app]
  iterate 4 erw [Cat.Hom₂.comp_app]
  rw [Cat.associator_inv_app]
  rw [Cat.whiskerRight_app]
  rw [Cat.associator_hom_app]
  rw [Cat.whiskerLeft_app]
  erw [Cat.whiskerLeft_app]
  iterate 3 erw [eqToHom_refl]
  iterate 3 erw [Category.id_comp]
  rw [Cat.associator_inv_app]
  iterate 4 (first | erw [eqToHom_refl] | erw [Category.id_comp] | erw [Category.comp_id])
  dsimp only [postcomp₂, postcomposingCat]
  simp only [Category.assoc]
  apply (Iso.inv_comp_eq ((Cat.Hom.toNatIso (b.2.mapComp f.1 (Quiver.Hom.op ZZ ≫ f₁))).app
    ((f.2.app a.1).toFunctor.obj X))).mpr
  apply (Iso.inv_comp_eq ((Cat.Hom.toNatIso (f.2.naturality
    (f.1 ≫ Quiver.Hom.op ZZ ≫ f₁))).app X)).mpr
  exact backwards_square_core f X f₁ ZZ

/-- The strong-transformation naturality square for `backwardsNaturalityIsoApp`. -/
lemma backwards_naturality_square {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b)
    (X : ↑(yonedaEvaluation.obj a)) {a₁ b₁ : Bᵒᵖ} (f₁ : a₁ ⟶ b₁) :
    (yoneda₀ (unop b.1)).map f₁ ◁ (backwardsNaturalityIsoApp f X b₁).hom ≫
      (((yonedaLemmaBackwardsFunctor a ⋙ (yonedaPairing.map f).toFunctor).obj X).naturality
        f₁).hom =
    ((((yonedaEvaluation.map f).toFunctor ⋙ yonedaLemmaBackwardsFunctor b).obj X).naturality
        f₁).hom ≫ (backwardsNaturalityIsoApp f X a₁).hom ▷ b.2.map f₁ := by
  apply Cat.Hom₂.ext_app
  intro ZZ
  simp only [Cat.Hom.toNatTrans_comp, NatTrans.comp_app, Cat.whiskerLeft_toNatTrans,
    Cat.whiskerRight_toNatTrans, whiskerLeft_app, whiskerRight_app]
  exact backwards_square_lifted f X f₁ ZZ

/-- The naturality iso of `yonedaLemmaBackwards` at `f : a ⟶ b`, componentwise. -/
def backwardsNaturalityIso {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b)
    (X : ↑(yonedaEvaluation.obj a)) :
    ((yonedaEvaluation.map f).toFunctor ⋙ yonedaLemmaBackwardsFunctor b).obj X ≅
      (yonedaLemmaBackwardsFunctor a ⋙ (yonedaPairing.map f).toFunctor).obj X :=
  StrongTrans.isoMk (fun α ↦ backwardsNaturalityIsoApp f X α)
    (fun f₁ ↦ backwards_naturality_square f X f₁)

/-- The cancellation core of `backwards_naturality_iso_natural`: two `NatTrans.naturality`
squares of the component isos, in canonical spellings. -/
lemma backwards_natural_core {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b)
    {X Y : ↑(yonedaEvaluation'.obj a)} (f₁ : X ⟶ Y) {γ : Bᵒᵖ}
    (ZZ : ↑((yoneda₀ (unop b.1)).obj γ)) :
    (b.2.map f.1 ≫ b.2.map (Quiver.Hom.op ZZ)).toFunctor.map
        ((f.2.app a.1).toFunctor.map f₁) ≫
      (b.2.mapComp f.1 (Quiver.Hom.op ZZ)).inv.toNatTrans.app
        ((f.2.app a.1).toFunctor.obj Y) ≫
      (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app Y =
    ((b.2.mapComp f.1 (Quiver.Hom.op ZZ)).inv.toNatTrans.app
        ((f.2.app a.1).toFunctor.obj X) ≫
      (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app X) ≫
      (f.2.app γ).toFunctor.map ((a.2.map (f.1 ≫ Quiver.Hom.op ZZ)).toFunctor.map f₁) := by
  have s1 := (b.2.mapComp f.1 (Quiver.Hom.op ZZ)).inv.toNatTrans.naturality
    ((f.2.app a.1).toFunctor.map f₁)
  have s2 : (b.2.map (f.1 ≫ Quiver.Hom.op ZZ)).toFunctor.map
        ((f.2.app a.1).toFunctor.map f₁) ≫
      (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app Y =
      (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app X ≫
      (f.2.app γ).toFunctor.map ((a.2.map (f.1 ≫ Quiver.Hom.op ZZ)).toFunctor.map f₁) :=
    (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.naturality f₁
  rw [reassoc_of% s1, s2]
  exact (Category.assoc _ _ _).symm

/-- Naturality (in `X`) of `backwardsNaturalityIso`. -/
lemma backwards_naturality_iso_natural {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} (f : a ⟶ b)
    {X Y : ↑(yonedaEvaluation.obj a)} (f₁ : X ⟶ Y) :
    ((yonedaEvaluation.map f).toFunctor ⋙ yonedaLemmaBackwardsFunctor b).map f₁ ≫
      (backwardsNaturalityIso f Y).hom =
    (backwardsNaturalityIso f X).hom ≫
      (yonedaLemmaBackwardsFunctor a ⋙ (yonedaPairing.map f).toFunctor).map f₁ := by
  obtain ⟨X⟩ := X
  obtain ⟨Y⟩ := Y
  obtain ⟨f₁⟩ := f₁
  apply homCategory.ext
  intro γ
  apply Cat.Hom₂.ext_app
  intro ZZ
  erw [homCategory_comp_as_app, homCategory_comp_as_app]
  dsimp only [backwardsNaturalityIso]
  simp only [isoMk_hom_as_app]
  exact backwards_natural_core f f₁ ZZ

/-- Lift-plumbing reduction: the backwards functor's `.map` component, stated with the
morphism generic so the def's internal `rcases` fires, so it holds by `rfl`.  Must be applied
with `erw` (the `StrongTrans` `homCategory` diamond). -/
lemma backwards_map_comp (x : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})) {A₀ B₀ : ↑(yonedaEvaluation'.obj x)}
    (m : A₀ ⟶ B₀) (c : Bᵒᵖ) (W : ↑((yoneda₀ (unop x.1)).obj c)) :
    (((((yonedaLemmaBackwardsFunctor x).map { down := m }).as.app c).toNatTrans).app W)
      = (x.2.map (Quiver.Hom.op W)).toFunctor.map m := rfl

/-- The reduced fibre-morphism core of `naturality_naturality` for `yonedaLemmaBackwards`:
the 2-cell coherence descended to a single fibre `↑(b.2.obj γ)`.  Using the composite 2-cell
`θ = η.1 ▷ ZZ.op` linearizes the proof into three inverse slides — the `b.2.mapComp`
naturality (`hmc`), the strong-transformation `naturality_naturality` (`hnn`), and the
modification naturality of `η.2` (`hmod`) — plus the `mapComp`-inverse point transport. -/
lemma backwards_naturality_naturality_core {a b : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})} {f g : a ⟶ b}
    (η : f ⟶ g) (x : ↑(yonedaEvaluation'.obj a)) {γ : Bᵒᵖ}
    (ZZ : ↑((yoneda₀ (unop b.1)).obj γ)) :
    (b.2.map (Quiver.Hom.op ZZ)).toFunctor.map
        ((b.2.map f.1).toFunctor.map ((η.2.as.app a.1).toNatTrans.app x) ≫
          (b.2.map₂ η.1).toNatTrans.app ((g.2.app a.1).toFunctor.obj x)) ≫
      (b.2.mapComp g.1 (Quiver.Hom.op ZZ)).inv.toNatTrans.app ((g.2.app a.1).toFunctor.obj x) ≫
        (g.2.naturality (g.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app x =
    ((b.2.mapComp f.1 (Quiver.Hom.op ZZ)).inv.toNatTrans.app ((f.2.app a.1).toFunctor.obj x) ≫
        (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app x) ≫
      (f.2.app γ).toFunctor.map ((a.2.map₂ (op2 (ZZ ◁ η.1.unop2))).toNatTrans.app x) ≫
        (η.2.as.app γ).toNatTrans.app
          ((a.2.map (Quiver.Hom.op
            ((postcomp (unop γ) g.1.unop).toCatHom.toFunctor.obj ZZ))).toFunctor.obj x) := by
  -- The three coherences, component-distributed (θ = η.1 ▷ ZZ.op linearizes the chain)
  have hmc := Cat.Hom₂.congr_app
    (b.2.toOplax.mapComp_naturality_left η.1 (Quiver.Hom.op ZZ)) ((g.2.app a.1).toFunctor.obj x)
  have hnn := g.2.naturality_naturality_app (η.1 ▷ Quiver.Hom.op ZZ) x
  have hmod := modification_naturality_app η.2 (f.1 ≫ Quiver.Hom.op ZZ) x
  simp only [Cat.Hom.toNatTrans_comp, NatTrans.comp_app,
    Cat.whiskerRight_toNatTrans, whiskerRight_app] at hmc hnn hmod
  -- hmc_inv: slide map₂ η.1 past the b.2.mapComp iso (inverse form), point G_ax
  have hmc_inv : (b.2.map (Quiver.Hom.op ZZ)).toFunctor.map
        ((b.2.map₂ η.1).toNatTrans.app ((g.2.app a.1).toFunctor.obj x)) ≫
      (b.2.mapComp g.1 (Quiver.Hom.op ZZ)).inv.toNatTrans.app ((g.2.app a.1).toFunctor.obj x) =
      (b.2.mapComp f.1 (Quiver.Hom.op ZZ)).inv.toNatTrans.app ((g.2.app a.1).toFunctor.obj x) ≫
        (b.2.map₂ (η.1 ▷ Quiver.Hom.op ZZ)).toNatTrans.app ((g.2.app a.1).toFunctor.obj x) := by
    apply (Iso.comp_inv_eq ((Cat.Hom.toNatIso (b.2.mapComp g.1 (Quiver.Hom.op ZZ))).app
      ((g.2.app a.1).toFunctor.obj x))).mpr
    erw [Category.assoc]
    apply (Iso.eq_inv_comp ((Cat.Hom.toNatIso (b.2.mapComp f.1 (Quiver.Hom.op ZZ))).app
      ((g.2.app a.1).toFunctor.obj x))).mpr
    exact hmc.symm
  -- hnn_inv: slide map₂ (η.1 ▷ ZZ.op) past g.2.naturality (inverse form), point x
  have hnn_inv : (b.2.map₂ (η.1 ▷ Quiver.Hom.op ZZ)).toNatTrans.app
        ((g.2.app a.1).toFunctor.obj x) ≫
      (g.2.naturality (g.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app x =
      (g.2.naturality (f.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app x ≫
        (g.2.app γ).toFunctor.map ((a.2.map₂ (η.1 ▷ Quiver.Hom.op ZZ)).toNatTrans.app x) := by
    apply (Iso.comp_inv_eq ((Cat.Hom.toNatIso (g.2.naturality (g.1 ≫ Quiver.Hom.op ZZ))).app x)).mpr
    erw [Category.assoc]
    apply (Iso.eq_inv_comp ((Cat.Hom.toNatIso
      (g.2.naturality (f.1 ≫ Quiver.Hom.op ZZ))).app x)).mpr
    exact hnn.symm
  rw [Functor.map_comp]
  erw [Category.assoc]
  erw [reassoc_of% hmc_inv]
  erw [Category.assoc]
  erw [hnn_inv]
  -- remaining η.2 coherences
  have hη2 := (η.2.as.app γ).toNatTrans.naturality
    ((a.2.map₂ (op2 (ZZ ◁ η.1.unop2))).toNatTrans.app x)
  have hMCinv := (b.2.mapComp f.1 (Quiver.Hom.op ZZ)).inv.toNatTrans.naturality
    ((η.2.as.app a.1).toNatTrans.app x)
  dsimp at hmod hη2 hMCinv
  -- hmod_inv: slide mfZZ.map P past g.2.naturality → f.2.naturality (modification), point x
  have hmod_inv : (b.2.map (f.1 ≫ Quiver.Hom.op ZZ)).toFunctor.map
        ((η.2.as.app a.1).toNatTrans.app x) ≫
      (g.2.naturality (f.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app x =
      (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ)).inv.toNatTrans.app x ≫
        (η.2.as.app γ).toNatTrans.app ((a.2.map (f.1 ≫ Quiver.Hom.op ZZ)).toFunctor.obj x) := by
    apply (Iso.comp_inv_eq ((Cat.Hom.toNatIso (g.2.naturality (f.1 ≫ Quiver.Hom.op ZZ))).app x)).mpr
    erw [Category.assoc]
    apply (Iso.eq_inv_comp ((Cat.Hom.toNatIso
      (f.2.naturality (f.1 ≫ Quiver.Hom.op ZZ))).app x)).mpr
    exact hmod.symm
  erw [reassoc_of% hMCinv, reassoc_of% hmod_inv]
  erw [Category.assoc, ← hη2, ← Category.assoc]
  rfl

/--
The *backward strong transformation* `yonedaEvaluation ⟶ yonedaPairing` for the Yoneda lemma.

At each pair `x = (b₀, F)`, the component functor is `yonedaLemmaBackwardsFunctor x`, the
Yoneda embedding functor sending `s : F.obj b₀` to the strong transformation
`(a, f) ↦ (F.map f).obj s`.

This is the inverse direction of the Yoneda equivalence.  Together with `yonedaLemmaForwards`
and the unit/counit isos (`yonedaHomInvId`, `yonedaInvHomId`), it forms `yonedaLemma`.
-/
def yonedaLemmaBackwards : StrongTrans (@yonedaEvaluation B _)  (@yonedaPairing B _) where
  app x := {toFunctor := yonedaLemmaBackwardsFunctor x}
  naturality {a b} f :=
    Cat.Hom.isoMk (NatIso.ofComponents (fun X ↦ backwardsNaturalityIso f X)
      (fun {X Y} f₁ ↦ backwards_naturality_iso_natural f f₁))
  naturality_naturality {a b f g} η := by
    apply Cat.Hom₂.ext_app
    intro X
    obtain ⟨x⟩ := X
    simp only [Cat.Hom.toNatTrans_comp, NatTrans.comp_app, Cat.whiskerLeft_toNatTrans,
      Cat.whiskerRight_toNatTrans, whiskerLeft_app, whiskerRight_app,
      yonedaEvaluation_map₂_app_down, Cat.Hom.isoMk_hom, Cat.toCatHom₂_toNatTrans,
      NatIso.ofComponents_hom_app]
    apply homCategory.ext
    intro γ
    erw [homCategory_comp_as_app, homCategory_comp_as_app]
    apply Cat.Hom₂.ext_app
    intro ZZ
    dsimp only [backwardsNaturalityIso, backwardsNaturalityIsoApp]
    simp only [Cat.Hom.toNatTrans_comp, NatTrans.comp_app, isoMk_hom_as_app, Cat.Hom.isoMk_hom,
      Cat.toCatHom₂_toNatTrans, NatIso.ofComponents_hom_app, Iso.trans_hom, Iso.symm_hom,
      Iso.app_hom, Cat.Hom.toNatIso]
    erw [backwards_map_comp]
    simp only [yonedaPairing_map₂]
    simp only [NatTrans.toCatHom₂_toNatTrans]
    dsimp only [yonedaPairingMap₂, yonedaPairingMapFunctor, Functor.whiskerLeft,
      Functor.whiskerRight, precomposing, postcomposing, precomposingCat, postcomposingCat,
      postcomposing₂]
    erw [homCategory_comp_as_app]
    simp only [Cat.Hom.toNatTrans_comp, NatTrans.comp_app, Cat.whiskerRight_toNatTrans,
      whiskerRight_app, whiskerRight_as_app, Cat.toCatHom₂_toNatTrans]
    simp only [precomp_map, postcomp₂, postcomposingCat, postcomp_obj,
      Pseudofunctor.StrongTrans.comp_app, Functor.comp_map, Cat.Hom.comp_toFunctor]
    dsimp only [yonedaLemmaBackwardsFunctor, backwardsTrans,
      backwardsFibreFunctor, yonedaEvaluation']
    simp only [Cat.whiskerLeft_toNatTrans, whiskerLeft_app, whiskerLeft_as_app]
    exact backwards_naturality_naturality_core η x ZZ
  naturality_id a := by sorry
  naturality_comp {a b c} f g := by sorry

end Biyoneda
