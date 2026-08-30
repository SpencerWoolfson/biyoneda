/-
Copyright (c) 2026 Spencer Woolfson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Spencer Woolfson
-/
import Biyoneda.Pairing

/-!
# The backward direction: the component functor

At a fixed pair `x = (b₀, F)`, `yonedaLemmaBackwardsFunctor x` sends an object `s : F.obj b₀`
to the strong transformation `(a, f) ↦ (F.map f).obj s`.  It is built in three layers:

* `backwardsFibreFunctor` — the component of that transformation at one `a : Bᵒᵖ`;
* `backwardsTransData` — those components as pointwise `StrongTransIntoCats` data;
* `backwardsTrans` — the strong transformation, via `StrongTransIntoCats.toStrongTrans`;
* `yonedaLemmaBackwardsFunctor` — and that, functorially in `s`.

`mapComp_id_app` and `mapComp_assoc_app` are general facts about any pseudofunctor evaluated at
an object, used by `backwardsTrans`'s coherence fields.

The naturality machinery is in `Biyoneda/BackwardsNaturality.lean`.
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

The evaluation point is typed `↑(x.2.obj x.1)` rather than `↑(yonedaEvaluation'.obj x)`.  The
two are `rfl`-equal, but the latter spelling drags `evaluationPseudo`'s parked coherence fields
into every declaration downstream *through the type*, contaminating the whole backwards chain
with `sorryAx` for no mathematical reason.
-/
@[simp]
def backwardsFibreFunctor (x : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat))
    (eval : ↑(x.2.obj x.1)) (a : Bᵒᵖ) :
    ↑((yoneda₀ (unop x.1)).obj a) ⥤ ↑(x.2.obj a) where
  obj b := (x.2.map (Quiver.Hom.op b)).toFunctor.obj eval
  map {X Y} f := (x.2.map₂ (op2 f)).toNatTrans.app eval
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

/-- Padding-free component form of `mapComp_assoc_right_hom`.

`mapComp_assoc_app` above is stated in the shape `StrongTrans`'s whiskered `naturality_comp`
obligation asks for, which pads the right-hand side with three identities.  The pointwise
`StrongTransIntoCats` obligation has no padding, so it wants this form. -/
lemma mapComp_assoc_app' (F : Bᵒᵖ ⥤ᵖ Cat.{w, v}) {b₀ : B} {a b c : Bᵒᵖ}
    (f : a ⟶ b) (g : b ⟶ c) (X : unop a ⟶ b₀) (eval : ↑(F.obj (op b₀))) :
    (F.mapComp (Quiver.Hom.op X) (f ≫ g)).hom.toNatTrans.app eval ≫
      (F.mapComp f g).hom.toNatTrans.app ((F.map (Quiver.Hom.op X)).toFunctor.obj eval) =
    (F.map₂ (op2 (α_ g.unop f.unop X).hom)).toNatTrans.app eval ≫
      (F.mapComp (Quiver.Hom.op X ≫ f) g).hom.toNatTrans.app eval ≫
        (F.map g).toFunctor.map
          ((F.mapComp (Quiver.Hom.op X) f).hom.toNatTrans.app eval) := by
  simpa using mapComp_assoc_app F f g X eval

/--
At a fixed pair `x = (b₀, F)` and an evaluation point `eval : F.obj b₀`, the Yoneda element
`yoneda₀ b₀ ⟶ F` **as pointwise `StrongTransIntoCats` data**.

Every obligation is stated in the fibre `↑(x.2.obj a)` -- a plain functor-category equation --
rather than as a `Cat` 2-cell, which is what lets all four fields close in one line each:

* `naturality`'s own square is `mapComp_naturality_left`;
* `naturality_naturality'` is `mapComp_naturality_right`;
* `naturality_id'` is `mapComp_id_app`, unpadded;
* `naturality_comp'` is `mapComp_assoc_app'`.

The hand-rolled `StrongTrans` this replaces had to descend through `Cat.Hom.isoMk` first, and
its naturality square was parked on a `congr 1` that over-descended into `HEq` goals.
-/
def backwardsTransData (x : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat)) (eval : ↑(x.2.obj x.1)) :
    StrongTransIntoCats (yoneda₀ (unop x.1)) x.2 where
  app a := backwardsFibreFunctor x eval a
  naturality {a b} f :=
    NatIso.ofComponents
      (fun X ↦ (Cat.Hom.toNatIso (x.2.mapComp (Quiver.Hom.op X) f)).app eval)
      (fun {X Y} g ↦
        Cat.Hom₂.congr_app (x.2.toOplax.mapComp_naturality_left (op2 g) f) eval)
  naturality_naturality' {a b} {f g} η X :=
    Cat.Hom₂.congr_app (x.2.toOplax.mapComp_naturality_right (Quiver.Hom.op X) η) eval
  naturality_id' a X := by
    have key := mapComp_id_app x.2 X eval
    simp only [Category.id_comp, Category.comp_id] at key
    exact key
  naturality_comp' {a b c} f g X := mapComp_assoc_app' x.2 f g X eval

/--
At a fixed pair `x = (b₀, F)` and an evaluation point `eval : F.obj b₀`, the strong
transformation `yoneda₀ b₀ ⟶ F` corresponding to `eval` under the Yoneda embedding.

* **Component at `a`**: the functor `backwardsFibreFunctor x eval a`, which
  sends `f : unop a ⟶ b₀` to `(F.map f).obj eval`.
* **Naturality at `f : a ⟶ b`**: an isomorphism built from the associativity coherence
  `F.mapComp`, whose hom component at `X` is `(F.mapComp (op X) f).hom.app eval`.

This is the "Yoneda element" — the object in `yonedaPairing.obj x` that
`yonedaLemmaBackwardsFunctor` sends `eval` to.

`StrongTransIntoCats.toStrongTrans` supplies the crossing, so nothing here is hand-rolled: the
result is `rfl`-equal to the previous hand-written structure and every field is proved.
-/
@[simp]
def backwardsTrans (x : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat))
    (eval : ↑(x.2.obj x.1)) : Pseudofunctor.StrongTrans (yoneda₀ (unop x.1)) x.2 :=
  (backwardsTransData x eval).toStrongTrans

/-- The component of `backwardsTrans`, at the functor level.

`backwardsTrans` is now a `StrongTransIntoCats.toStrongTrans`, so `simp [backwardsTrans]` no
longer exposes `backwardsFibreFunctor`.  Reason through this instead of unfolding the def. -/
@[simp] lemma backwardsTrans_app_toFunctor (x : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat)) (eval : ↑(x.2.obj x.1))
    (a : Bᵒᵖ) :
    ((backwardsTrans x eval).app a).toFunctor = backwardsFibreFunctor x eval a := rfl

set_option backward.isDefEq.respectTransparency false in
/--
At a fixed pair `x = (b₀, F)`, the *Yoneda embedding functor*
`F.obj b₀ ⥤ StrongTrans (yoneda₀ b₀) F`.

* **On objects**: sends an element `eval : F.obj b₀` to the strong transformation
  `backwardsTrans x eval`, whose `a`-component sends
  `f : unop a ⟶ b₀` to `(F.map f).obj eval`.
* **On morphisms**: sends a morphism `g : eval ⟶ eval'` to the modification whose
  `c`-component has, at each `X`, the morphism `(F.map (op X)).map g`.

This is the component functor of the strong transformation `yonedaLemmaBackwards`.
-/
@[simp]
def yonedaLemmaBackwardsFunctor (x : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat)) :
    yonedaEvaluation'.obj x ⥤ yonedaPairing.obj x where
  obj a := backwardsTrans x a
  map {a b} f := by
    refine { as := { app := ?_, naturality := ?_ } }
    · intro c
      refine { toNatTrans := { app := ?_, naturality := ?_ } }
      · exact fun X ↦ (x.2.map (Quiver.Hom.op X)).toFunctor.map f
      · intro X Y g
        simp only [backwardsTrans_app_toFunctor, backwardsFibreFunctor, op_unop,
          NatTrans.naturality]
    · intro t u g
      refine Cat.Hom₂.ext_iff.mpr ?_
      ext c
      rw [Cat.Hom.toNatTrans_comp, Cat.Hom.toNatTrans_comp]
      simp only [backwardsTrans_app_toFunctor, backwardsFibreFunctor, op_unop,
        Cat.Hom.comp_toFunctor, comp_obj, Cat.whiskerLeft_toNatTrans,
        Cat.Hom.isoMk_hom, NatTrans.toCatHom₂_toNatTrans, Cat.whiskerRight_toNatTrans]
      exact (x.2.mapComp (Quiver.Hom.op c) g).hom.toNatTrans.naturality f
  map_id X := by
    apply homCategory.ext
    intro c
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext W
    exact (x.2.map (Quiver.Hom.op W)).toFunctor.map_id _
  map_comp {X Y Z} f g := by
    apply homCategory.ext
    intro c
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext W
    exact (x.2.map (Quiver.Hom.op W)).toFunctor.map_comp _ _

end Biyoneda
