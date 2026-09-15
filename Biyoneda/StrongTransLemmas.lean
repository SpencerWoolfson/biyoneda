/-
Copyright (c) 2026 Spencer Woolfson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Spencer Woolfson
-/
module

public import Biyoneda.ForMathlib

/-!
# Strong transformations into `Cat`, at a point

General lemmas about strong transformations between `Cat`-valued pseudofunctors, stated at a
point in the fibre.  Nothing here mentions the Yoneda development or the evaluation
pseudofunctor; `C` is an arbitrary bicategory.

They were split out of `Biyoneda/Evaluation.lean` on 2026-09-07, where they had grown up
interleaved with `evaluationPseudo`'s own coherence proofs.  The split is along the seam the
upstreaming plan needs: this file is one PR's worth of general API, and what remains in
`Evaluation.lean` is another.

## What is here

* **Spelling bridges** — `(𝟙 F).app a` does not elaborate through dot notation, so the identity
  and composite transformations' components have to be named in the spelling that does.
* **`naturality` at a point**, in the directions Mathlib does not generate: the composite's
  (`comp_naturality_app` and its inverse), the slide-and-cancel form, and the associativity
  coherence (`naturality_comp_assoc_core`) that both directions of the Yoneda equivalence reduce
  to. The conjugated form is the 2-cell lemma `Pseudofunctor.StrongTrans.naturality_naturality_conj`
  in `ForMathlib.lean`, and `naturality_comp` inverted is Mathlib's `naturality_comp_inv_app`.
* **Two folds `simp` will not do** — `map_comp_cancel` and `map_map_comp`.  `← Functor.map_comp`
  is the wrong direction for the default simp set and loops if added to it, so the fold has to
  be named.
* A few `Cat` shape lemmas that the above rest on.

## Upstreaming note

These belong in three different places upstream — the `Functor` folds under
`CategoryTheory/Functor/`, the `Cat` shape lemmas beside the strictness lemmas in
`Biyoneda/ForMathlib.lean`'s target, and the rest with `StrongTrans`.  They are kept together
here because that is how they are *used*; subdivide at PR time, not before.
-/

@[expose] public section

namespace CategoryTheory.Bicategory

open CategoryTheory _root_.CategoryTheory.Bicategory Pseudofunctor StrongTrans
  _root_.CategoryTheory.Functor
open scoped Pseudofunctor.StrongTrans

universe u v w

variable {C : Type u} [Bicategory.{w, v} C]
variable {x y z t : C} {E F G H : C ⥤ᵖ Cat.{w, v}}

lemma cat_unitor_block {X Y Z : Cat.{v, u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((ρ_ f).hom ≫ (λ_ f).inv) ▷ g = 𝟙 (f ≫ g) := by aesop_cat

/-! ### Spelling bridges

`(𝟙 F).app a` **does not elaborate at all** through dot notation: `𝟙 F` presents as
`CategoryStruct.toQuiver.1 F F`, which the elaborator will not treat as a `StrongTrans`, so the
bridge cannot even be stated that way.  Written with *explicit application*,
`StrongTrans.app (𝟙 F) a`, it elaborates and is `rfl`.

Being `rfl` is what matters: these are 1-morphisms sitting in the *types* of the surrounding
2-cells, so `simp` can never rewrite them — its motive is not type-correct — but `dsimp` can,
because it preserves definitional equality.  Use them with `dsimp only`.

They are deliberately **not** `@[simp]`: as rewrite rules in the wrong phase they destabilise
the ambient simp set.  Mathlib has `StrongTrans.categoryStruct_id_app` and friends, but stated
in the dot-notation form, which is exactly the form that does not fire here. -/

/-- `StrongTrans.categoryStruct_id_app` in the spelling that elaborates. -/
lemma strongTrans_id_app (F : C ⥤ᵖ Cat.{w, v}) (a : C) :
    StrongTrans.app (𝟙 F) a = 𝟙 (F.obj a) := rfl

/-- `StrongTrans.comp_app` in the spelling that elaborates. -/
lemma strongTrans_comp_app (η : F ⟶ G) (θ : G ⟶ H) (a : C) :
    StrongTrans.app (η ≫ θ) a = StrongTrans.app η a ≫ StrongTrans.app θ a := rfl

/-- The left unitor of the pseudofunctor bicategory, componentwise. -/
lemma strongTrans_leftUnitor_app (α : F ⟶ G) (a : C) :
    ((λ_ α).hom).as.app a = (λ_ (StrongTrans.app α a)).hom := rfl

/-- The right unitor of the pseudofunctor bicategory, componentwise. -/
lemma strongTrans_rightUnitor_app (α : F ⟶ G) (a : C) :
    ((ρ_ α).hom).as.app a = (ρ_ (StrongTrans.app α a)).hom := rfl

/-- The naturality constraint of the identity strong transformation. -/
lemma strongTrans_id_naturality_hom (F : C ⥤ᵖ Cat.{w, v}) (u : x ⟶ y) :
    (StrongTrans.naturality (𝟙 F) u).hom = (ρ_ (F.map u)).hom ≫ (λ_ (F.map u)).inv := rfl

/-- The identity strong transformation's naturality, whiskered, is the identity 2-cell.
The RHS spelling is pinned to the normalised form; without that pin the `𝟙 _` elaborates at the
un-normalised type and nothing matches. -/
lemma strongTrans_id_naturality_whiskerRight (u : x ⟶ y) (α : F ⟶ G) :
    ((StrongTrans.naturality (𝟙 F) u) ▷ᵢ α.app y).hom = 𝟙 (F.map u ≫ α.app y) := by
  simp only [whiskerRightIso_hom, strongTrans_id_naturality_hom]
  exact cat_unitor_block (F.map u) (α.app y)

lemma cat_whiskerLeft_leftUnitor {X Y Z : Cat.{v, u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ◁ (λ_ g).hom = 𝟙 (f ≫ g) := by aesop_cat

lemma strongTrans_id_app_toFunctor_map (F : C ⥤ᵖ Cat.{w, v}) (a : C)
    {p q : ↑(F.obj a)} (h : p ⟶ q) : ((StrongTrans.app (𝟙 F) a)).toFunctor.map h = h := rfl

/-- Component form of `strongTrans_id_naturality_whiskerRight`. -/
lemma strongTrans_id_naturality_whiskerRight_app (u : x ⟶ y) (α : F ⟶ G) (W : ↑(F.obj x)) :
    ((StrongTrans.naturality (𝟙 F) u) ▷ᵢ α.app y).hom.toNatTrans.app W = 𝟙 _ := by
  rw [strongTrans_id_naturality_whiskerRight]; aesop_cat

/-- Component form of `cat_whiskerLeft_leftUnitor`. -/
lemma cat_whiskerLeft_leftUnitor_app {X' Y' Z' : Cat.{v, u}} (f : X' ⟶ Y') (g : Y' ⟶ Z')
    (W : ↑X') : (f ◁ (λ_ g).hom).toNatTrans.app W = 𝟙 _ := by
  rw [cat_whiskerLeft_leftUnitor]; aesop_cat

/-- Cancel an adjacent inverse/forward pair sitting **under a functor's `.map`**.

`simp` cancels a bare adjacent inv/hom pair happily, but it will not fold through the functor
first, because
`← Functor.map_comp` is the wrong direction for the default simp set and cannot be added to it
without looping against the forward rule.  So the fold has to be named.  Taking the cancellation
as a hypothesis rather than an `Iso` keeps the statement first-order: the goals here spell the
pair as `(…).inv.toNatTrans.app Z`, whose head is `NatTrans.app`, so an `e.inv`-shaped pattern
would never unify. -/
@[reassoc]
lemma map_comp_cancel {D E : Type*} [Category D] [Category E] (P : D ⥤ E) {a b : D}
    (A : a ⟶ b) (B : b ⟶ a) (h : A ≫ B = 𝟙 a) :
    P.map A ≫ P.map B = 𝟙 (P.obj a) := by
  rw [← Functor.map_comp, h, Functor.map_id]

/-- The naturality of a **composite** strong transformation, at a point.

`(δ ≫ α).naturality f` is an associator sandwich around `δ`'s and `α`'s; in `Cat` the three
associators are identities definitionally, so this is `rfl` once they are written in, and the
padding comes off with `simp`.  Without it the composite's naturality sits in the goal as an
opaque five-factor block that no distribution lemma will touch. -/
lemma strongTrans_comp_naturality_app (δ : F ⟶ G) (α : G ⟶ H) {a b : C} (f : a ⟶ b)
    (W : ↑(F.obj a)) :
    ((δ ≫ α).naturality f).hom.toNatTrans.app W
      = (α.app b).toFunctor.map ((δ.naturality f).hom.toNatTrans.app W) ≫
        (α.naturality f).hom.toNatTrans.app ((δ.app a).toFunctor.obj W) := by
  have h : ((δ ≫ α).naturality f).hom.toNatTrans.app W
      = (𝟙 _) ≫ (α.app b).toFunctor.map ((δ.naturality f).hom.toNatTrans.app W) ≫ (𝟙 _) ≫
        (α.naturality f).hom.toNatTrans.app ((δ.app a).toFunctor.obj W) ≫ (𝟙 _) := rfl
  simpa using h

/-- Fold two nested `.map` layers across a composition.  The one-layer version is
`← Functor.map_comp`, which cannot be a simp lemma (wrong direction, loops against the forward
rule); this is its two-layer companion, and `@[reassoc]` supplies the right-associated form the
goals actually carry. -/
@[reassoc]
lemma map_map_comp {D E W : Type*} [Category D] [Category E] [Category W]
    (Q : D ⥤ E) (P : E ⥤ W) {a b c : D} (A : a ⟶ b) (B : b ⟶ c) :
    P.map (Q.map A) ≫ P.map (Q.map B) = P.map (Q.map (A ≫ B)) := by
  rw [← Functor.map_comp, ← Functor.map_comp]

/-- Slide a morphism through `α.naturality v` and cancel the pair: the conjugation form for the
naturality **isomorphism** itself, as opposed to `naturality_naturality_conj_app`, which is the
one for `map₂`.  This is what collapses the `hom … inv` sandwich the associator core produces. -/
@[reassoc]
lemma strongTrans_naturality_slide (α : G ⟶ H) {a b : C} (v : a ⟶ b) {W W' : ↑(G.obj a)}
    (m : W ⟶ W') :
    (α.naturality v).hom.toNatTrans.app W ≫
        (H.map v).toFunctor.map ((α.app a).toFunctor.map m) ≫
        (α.naturality v).inv.toNatTrans.app W'
      = (α.app b).toFunctor.map ((G.map v).toFunctor.map m) := by
  have h := (α.naturality v).hom.toNatTrans.naturality m
  dsimp at h
  rw [← Category.assoc, ← h, Category.assoc]
  simp

/-- The naturality of a **composite** strong transformation at a point, in inverse form.
`strongTrans_comp_naturality_app` gives the forward direction; inverting a composite reverses
it, and the cleanest way to say so is to invert the whole `Iso` rather than the equation. -/
lemma strongTrans_comp_naturality_inv_app (δ : F ⟶ G) (α : G ⟶ H) {a b : C} (f : a ⟶ b)
    (W : ↑(F.obj a)) :
    ((δ ≫ α).naturality f).inv.toNatTrans.app W
      = (α.naturality f).inv.toNatTrans.app ((δ.app a).toFunctor.obj W) ≫
        (α.app b).toFunctor.map ((δ.naturality f).inv.toNatTrans.app W) := by
  have key : (Cat.Hom.toNatIso ((δ ≫ α).naturality f)).app W
      = (α.app b).toFunctor.mapIso ((Cat.Hom.toNatIso (δ.naturality f)).app W) ≪≫
        (Cat.Hom.toNatIso (α.naturality f)).app ((δ.app a).toFunctor.obj W) :=
    Iso.ext (strongTrans_comp_naturality_app δ α f W)
  exact congrArg Iso.inv key

/-- The associativity coherence a strong transformation's `naturality` satisfies against the
two pseudofunctors' `mapComp`s, at a point.

Three 1-cells and one transformation: it says that transporting `x` along `u ≫ v` and then `W`
agrees with transporting along `u` and then `v ≫ W`, once both are corrected by the `mapComp`
constraints.  Both `naturality_comp` obligations of the Yoneda equivalence come down to this.

The proof is four moves: `simp` turns `F.map₂ (α_ u v W).hom` into `F`'s own `mapComp`
associativity (`map₂_associator`); then three applications of Mathlib's
`naturality_comp_inv_app`, each followed by the `hom`/`inv` cancellations it exposes,
strip the `G`-side coherences; what is left is one naturality square of `(α.naturality W).inv`. -/
lemma naturality_comp_assoc_core (α : F ⟶ G) {p q r s : C} (u : p ⟶ q) (v : q ⟶ r) (W : r ⟶ s)
    (x : ↑(F.obj p)) :
    ((G.map W).toFunctor.map ((α.naturality (u ≫ v)).hom.toNatTrans.app x) ≫
        (G.mapComp (u ≫ v) W).inv.toNatTrans.app ((α.app p).toFunctor.obj x) ≫
          (α.naturality ((u ≫ v) ≫ W)).inv.toNatTrans.app x) ≫
      (α.app s).toFunctor.map ((F.map₂ (α_ u v W).hom).toNatTrans.app x) =
    (G.map W).toFunctor.map
        ((α.app r).toFunctor.map ((F.mapComp u v).hom.toNatTrans.app x) ≫
          (α.naturality v).hom.toNatTrans.app ((F.map u).toFunctor.obj x)) ≫
      (G.mapComp v W).inv.toNatTrans.app
          ((α.app q).toFunctor.obj ((F.map u).toFunctor.obj x)) ≫
        (G.map (v ≫ W)).toFunctor.map ((α.naturality u).hom.toNatTrans.app x) ≫
          (G.mapComp u (v ≫ W)).inv.toNatTrans.app ((α.app p).toFunctor.obj x) ≫
            (α.naturality (u ≫ v ≫ W)).inv.toNatTrans.app x := by
  simp
  rw [Pseudofunctor.StrongTrans.naturality_comp_inv_app_assoc α (u ≫ v) W x,
    Cat.Hom.inv_hom_id_toNatTrans_app_assoc,
    map_comp_cancel_assoc (G.map W).toFunctor
      ((α.naturality (u ≫ v)).hom.toNatTrans.app x)
      ((α.naturality (u ≫ v)).inv.toNatTrans.app x)
      (Cat.Hom.hom_inv_id_toNatTrans_app (α.naturality (u ≫ v)) _),
    map_comp_cancel_assoc (α.app s).toFunctor
      ((F.mapComp (u ≫ v) W).inv.toNatTrans.app x)
      ((F.mapComp (u ≫ v) W).hom.toNatTrans.app x)
      (Cat.Hom.inv_hom_id_toNatTrans_app (F.mapComp (u ≫ v) W) _)]
  rw [Pseudofunctor.StrongTrans.naturality_comp_inv_app α u (v ≫ W) x,
    Cat.Hom.inv_hom_id_toNatTrans_app_assoc,
    map_comp_cancel_assoc (G.map (v ≫ W)).toFunctor
      ((α.naturality u).hom.toNatTrans.app x)
      ((α.naturality u).inv.toNatTrans.app x)
      (Cat.Hom.hom_inv_id_toNatTrans_app (α.naturality u) _)]
  rw [Pseudofunctor.StrongTrans.naturality_comp_inv_app_assoc α v W ((F.map u).toFunctor.obj x),
    Cat.Hom.inv_hom_id_toNatTrans_app_assoc,
    map_comp_cancel_assoc (G.map W).toFunctor
      ((α.naturality v).hom.toNatTrans.app ((F.map u).toFunctor.obj x))
      ((α.naturality v).inv.toNatTrans.app ((F.map u).toFunctor.obj x))
      (Cat.Hom.hom_inv_id_toNatTrans_app (α.naturality v) _)]
  have hfin : (G.map W).toFunctor.map
        ((α.app r).toFunctor.map ((F.mapComp u v).hom.toNatTrans.app x)) ≫
      (α.naturality W).inv.toNatTrans.app
        ((F.map v).toFunctor.obj ((F.map u).toFunctor.obj x))
      = (α.naturality W).inv.toNatTrans.app ((F.map (u ≫ v)).toFunctor.obj x) ≫
        (α.app s).toFunctor.map
          ((F.map W).toFunctor.map ((F.mapComp u v).hom.toNatTrans.app x)) :=
    (α.naturality W).inv.toNatTrans.naturality _
  rw [reassoc_of% hfin]

/-- The same conjugation for a modification's naturality. -/
lemma modification_naturality_conj {α α' : F ⟶ G} (Γ : α ⟶ α') {a b : C} (f : a ⟶ b)
    (W : ↑(F.obj a)) :
    (Γ.as.app b).toNatTrans.app ((F.map f).toFunctor.obj W)
      = (α.naturality f).hom.toNatTrans.app W ≫
        (G.map f).toFunctor.map ((Γ.as.app a).toNatTrans.app W) ≫
        (α'.naturality f).inv.toNatTrans.app W := by
  have h := modification_naturality_app Γ f W
  rw [← Category.assoc]
  exact (Iso.eq_comp_inv ((Cat.Hom.toNatIso (α'.naturality f)).app W)).mpr h

end CategoryTheory.Bicategory
