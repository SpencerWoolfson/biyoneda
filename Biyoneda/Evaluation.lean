/-
Copyright (c) 2026 Spencer Woolfson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Spencer Woolfson
-/
import Mathlib.CategoryTheory.Bicategory.Product
import Mathlib.CategoryTheory.Functor.Currying
import Biyoneda.ForMathlib

/-!
# The evaluation pseudofunctor

For a bicategory `C`, this file constructs the **evaluation pseudofunctor**

  `evaluationPseudo : C × (C ⥤ᵖ Cat) ⥤ᵖ Cat`,   `(c, F) ↦ F.obj c`,

the bicategorical analogue of Mathlib's `CategoryTheory.evaluationUncurried`, which is currently
missing from the `Bicategory` library.  Nothing here is specific to the Yoneda lemma: `C` is an
arbitrary bicategory.  The bicategorical Yoneda development uses the instance `C := Bᵒᵖ`.

## Implementation notes

### Which diagonal

The action on 1-morphisms fills a square in one of two ways.  This file uses **Mathlib's**
choice, matching `evaluationUncurried`:

```
map f = x.2.map f.1 ≫ f.2.app y.1
```

The other diagonal, `f.2.app x.1 ≫ y.2.map f.1`, is what this file used before 2026-08-28.  The
two are isomorphic but not equal: for a strong transformation `f.2` they are related by
`f.2.naturality f.1`, which is an iso and not an identity.  They agree in a 1-category, where
naturality is an equation, which is why Mathlib's choice looks arbitrary there and is not here.

The switch was made for alignment with Mathlib and for eventual upstreaming.  It is **not** a
simplification: the coherence budget is symmetric.  Measured on `mapComp`, both diagonals need
exactly one `mapComp` of a component pseudofunctor and one strong-transformation `naturality`
slide.  The only asymmetries found are cosmetic and are recorded at the two component lemmas at
the end of this file.

### Why the target is `Cat` and not a general `D`

The target bicategory is fixed to `Cat` rather than an arbitrary bicategory `D`.  This is not
incidental: the `mapId` field is `x.2.mapId x.1`, which typechecks only because `Cat` is a
`Bicategory.Strict` and so a unitor reduces definitionally.  Over a general `D` the field needs
an explicit unitor, which changes the term and is a separate (non-definitional) construction.

Note the diagonal switch moves which unitor is being leaned on.  The old diagonal needed
`𝟙 ≫ f`; this one needs `f ≫ 𝟙`.  See the comment at `mapId`.
-/

namespace CategoryTheory.Bicategory

open CategoryTheory Bicategory Pseudofunctor StrongTrans Functor
open scoped Pseudofunctor.StrongTrans

universe u v w

variable {C : Type u} [Bicategory.{w, v} C]


/-!
## Assembly from Mathlib parts

`evaluationPseudo`'s action on hom-categories is not hand-rolled: it is the composite of three
gadgets that already exist upstream.  The `rfl` bridges below record that the structure fields
agree with the assembly *definitionally*, so a fact proved about `evalHom` can be used at
`evaluationPseudo` with `exact`, and no downstream spelling moves.
-/

/-- Evaluation at a fixed object `a`, as a **strict** pseudofunctor `(C ⥤ᵖ Cat) ⥤ᵖ Cat`.

This is the honest statement that the pseudofunctor variable of `evaluationPseudo` carries no
coherence content: `η ↦ η.app a` preserves identities and composition on the nose, so `mapId`
and `mapComp` are `eqToIso` and all five coherence laws come from `StrictPseudofunctor.mk'`.
All of the genuine content of `evaluationPseudo` therefore lives in the `C` variable. -/
def evalAt (a : C) : StrictPseudofunctor (C ⥤ᵖ Cat.{w, v}) Cat.{w, v} := .mk'
  { obj F := F.obj a
    map η := η.app a
    map₂ Γ := Γ.as.app a
    -- `simp` reduces each to `X = eqToHom _ ≫ X`, where the `eqToHom` sits at a *defeq* but not
    -- syntactically equal pair of endpoints (`(η ≫ θ).app a` vs `η.app a ≫ θ.app a`), so
    -- `eqToHom_refl` cannot match it.  `exact` closes the gap: proof irrelevance makes the
    -- coercion definitionally `𝟙`, and `exact` unifies at default transparency where `rfl`
    -- on the raw goal does not.
    map₂_whisker_left := by intros; simp; exact (Category.id_comp _).symm
    map₂_whisker_right := by intros; simp; exact (Category.id_comp _).symm }

/-- The hom-functor of `evaluationPseudo`, assembled from Mathlib's own gadgets:

* `PrelaxFunctor.mapFunctor` in the `C` variable,
* `Pseudofunctor.StrongTrans.appFunctor` in the pseudofunctor variable,
* composition in `Cat` as a bifunctor, `Functor.uncurry.obj (precomposing …)`.

The domain is the hom-category of `C × (C ⥤ᵖ Cat)`, which `Bicategory.prod` defines to be
literally `CategoryTheory.prod'` of the two factors' hom-categories — so `Functor.prod` and
`Functor.uncurry` apply directly, with no instance diamond. -/
def evalHom (x y : C × (C ⥤ᵖ Cat.{w, v})) : (x ⟶ y) ⥤ (x.2.obj x.1 ⟶ y.2.obj y.1) :=
  ((x.2.mapFunctor x.1 y.1).prod (Pseudofunctor.StrongTrans.appFunctor x.2 y.2 y.1)) ⋙
    Functor.uncurry.obj (precomposing (x.2.obj x.1) (x.2.obj y.1) (y.2.obj y.1))


/-!
## The constraint data as named parts, and the five coherence laws

The five pseudofunctor coherence laws cannot be proved *inside* the structure: there, every
object is a projection of a product (`a.2`, `(𝟙 a).1`, ...), and the goal ends up carrying two
spellings of the same identity 1-morphism — one from the field's own type, one introduced by
`simp` rewriting `λ_`.  Because that is a 1-morphism sitting in the *types* of the surrounding
2-cells, no rewrite can fix it: `simp`'s motive is not type-correct, `dsimp` declines, and the
bridge `(𝟙 a).1 = 𝟙 a.1` does not even elaborate (`𝟙 a` presents as `CategoryStruct.toQuiver.1
a a`, which the elaborator will not project).  See notes/evaluation_phase2_parked.md.

The fix is the standalone-lemma pattern: name the constraint data, state the five laws about the
names in clean variables where `𝟙 F` is unambiguous, and plug them in with `exact`.  Each plug
below is definitionally the field it fills, so nothing downstream moves — `evaluationPseudo_map_eq`
and `evaluationPseudo_map₂_eq` are still `rfl`.
-/

section Parts

variable {x y z t : C} {E F G H : C ⥤ᵖ Cat.{w, v}}

/-- The action of evaluation on 1-morphisms, in clean variables. -/
abbrev evalMap (u : x ⟶ y) (α : F ⟶ G) : F.obj x ⟶ G.obj y := F.map u ≫ α.app y

/-- The action of evaluation on 2-morphisms, in clean variables. -/
abbrev evalMap₂ {u u' : x ⟶ y} {α α' : F ⟶ G} (σ : u ⟶ u') (Γ : α ⟶ α') :
    evalMap u α ⟶ evalMap u' α' :=
  (F.map₂ σ ▷ α.app y) ≫ (F.map u' ◁ Γ.as.app y)

/-- The composition constraint of evaluation, in clean variables: one `mapComp` of the source
pseudofunctor and one strong-transformation `naturality` slide, glued by associators. -/
def evalMapComp (u : x ⟶ y) (α : F ⟶ G) (v : y ⟶ z) (β : G ⟶ H) :
    F.map (u ≫ v) ≫ (α.app z ≫ β.app z) ≅ evalMap u α ≫ evalMap v β :=
  (F.mapComp u v) ▷ᵢ (α.app z ≫ β.app z) ≪≫
  (α_ (F.map u) (F.map v) (α.app z ≫ β.app z)) ≪≫
  (F.map u) ◁ᵢ ((α_ (F.map v) (α.app z) (β.app z)).symm ≪≫
    ((α.naturality v) ▷ᵢ (β.app z)) ≪≫
    (α_ (α.app y) (G.map v) (β.app z))) ≪≫
  (α_ (F.map u) (α.app y) (G.map v ≫ β.app z)).symm

/-! ### `Cat` is strict, definitionally

Every associator and unitor of the bicategory `Cat` is the *identity* 2-cell, by `rfl`.  That is
what makes the coherence residuals collapse: they are built entirely from `α_`, `λ_`, `ρ_`, and
in `Cat` those are not merely invertible but definitionally trivial.  `simp only` with these six
turns any structural block into identities.  Mathlib records `Cat`'s strictness as a `Strict`
instance, whose `associator_eqToIso` and friends go through `eqToIso` -- a strictly weaker
statement than these.

Deliberately **not** `@[simp]`: measured 2026-08-29, tagging them globally changes the simp
normal form enough to break `BackwardsFunctor.lean:69`.  Cite them explicitly. -/

lemma cat_associator_hom {X Y Z W : Cat.{v, u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) :
    (α_ f g h).hom = 𝟙 _ := rfl
lemma cat_associator_inv {X Y Z W : Cat.{v, u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) :
    (α_ f g h).inv = 𝟙 _ := rfl
lemma cat_leftUnitor_hom {X Y : Cat.{v, u}} (f : X ⟶ Y) : (λ_ f).hom = 𝟙 f := rfl
lemma cat_leftUnitor_inv {X Y : Cat.{v, u}} (f : X ⟶ Y) : (λ_ f).inv = 𝟙 f := rfl
lemma cat_rightUnitor_hom {X Y : Cat.{v, u}} (f : X ⟶ Y) : (ρ_ f).hom = 𝟙 f := rfl
lemma cat_rightUnitor_inv {X Y : Cat.{v, u}} (f : X ⟶ Y) : (ρ_ f).inv = 𝟙 f := rfl

lemma cat_id_comp {X Y : Cat.{v, u}} {f g : X ⟶ Y} (η : f ⟶ g) : 𝟙 f ≫ η = η := by simp
lemma cat_comp_id {X Y : Cat.{v, u}} {f g : X ⟶ Y} (η : f ⟶ g) : η ≫ 𝟙 g = η := by simp
lemma cat_id_whiskerRight {X Y Z : Cat.{v, u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    𝟙 f ▷ g = 𝟙 (f ≫ g) := by simp
lemma cat_whiskerLeft_id {X Y Z : Cat.{v, u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ◁ 𝟙 g = 𝟙 (f ≫ g) := rfl

lemma bicat_id_comp {B : Type*} [Bicategory B] {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
    𝟙 f ≫ η = η := Category.id_comp η
lemma bicat_comp_id {B : Type*} [Bicategory B] {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
    η ≫ 𝟙 g = η := Category.comp_id η
lemma bicat_id_whiskerRight {B : Type*} [Bicategory B] {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    𝟙 f ▷ g = 𝟙 (f ≫ g) := Bicategory.id_whiskerRight f g
lemma bicat_whiskerLeft_id {B : Type*} [Bicategory B] {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    f ◁ 𝟙 g = 𝟙 (f ≫ g) := Bicategory.whiskerLeft_id f g

lemma cat_unitor_block {X Y Z : Cat.{v, u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((ρ_ f).hom ≫ (λ_ f).inv) ▷ g = 𝟙 (f ≫ g) := by aesop_cat

/-! ### Spelling bridges

The obstruction described above is that `(𝟙 F).app a` will not reduce.  The reason it resisted
every tactic is narrower than it looked: **the dot notation `(𝟙 F).app a` does not elaborate at
all** — `𝟙 F` presents as `CategoryStruct.toQuiver.1 F F`, which the elaborator will not treat as
a `StrongTrans`, so the bridge could not even be stated.  Written with *explicit application*,
`StrongTrans.app (𝟙 F) a`, it elaborates and is `rfl`.

Being `rfl` is what matters: these are 1-morphisms sitting in the *types* of the surrounding
2-cells, so `simp` can never rewrite them (its motive is not type-correct), but `dsimp` can,
because it preserves definitional equality.  Use them with `dsimp only`, via `eval_norm` below.

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

/-- Evaluation of an identity 1-morphism of the product: the second factor contributes nothing. -/
lemma evalMap_id_id (x : C) (F : C ⥤ᵖ Cat.{w, v}) : evalMap (𝟙 x) (𝟙 F) = F.map (𝟙 x) := rfl

/-! ### Shape lemmas for `evalMapComp`

A nested `≪≫` does not distribute on its own, so the constraint iso is opaque to rewriting until
its `hom` and `inv` are named.  Both of these are needed before any of the five cores can be
attacked componentwise. -/

/-- `evalMapComp`'s forward direction, with the `≪≫` chain distributed. -/
lemma evalMapComp_hom (u : x ⟶ y) (α : F ⟶ G) (v : y ⟶ z) (β : G ⟶ H) :
    (evalMapComp u α v β).hom
      = (F.mapComp u v).hom ▷ (α.app z ≫ β.app z) ≫
        (α_ (F.map u) (F.map v) (α.app z ≫ β.app z)).hom ≫
        F.map u ◁ ((α_ (F.map v) (α.app z) (β.app z)).inv ≫
          (α.naturality v).hom ▷ β.app z ≫
          (α_ (α.app y) (G.map v) (β.app z)).hom) ≫
        (α_ (F.map u) (α.app y) (G.map v ≫ β.app z)).inv := rfl

/-- `evalMapComp`'s inverse direction, with the `≪≫` chain distributed. -/
lemma evalMapComp_inv (u : x ⟶ y) (α : F ⟶ G) (v : y ⟶ z) (β : G ⟶ H) :
    (evalMapComp u α v β).inv
      = (α_ (F.map u) (α.app y) (G.map v ≫ β.app z)).hom ≫
        F.map u ◁ ((α_ (α.app y) (G.map v) (β.app z)).inv ≫
          (α.naturality v).inv ▷ β.app z ≫
          (α_ (F.map v) (α.app z) (β.app z)).hom) ≫
        (α_ (F.map u) (F.map v) (α.app z ≫ β.app z)).inv ≫
        (F.mapComp u v).inv ▷ (α.app z ≫ β.app z) := by
  simp [evalMapComp]

/-- The other filling of the `map₂` square, by interchange.  Sometimes the more convenient
orientation: it puts the modification component leftmost. -/
lemma evalMap₂_eq_exchange {u u' : x ⟶ y} {α α' : F ⟶ G} (σ : u ⟶ u') (Γ : α ⟶ α') :
    evalMap₂ σ Γ = (F.map u ◁ Γ.as.app y) ≫ (F.map₂ σ ▷ α'.app y) := by
  simp [whisker_exchange]


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

/-! ### Shape lemmas specialised at an identity

`evalMapComp_hom` above is stated for general arguments, so rewriting with it at `𝟙 F`
*re-introduces* the `(𝟙 F).app y` spelling that the bridges just removed — the rewrite undoes
the normalisation.  These four are the same facts already specialised, so no rewrite can put the
bad spelling back.  All four are `rfl`, which is only possible because of the bridges above. -/

/-- `evalMapComp` with an identity in the first slot, already normalised. -/
lemma evalMapComp_id_left_hom (u : x ⟶ y) (α : F ⟶ G) :
    (evalMapComp (𝟙 x) (𝟙 F) u α).hom
      = (F.mapComp (𝟙 x) u).hom ▷ (𝟙 (F.obj y) ≫ α.app y) ≫
        (α_ (F.map (𝟙 x)) (F.map u) (𝟙 (F.obj y) ≫ α.app y)).hom ≫
        F.map (𝟙 x) ◁ ((α_ (F.map u) (𝟙 (F.obj y)) (α.app y)).inv ≫
          ((ρ_ (F.map u)).hom ≫ (λ_ (F.map u)).inv) ▷ α.app y ≫
          (α_ (𝟙 (F.obj x)) (F.map u) (α.app y)).hom) ≫
        (α_ (F.map (𝟙 x)) (𝟙 (F.obj x)) (F.map u ≫ α.app y)).inv := rfl

/-- `evalMapComp` with an identity in the second slot, already normalised. -/
lemma evalMapComp_id_right_hom (u : x ⟶ y) (α : F ⟶ G) :
    (evalMapComp u α (𝟙 y) (𝟙 G)).hom
      = (F.mapComp u (𝟙 y)).hom ▷ (α.app y ≫ 𝟙 (G.obj y)) ≫
        (α_ (F.map u) (F.map (𝟙 y)) (α.app y ≫ 𝟙 (G.obj y))).hom ≫
        F.map u ◁ ((α_ (F.map (𝟙 y)) (α.app y) (𝟙 (G.obj y))).inv ≫
          (α.naturality (𝟙 y)).hom ▷ 𝟙 (G.obj y) ≫
          (α_ (α.app y) (G.map (𝟙 y)) (𝟙 (G.obj y))).hom) ≫
        (α_ (F.map u) (α.app y) (G.map (𝟙 y) ≫ 𝟙 (G.obj y))).inv := rfl

/-- The left-hand side of `eval_left_unitor`, already normalised. -/
lemma evalMap₂_leftUnitor (u : x ⟶ y) (α : F ⟶ G) :
    evalMap₂ (λ_ u).hom (λ_ α).hom
      = F.map₂ (λ_ u).hom ▷ (𝟙 (F.obj y) ≫ α.app y) ≫
        F.map u ◁ (λ_ (α.app y)).hom := rfl

/-- The left-hand side of `eval_right_unitor`, already normalised. -/
lemma evalMap₂_rightUnitor (u : x ⟶ y) (α : F ⟶ G) :
    evalMap₂ (ρ_ u).hom (ρ_ α).hom
      = F.map₂ (ρ_ u).hom ▷ (α.app y ≫ 𝟙 (G.obj y)) ≫
        F.map u ◁ (ρ_ (α.app y)).hom := rfl

/-- Component form of `strongTrans_id_naturality_whiskerRight`. -/
lemma strongTrans_id_naturality_whiskerRight_app (u : x ⟶ y) (α : F ⟶ G) (W : ↑(F.obj x)) :
    ((StrongTrans.naturality (𝟙 F) u) ▷ᵢ α.app y).hom.toNatTrans.app W = 𝟙 _ := by
  rw [strongTrans_id_naturality_whiskerRight]; aesop_cat

/-- Component form of `cat_whiskerLeft_leftUnitor`. -/
lemma cat_whiskerLeft_leftUnitor_app {X' Y' Z' : Cat.{v, u}} (f : X' ⟶ Y') (g : Y' ⟶ Z')
    (W : ↑X') : (f ◁ (λ_ g).hom).toNatTrans.app W = 𝟙 _ := by
  rw [cat_whiskerLeft_leftUnitor]; aesop_cat

/-! ### The five coherence laws

The two unitors are **closed** (2026-08-30).  What broke them open was not a stronger tactic but
a change of shape: stop normalising `Cat`'s unitors and associators away, and instead write them
into the statement of a `rfl` bridge as the identities they definitionally are.  See
`eval_left_unitor` for the four-step recipe.

The three remaining -- `eval_whisker_left`, `eval_whisker_right`, `eval_associator` -- are still
open, and the same recipe is the thing to try on them.  Historical note for those: measured to
fail are `simp`, `cat_disch`, `bicategory`, `simp; bicategory`, `simp [categoryStruct_id_app,
categoryStruct_id_naturality_hom]`, and `dsimp only [categoryStruct_id_app]; simp`. -/

/-- The right-hand side of `eval_left_unitor`, distributed at a point, with every `Cat` unitor
and associator left in place as the identity it definitionally is.

This is the move that breaks the wall.  The `cat_*` lemmas above say `(λ_ f).hom = 𝟙 f`, and
firing one leaves the goal internally inconsistent at reducible transparency (see the note on
those lemmas).  Writing the identities into the *statement* instead means nothing has to fire:
the bridge is `rfl`, and `simp` then finishes on a goal that is already in the fibre and no
longer contains a unitor to stumble over. -/
lemma eval_left_unitor_rhs_app (u : x ⟶ y) (α : F ⟶ G) (Z : ↑(F.obj x)) :
    (((F.mapComp (𝟙 x) u).hom ▷ (𝟙 (F.obj y) ≫ α.app y) ≫
        (α_ (F.map (𝟙 x)) (F.map u) (𝟙 (F.obj y) ≫ α.app y)).hom ≫
        F.map (𝟙 x) ◁ ((α_ (F.map u) (𝟙 (F.obj y)) (α.app y)).inv ≫
          ((ρ_ (F.map u)).hom ≫ (λ_ (F.map u)).inv) ▷ α.app y ≫
          (α_ (𝟙 (F.obj x)) (F.map u) (α.app y)).hom) ≫
        (α_ (F.map (𝟙 x)) (𝟙 (F.obj x)) (F.map u ≫ α.app y)).inv) ≫
      (F.mapId x).hom ▷ evalMap u α ≫ (λ_ (evalMap u α)).hom).toNatTrans.app Z
    = ((𝟙 (F.obj y) ≫ α.app y).toFunctor.map ((F.mapComp (𝟙 x) u).hom.toNatTrans.app Z) ≫
        (𝟙 _) ≫
        ((𝟙 _) ≫ (α.app y).toFunctor.map ((𝟙 _) ≫ (𝟙 _)) ≫ (𝟙 _)) ≫
        (𝟙 _)) ≫
      (evalMap u α).toFunctor.map ((F.mapId x).hom.toNatTrans.app Z) ≫ (𝟙 _) := rfl

/-- Left-unitor coherence for `evaluationPseudo`.

The whole mathematical content is `F.map₂_left_unitor`; everything else is `Cat` structure.
The proof shape that works -- and that the other four cores should follow -- is:

1. rewrite the three `rfl` shape lemmas, so both sides are fully explicit;
2. descend to a fibre with `Cat.Hom₂.ext_app` **before** any `simp`;
3. bridge the side `simp` cannot distribute, with the identities written into the statement;
4. let `simp` finish, now that no unitor has to be rewritten.

Step 3 is the one that matters.  Earlier attempts normalised the unitors away with
`simp only [cat_leftUnitor_hom, ...]` first and were dead on arrival. -/
lemma eval_left_unitor (u : x ⟶ y) (α : F ⟶ G) :
    evalMap₂ (λ_ u).hom (λ_ α).hom
      = (evalMapComp (𝟙 x) (𝟙 F) u α).hom ≫
        (F.mapId x).hom ▷ evalMap u α ≫ (λ_ (evalMap u α)).hom := by
  rw [evalMap₂_leftUnitor, evalMapComp_id_left_hom, F.map₂_left_unitor]
  apply Cat.Hom₂.ext_app; intro Z
  refine Eq.trans ?_ (eval_left_unitor_rhs_app u α Z).symm
  simp

/-- `StrongTrans.naturality_id` at a point, unpadded.

Mathlib states it whiskered, with a left and a right unitor between the factors; in `Cat` both
are identities.  Same treatment as everywhere else in this section: two `rfl` bridges carrying
the residual `𝟙`s, then `simpa` to strip them. -/
lemma strongTrans_naturality_id_app (α : F ⟶ G) (a : C) (W : ↑(F.obj a)) :
    (α.app a).toFunctor.map ((F.mapId a).hom.toNatTrans.app W)
      = (α.naturality (𝟙 a)).hom.toNatTrans.app W ≫
        (G.mapId a).hom.toNatTrans.app ((α.app a).toFunctor.obj W) := by
  have h := Cat.Hom₂.congr_app (α.naturality_id a) W
  have hl : ((α.naturality (𝟙 a)).hom ≫ α.app a ◁ (G.mapId a).hom).toNatTrans.app W
      = (α.naturality (𝟙 a)).hom.toNatTrans.app W ≫
        (G.mapId a).hom.toNatTrans.app ((α.app a).toFunctor.obj W) := rfl
  have hr : ((F.mapId a).hom ▷ α.app a ≫
        (λ_ (α.app a)).hom ≫ (ρ_ (α.app a)).inv).toNatTrans.app W
      = (α.app a).toFunctor.map ((F.mapId a).hom.toNatTrans.app W) ≫ (𝟙 _) ≫ (𝟙 _) := rfl
  simpa using hr.symm.trans (h.symm.trans hl)

/-- The right-hand side of `eval_right_unitor`, distributed at a point.  Companion of
`eval_left_unitor_rhs_app`; see the note there for why the identities stay in the statement. -/
lemma eval_right_unitor_rhs_app (u : x ⟶ y) (α : F ⟶ G) (Z : ↑(F.obj x)) :
    (((F.mapComp u (𝟙 y)).hom ▷ (α.app y ≫ 𝟙 (G.obj y)) ≫
        (α_ (F.map u) (F.map (𝟙 y)) (α.app y ≫ 𝟙 (G.obj y))).hom ≫
        F.map u ◁ ((α_ (F.map (𝟙 y)) (α.app y) (𝟙 (G.obj y))).inv ≫
          (α.naturality (𝟙 y)).hom ▷ 𝟙 (G.obj y) ≫
          (α_ (α.app y) (G.map (𝟙 y)) (𝟙 (G.obj y))).hom) ≫
        (α_ (F.map u) (α.app y) (G.map (𝟙 y) ≫ 𝟙 (G.obj y))).inv) ≫
      evalMap u α ◁ (G.mapId y).hom ≫ (ρ_ (evalMap u α)).hom).toNatTrans.app Z
    = ((α.app y ≫ 𝟙 (G.obj y)).toFunctor.map ((F.mapComp u (𝟙 y)).hom.toNatTrans.app Z) ≫
        (𝟙 _) ≫
        ((𝟙 _) ≫
            (α.naturality (𝟙 y)).hom.toNatTrans.app ((F.map u).toFunctor.obj Z) ≫ (𝟙 _)) ≫
        (𝟙 _)) ≫
      (G.mapId y).hom.toNatTrans.app ((evalMap u α).toFunctor.obj Z) ≫ (𝟙 _) := rfl

/-- Right-unitor coherence for `evaluationPseudo`.

Same four-step shape as `eval_left_unitor`, with one extra ingredient: unlike the left unitor
this one has genuine content beyond `F.map₂_right_unitor`, namely `α.naturality_id` -- which
`simp` picks up from `strongTrans_naturality_id_app` once the bridge has cleared the unitors
out of the way. -/
lemma eval_right_unitor (u : x ⟶ y) (α : F ⟶ G) :
    evalMap₂ (ρ_ u).hom (ρ_ α).hom
      = (evalMapComp u α (𝟙 y) (𝟙 G)).hom ≫
        evalMap u α ◁ (G.mapId y).hom ≫ (ρ_ (evalMap u α)).hom := by
  rw [evalMap₂_rightUnitor, evalMapComp_id_right_hom, F.map₂_right_unitor]
  apply Cat.Hom₂.ext_app; intro Z
  refine Eq.trans ?_ (eval_right_unitor_rhs_app u α Z).symm
  simp [strongTrans_naturality_id_app]

/-! ### Shared machinery for the three remaining cores

`evalMapComp`'s two directions, distributed at a point.  These are the general-argument
companions of the identity-specialised shape lemmas above, and they are what `simp` cannot
produce on its own: it reduces everything around them and then stops at
`(evalMapComp _ _ _ _).hom.toNatTrans.app Z`.  Both carry `Cat`'s associators as the identities
they definitionally are, per the recipe on `eval_left_unitor`. -/

/-- `evalMapComp`'s forward direction at a point. -/
lemma evalMapComp_hom_app (u : x ⟶ y) (α : F ⟶ G) (v : y ⟶ z) (β : G ⟶ H) (Z : ↑(F.obj x)) :
    (evalMapComp u α v β).hom.toNatTrans.app Z
      = (α.app z ≫ β.app z).toFunctor.map ((F.mapComp u v).hom.toNatTrans.app Z) ≫
        (𝟙 _) ≫
        ((𝟙 _) ≫ (β.app z).toFunctor.map
            ((α.naturality v).hom.toNatTrans.app ((F.map u).toFunctor.obj Z)) ≫ (𝟙 _)) ≫
        (𝟙 _) := rfl

/-- `evalMapComp`'s inverse direction at a point.  Unlike the forward one this is not `rfl`
from the definition -- `evalMapComp_inv` has to distribute the `≪≫` chain first -- so it is
`congrArg` of that, then a `rfl` bridge. -/
lemma evalMapComp_inv_app (u : x ⟶ y) (α : F ⟶ G) (v : y ⟶ z) (β : G ⟶ H) (Z : ↑(F.obj x)) :
    (evalMapComp u α v β).inv.toNatTrans.app Z
      = (𝟙 _) ≫
        ((𝟙 _) ≫ (β.app z).toFunctor.map
            ((α.naturality v).inv.toNatTrans.app ((F.map u).toFunctor.obj Z)) ≫ (𝟙 _)) ≫
        (𝟙 _) ≫
        (α.app z ≫ β.app z).toFunctor.map ((F.mapComp u v).inv.toNatTrans.app Z) := by
  have hb : ((α_ (F.map u) (α.app y) (G.map v ≫ β.app z)).hom ≫
        F.map u ◁ ((α_ (α.app y) (G.map v) (β.app z)).inv ≫
          (α.naturality v).inv ▷ β.app z ≫
          (α_ (F.map v) (α.app z) (β.app z)).hom) ≫
        (α_ (F.map u) (F.map v) (α.app z ≫ β.app z)).inv ≫
        (F.mapComp u v).inv ▷ (α.app z ≫ β.app z)).toNatTrans.app Z
      = (𝟙 _) ≫
        ((𝟙 _) ≫ (β.app z).toFunctor.map
            ((α.naturality v).inv.toNatTrans.app ((F.map u).toFunctor.obj Z)) ≫ (𝟙 _)) ≫
        (𝟙 _) ≫
        (α.app z ≫ β.app z).toFunctor.map ((F.mapComp u v).inv.toNatTrans.app Z) := rfl
  exact (congrArg (fun m ↦ m.toNatTrans.app Z) (evalMapComp_inv u α v β)).trans hb

/-- `StrongTrans.naturality_naturality` solved for the bare `map₂` image: the conjugated form
is what the whisker cores need, since there the `naturality` iso appears on both sides. -/
lemma strongTrans_naturality_conj (α : F ⟶ G) {v v' : y ⟶ z} (σ : v ⟶ v') (W : ↑(F.obj y)) :
    (α.app z).toFunctor.map ((F.map₂ σ).toNatTrans.app W)
      = (α.naturality v).hom.toNatTrans.app W ≫
        (G.map₂ σ).toNatTrans.app ((α.app y).toFunctor.obj W) ≫
        (α.naturality v').inv.toNatTrans.app W := by
  have h := α.naturality_naturality_app σ W
  rw [← Category.assoc]
  exact (Iso.eq_comp_inv ((Cat.Hom.toNatIso (α.naturality v')).app W)).mpr h

/-- Cancel an adjacent inverse/forward pair sitting **under a functor's `.map`**.

`simp` cancels a bare adjacent inv/hom pair happily -- it does so on the other side of
`eval_whisker_right` -- but it will not fold through the functor first, because
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

/-- `StrongTrans.naturality_comp` at a point, in **inverse** form.

Mathlib's `naturality_comp_hom_app` gives the forward direction; the whisker/associator cores
meet the reverse one, and inverting a five-factor equation in place is exactly the kind of
rewriting the `Cat` diamond blocks.  Stated once here with `f`, `g` and `α` abstract. -/
lemma strongTrans_naturality_comp_inv_app (α : F ⟶ G) {a b c : C} (f : a ⟶ b) (g : b ⟶ c)
    (W : ↑(F.obj a)) :
    (G.mapComp f g).inv.toNatTrans.app ((α.app a).toFunctor.obj W) ≫
        (α.naturality (f ≫ g)).inv.toNatTrans.app W
      = (G.map g).toFunctor.map ((α.naturality f).inv.toNatTrans.app W) ≫
        (α.naturality g).inv.toNatTrans.app ((F.map f).toFunctor.obj W) ≫
        (α.app c).toFunctor.map ((F.mapComp f g).inv.toNatTrans.app W) := by
  have h := Cat.Hom₂.congr_app (α.naturality_comp f g) W
  simp only [Cat.Hom.toNatTrans_comp, NatTrans.comp_app, Cat.whiskerLeft_toNatTrans,
    Cat.whiskerRight_toNatTrans, whiskerLeft_app, whiskerRight_app] at h
  -- `Cat`'s three associators are identities definitionally; write them in rather than
  -- normalising them away (see the recipe on `eval_left_unitor`), then strip them here.
  have hb : (α.app c).toFunctor.map ((F.mapComp f g).hom.toNatTrans.app W) ≫
        (α_ (F.map f) (F.map g) (α.app c)).hom.toNatTrans.app W ≫
          (α.naturality g).hom.toNatTrans.app ((F.map f).toFunctor.obj W) ≫
            (α_ (F.map f) (α.app b) (G.map g)).inv.toNatTrans.app W ≫
              (G.map g).toFunctor.map ((α.naturality f).hom.toNatTrans.app W) ≫
                (α_ (α.app a) (G.map f) (G.map g)).hom.toNatTrans.app W
      = (α.app c).toFunctor.map ((F.mapComp f g).hom.toNatTrans.app W) ≫ (𝟙 _) ≫
          (α.naturality g).hom.toNatTrans.app ((F.map f).toFunctor.obj W) ≫ (𝟙 _) ≫
            (G.map g).toFunctor.map ((α.naturality f).hom.toNatTrans.app W) ≫ (𝟙 _) := rfl
  rw [hb] at h
  simp only [Category.id_comp, Category.comp_id] at h
  -- now invert the whole equation at the `Iso` level, where reversal is structural
  have key :
      ((Cat.Hom.toNatIso (α.naturality (f ≫ g))).app W ≪≫
          (Cat.Hom.toNatIso (G.mapComp f g)).app ((α.app a).toFunctor.obj W))
        = ((α.app c).toFunctor.mapIso ((Cat.Hom.toNatIso (F.mapComp f g)).app W) ≪≫
            (Cat.Hom.toNatIso (α.naturality g)).app ((F.map f).toFunctor.obj W) ≪≫
              (G.map g).toFunctor.mapIso ((Cat.Hom.toNatIso (α.naturality f)).app W)) :=
    Iso.ext h
  simpa using congrArg Iso.inv key

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

/-- Left-whiskering coherence for `evaluationPseudo`.

Follows the `eval_left_unitor` recipe with the general bridges above.  Note the `rw` rather
than a `simp` argument for `strongTrans_naturality_conj`: as a simp lemma it also fires on the
right-hand side's `β'` and the two sides diverge.  `rw` takes the first occurrence, which is
the left-hand side's `F.map₂ σ`, and that is the only one that needs rewriting. -/
lemma eval_whisker_left (u : x ⟶ y) (α : F ⟶ G) {v v' : y ⟶ z} {β β' : G ⟶ H}
    (σ : v ⟶ v') (Γ : β ⟶ β') :
    evalMap₂ (u ◁ σ) (α ◁ Γ)
      = (evalMapComp u α v β).hom ≫ evalMap u α ◁ evalMap₂ σ Γ ≫
        (evalMapComp u α v' β').inv := by
  apply Cat.Hom₂.ext_app; intro Z
  simp [evalMapComp_hom_app, evalMapComp_inv_app]
  rw [strongTrans_naturality_conj]
  simp

-- The descent below is a `simp` followed by targeted `rw`s, which `linter.flexible` flags.
-- Squeezing it would pin the proof to today's simp normal form -- the failure mode this file's
-- header records from the v4.30 -> v4.33 walk -- and every `rw` after it names an explicit
-- lemma, so drift fails loudly rather than silently.
set_option linter.flexible false in
/-- Right-whiskering coherence for `evaluationPseudo`.

PARKED (2026-08-30), with the prefix below reaching the residual described here.  The bridges
strip both sides down to chains of `(β.app z).toFunctor.map` factors that agree except for
three slides; two of them go through (`strongTrans_naturality_conj` and
`modification_naturality_conj` both fire, and `naturality_comp_hom_app` splits
`α.naturality (u' ≫ v)`).

What blocks it is the *cancellation*.  The right-hand side ends up with the adjacent pair

  (β.app z).map ((G.map v).map (α.naturality u').inv) ≫
  (β.app z).map ((G.map v).map (α.naturality u').hom)

which is an identity, but collapsing it needs `← Functor.map_comp` to fire through **two**
nested `.map` layers.  It fires through the outer one (the analogous `F.mapComp u' v` pair on
the left-hand side does cancel this way) and not the inner one -- the same reducible-transparency
failure this file's `cat_*` note describes, one level down.

Next move: a `rfl` bridge naming the doubly-nested fold, in the spirit of the bridges above --
`(β.app z).map ((G.map v).map A) ≫ (β.app z).map ((G.map v).map B)` against
`(β.app z).map ((G.map v).map (A ≫ B))` -- rather than another `simp only [← Functor.map_comp]`.
Measured to fail: `simp only [← Category.assoc]; simp only [← Functor.map_comp]` iterated four
times, with and without the `inv_hom_id` component lemmas interleaved. -/
lemma eval_whisker_right {u u' : x ⟶ y} {α α' : F ⟶ G} (σ : u ⟶ u') (Γ : α ⟶ α')
    (v : y ⟶ z) (β : G ⟶ H) :
    evalMap₂ (σ ▷ v) (Γ ▷ β)
      = (evalMapComp u α v β).hom ≫ evalMap₂ σ Γ ▷ evalMap v β ≫
        (evalMapComp u' α' v β).inv := by
  apply Cat.Hom₂.ext_app; intro Z
  simp [evalMapComp_hom_app, evalMapComp_inv_app,
    strongTrans_naturality_conj, modification_naturality_conj,
    Pseudofunctor.StrongTrans.naturality_comp_hom_app]
  simp only [← Category.assoc]
  simp only [← Functor.map_comp]
  congr 1
  simp
  rw [map_comp_cancel_assoc (G.map v).toFunctor
    ((α.naturality u').inv.toNatTrans.app Z) ((α.naturality u').hom.toNatTrans.app Z) (by simp)]
  -- 1. slide `F.map₂ σ` through `α.naturality v`
  have h1 := (α.naturality v).hom.toNatTrans.naturality ((F.map₂ σ).toNatTrans.app Z)
  dsimp at h1
  rw [reassoc_of% h1]
  -- 2. `α`'s 2-naturality, conjugated
  rw [strongTrans_naturality_conj]
  -- 3. the conjugation leaves a second one-layer inv/hom pair; split and cancel it
  simp only [Functor.map_comp, Category.assoc]
  rw [map_comp_cancel_assoc (G.map v).toFunctor
    ((α.naturality u').inv.toNatTrans.app Z) ((α.naturality u').hom.toNatTrans.app Z) (by simp)]
  -- 4. slide the modification component through `G.mapComp u' v`
  have h2 := (G.mapComp u' v).inv.toNatTrans.naturality ((Γ.as.app x).toNatTrans.app Z)
  dsimp at h2
  rw [← reassoc_of% h2]
  -- 5. five leading factors now agree; what is left is `α'`'s composition coherence, inverted
  iterate 5 refine congrArg (CategoryStruct.comp _) ?_
  exact strongTrans_naturality_comp_inv_app α' u' v Z

/-- Associator coherence for `evaluationPseudo`.  The largest of the five: three `mapComp`s and
two `naturality` slides to align, with `F.map₂_associator` as its input.

PARKED (2026-08-30).  The bridges above apply and the descent runs, but the residual is
substantially larger than `eval_whisker_right`'s and has not been analysed.  Close that one
first -- the doubly-nested fold it needs is almost certainly needed here too. -/
lemma eval_associator (s : x ⟶ y) (δ : F ⟶ G) (u : y ⟶ z) (α : G ⟶ H)
    (v : z ⟶ t) (β : H ⟶ E) :
    evalMap₂ (α_ s u v).hom (α_ δ α β).hom
      = (evalMapComp (s ≫ u) (δ ≫ α) v β).hom ≫
        (evalMapComp s δ u α).hom ▷ evalMap v β ≫
        (α_ (evalMap s δ) (evalMap u α) (evalMap v β)).hom ≫
        evalMap s δ ◁ (evalMapComp u α v β).inv ≫
        (evalMapComp s δ (u ≫ v) (α ≫ β)).inv := by
  apply Cat.Hom₂.ext_app; intro Z
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    whiskerLeftIso_hom, whiskerRightIso_hom, whiskerLeftIso_inv, whiskerRightIso_inv,
    Cat.Hom.toNatTrans_comp, NatTrans.comp_app, Cat.whiskerLeft_toNatTrans,
    Cat.whiskerRight_toNatTrans, whiskerLeft_app, whiskerRight_app,
    Cat.associator_hom_toNatTrans_app, Cat.associator_inv_toNatTrans_app,
    Cat.Hom.comp_toFunctor, Functor.comp_obj, Category.id_comp, Category.comp_id]
  simp [evalMapComp_hom_app, evalMapComp_inv_app]
  -- PARKED (2026-08-30).  The prefix above is the `evaluationPseudo_mapComp_hom_app` descent
  -- and it runs; the state it reaches is precise enough to name the obstruction.
  --
  -- The LHS distributes COMPLETELY: four factors, each a triple-nested
  -- `(β.app t).map ((α.app t).map ((δ.app t).map …))`, over `F.mapComp (s ≫ u) v`,
  -- `F.mapComp s u`, `F.mapComp u v` and `F.mapComp s (u ≫ v)`.  The first of those four
  -- matches the RHS's first factor already.
  --
  -- What blocks it is one block on the RHS that will not split:
  --     ((α_ (F.map (s ≫ u) ≫ δ.app z ≫ α.app z) (H.map v) (β.app t)).inv ≫
  --       (evalMapComp s δ u α).hom ▷ H.map v ▷ β.app t ≫ …).toNatTrans.app Z
  -- `Cat.Hom.toNatTrans_comp` and `NatTrans.comp_app` are both in the set above and neither
  -- fires on it -- the `Cat` composition diamond, one layer in from where the rest of the goal
  -- lives.  Running the whole distribution set a SECOND time is measured to make no progress,
  -- so it is at a fixpoint, not merely under-applied.
  --
  -- Next move, and it is the move that closed `eval_whisker_right`: do not widen the simp set.
  -- Add `rfl` component bridges for the two whiskered blocks by name --
  -- `(evalMapComp s δ u α).hom ▷ evalMap v β` and `evalMap s δ ◁ (evalMapComp u α v β).inv`,
  -- each at a point, with `Cat`'s associators written in as the identities they are -- in the
  -- style of `evalMapComp_hom_app`/`evalMapComp_inv_app` just above.  Those two are what the
  -- statement whiskers, and naming them is what lets `simp` past the diamond.
  --
  -- Once distributed, expect the same five-slide shape `eval_whisker_right` had, with
  -- `map_comp_cancel` and `strongTrans_naturality_comp_inv_app` (both proved, above) doing the
  -- same jobs; `δ`'s and `α`'s `naturality_comp` should supply the rest.
  sorry

end Parts

/--
The *evaluation pseudofunctor* `C × (C ⥤ᵖ Cat) ⥤ᵖ Cat.{w, v}`.

This is the right-hand side of the Yoneda equivalence (before universe promotion):

* **On objects**: `(b, F) ↦ F.obj b` — evaluate the pseudofunctor `F` at the object `b`.
* **On 1-morphisms**: `(f : b' ⟶ b, α : F ⟶ G) ↦ F.map f ≫ α.app b`, i.e., map along `f` using
  `F`, then apply the component of `α` at `b`.  This is Mathlib's diagonal; see the module
  docstring.
* **On 2-morphisms**: `(σ, τ) ↦ (F.map₂ σ ▷ α.app b) ≫ (F.map g ◁ τ.as.app b)`.
* **Coherence iso `mapId`**: `F.mapId b`, the identity coherence of `F`.
* **Coherence iso `mapComp`**: built from the associator, `F.mapComp`, and `α.naturality`.

Note: this pseudofunctor lands in the smaller universe `Cat.{w, v}`.  Use `yonedaEvaluation`
(which post-composes with `catPseudoULift`) for the universe-matched version.
-/
def evaluationPseudo : C × (C ⥤ᵖ Cat.{w, v}) ⥤ᵖ Cat.{w, v} where
  obj p := p.2.obj p.1
  map {p q} f := evalMap f.1 f.2
  map₂ {p q f g} η := evalMap₂ η.1 η.2
  mapId p := p.2.mapId p.1
  -- Typechecks only because `Cat` is `Bicategory.Strict`, so `f ≫ 𝟙` reduces definitionally.
  -- The pre-2026-08-28 diagonal needed `𝟙 ≫ f` here instead.
  mapComp {p q r} f g := evalMapComp f.1 f.2 g.1 g.2
  -- Each of the five destructures the product objects, then is exactly one of the cores above.
  map₂_whisker_left := by
    rintro ⟨x, F⟩ ⟨y, G⟩ ⟨z, H⟩ ⟨u, α⟩ ⟨v, β⟩ ⟨v', β'⟩ ⟨σ, Γ⟩
    exact eval_whisker_left u α σ Γ
  map₂_whisker_right := by
    rintro ⟨x, F⟩ ⟨y, G⟩ ⟨z, H⟩ ⟨u, α⟩ ⟨u', α'⟩ ⟨σ, Γ⟩ ⟨v, β⟩
    exact eval_whisker_right σ Γ v β
  map₂_associator := by
    rintro ⟨w, E⟩ ⟨x, F⟩ ⟨y, G⟩ ⟨z, H⟩ ⟨s, δ⟩ ⟨u, α⟩ ⟨v, β⟩
    exact eval_associator s δ u α v β
  map₂_left_unitor := by
    rintro ⟨x, F⟩ ⟨y, G⟩ ⟨u, α⟩
    exact eval_left_unitor u α
  map₂_right_unitor := by
    rintro ⟨x, F⟩ ⟨y, G⟩ ⟨u, α⟩
    exact eval_right_unitor u α

/-!
## The assembly bridges

Every one of these is `rfl`: `evaluationPseudo` and `evalHom` are the same data, so the
Mathlib-gadget vocabulary (`Functor.map_comp`, `Functor.uncurry`, `precomposing`) is available
at `evaluationPseudo` for the cost of an `exact`.  Deliberately **not** `@[simp]`, following the
convention recorded below: cite them explicitly.
-/

section Assembly

variable {x y : C × (C ⥤ᵖ Cat.{w, v})}

/-- `evaluationPseudo`'s hom-functor is `evalHom`, definitionally. -/
lemma evaluationPseudo_mapFunctor (x y : C × (C ⥤ᵖ Cat.{w, v})) :
    (evaluationPseudo (C := C)).toPrelaxFunctor.mapFunctor x y = evalHom x y := rfl

/-- `evaluationPseudo.map` is `evalHom`'s action on objects. -/
lemma evaluationPseudo_map_eq (f : x ⟶ y) :
    (evaluationPseudo (C := C)).map f = (evalHom x y).obj f := rfl

/-- `evaluationPseudo.map₂` is `evalHom`'s action on morphisms.  This is the useful direction:
it puts the two-morphism field under a functor, so `Functor.map_id` / `Functor.map_comp` and the
`Functor.uncurry` simp set apply to it. -/
lemma evaluationPseudo_map₂_eq {f g : x ⟶ y} (η : f ⟶ g) :
    (evaluationPseudo (C := C)).map₂ η = (evalHom x y).map η := rfl

/-- The pseudofunctor variable, evaluated at a fixed object, agrees with `evalAt`. -/
lemma evaluationPseudo_obj_eq_evalAt (a : C) (F : C ⥤ᵖ Cat.{w, v}) :
    (evaluationPseudo (C := C)).obj (a, F) = (evalAt a).obj F := rfl

end Assembly

/-!
## Component API for `evaluationPseudo`

The structure fields of `evaluationPseudo` are large pastings, but every coherence obligation in
practice descends into a fibre, where only the *components* matter.  The lemmas below give those
components in reduced form.

These are deliberately **not** `@[simp]` — see the note in `Biyoneda.ForMathlib`: tagging them
globally adds a match attempt to every bare `simp` in the development.  Cite them explicitly.

Measured 2026-08-28: this API has **no uses outside this file**.  It is kept because the
`mapComp` component lemmas are the intended entry point for the coherence work above, not
because anything currently depends on it.
-/

section API

variable {x y : C × (C ⥤ᵖ Cat.{w, v})}

/-- `evaluationPseudo` on objects: `(c, F) ↦ F.obj c`. -/
lemma evaluationPseudo_obj (x : C × (C ⥤ᵖ Cat.{w, v})) :
    (evaluationPseudo (C := C)).obj x = x.2.obj x.1 := rfl

/-- `evaluationPseudo` on 1-morphisms, on Mathlib's diagonal. -/
lemma evaluationPseudo_map (f : x ⟶ y) :
    (evaluationPseudo (C := C)).map f = x.2.map f.1 ≫ f.2.app y.1 := rfl

/-- `evaluationPseudo`'s unit coherence is that of the first component. -/
lemma evaluationPseudo_mapId (x : C × (C ⥤ᵖ Cat.{w, v})) :
    (evaluationPseudo (C := C)).mapId x = x.2.mapId x.1 := rfl

/-- Point form of `evaluationPseudo_map`. -/
lemma evaluationPseudo_map_obj (f : x ⟶ y) (Z : ↑(x.2.obj x.1)) :
    ((evaluationPseudo (C := C)).map f).toFunctor.obj Z
      = (f.2.app y.1).toFunctor.obj ((x.2.map f.1).toFunctor.obj Z) := rfl

/-- Component of `evaluationPseudo.map₂`. -/
lemma evaluationPseudo_map₂_app {f g : x ⟶ y} (η : f ⟶ g) (Z : ↑(x.2.obj x.1)) :
    ((evaluationPseudo (C := C)).map₂ η).toNatTrans.app Z
      = (f.2.app y.1).toFunctor.map ((x.2.map₂ η.1).toNatTrans.app Z) ≫
        (η.2.as.app y.1).toNatTrans.app ((x.2.map g.1).toFunctor.obj Z) := rfl

/-- Component of `evaluationPseudo.mapId`. -/
lemma evaluationPseudo_mapId_hom_app (x : C × (C ⥤ᵖ Cat.{w, v})) (Z : ↑(x.2.obj x.1)) :
    ((evaluationPseudo (C := C)).mapId x).hom.toNatTrans.app Z
      = (x.2.mapId x.1).hom.toNatTrans.app Z := rfl

/-- Component of `evaluationPseudo.mapComp`, with the strict-`Cat` associator identities
already cancelled: only the source's `mapComp` and the naturality survive.

Cosmetic regression from the diagonal switch, recorded deliberately: on the previous diagonal
the `mapComp` factor was whiskered on the *right* and so appeared as a bare component
`(c.2.mapComp f.1 g.1).hom.app _`.  Here it is whiskered on the left, so it appears under a
`Functor.map`.  Nothing depends on this, but it is one more `Functor.map` for the folding
cascades in the coherence proofs to see past. -/
lemma evaluationPseudo_mapComp_hom_app {a b c : C × (C ⥤ᵖ Cat.{w, v})} (f : a ⟶ b) (g : b ⟶ c)
    (Z : ↑(a.2.obj a.1)) :
    ((evaluationPseudo (C := C)).mapComp f g).hom.toNatTrans.app Z
      = (f.2.app c.1 ≫ g.2.app c.1).toFunctor.map
            ((a.2.mapComp f.1 g.1).hom.toNatTrans.app Z) ≫
        (g.2.app c.1).toFunctor.map
            ((f.2.naturality g.1).hom.toNatTrans.app ((a.2.map f.1).toFunctor.obj Z)) := by
  dsimp only [evaluationPseudo, evalMapComp]
  simp only [Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom, whiskerRightIso_hom,
    Cat.Hom.toNatTrans_comp, NatTrans.comp_app, Cat.whiskerLeft_toNatTrans,
    Cat.whiskerRight_toNatTrans, whiskerLeft_app, whiskerRight_app,
    Cat.associator_hom_toNatTrans_app, Cat.associator_inv_toNatTrans_app,
    Cat.Hom.comp_toFunctor, Functor.comp_obj, Category.id_comp, Category.comp_id]
  -- the `simp only` set above no longer reaches the `≪≫` chain on its own; a full `simp`
  -- does, and the residual is then definitional
  simp
  rfl

/-- Inverse form of `evaluationPseudo_mapComp_hom_app`. -/
lemma evaluationPseudo_mapComp_inv_app {a b c : C × (C ⥤ᵖ Cat.{w, v})} (f : a ⟶ b) (g : b ⟶ c)
    (Z : ↑(a.2.obj a.1)) :
    ((evaluationPseudo (C := C)).mapComp f g).inv.toNatTrans.app Z
      = (g.2.app c.1).toFunctor.map
            ((f.2.naturality g.1).inv.toNatTrans.app ((a.2.map f.1).toFunctor.obj Z)) ≫
        (f.2.app c.1 ≫ g.2.app c.1).toFunctor.map
            ((a.2.mapComp f.1 g.1).inv.toNatTrans.app Z) := by
  dsimp only [evaluationPseudo, evalMapComp]
  simp only [Iso.trans_inv, Iso.symm_inv, whiskerLeftIso_inv, whiskerRightIso_inv,
    Cat.Hom.toNatTrans_comp, NatTrans.comp_app, Cat.whiskerLeft_toNatTrans,
    Cat.whiskerRight_toNatTrans, whiskerLeft_app, whiskerRight_app,
    Cat.associator_hom_toNatTrans_app, Cat.associator_inv_toNatTrans_app,
    Cat.Hom.comp_toFunctor, Functor.comp_obj, Category.id_comp, Category.comp_id]
  simp
  rfl

end API

end CategoryTheory.Bicategory
