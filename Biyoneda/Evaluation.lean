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

/-! ### The five coherence laws

OPEN.  Each is stated exactly as the corresponding `Pseudofunctor` field, instantiated at an
explicit pair, and each is verified to plug into that field by `exact`.  Measured to fail:
`simp`, `cat_disch`, `bicategory`, `simp; bicategory`, `simp [categoryStruct_id_app,
categoryStruct_id_naturality_hom]`, and `dsimp only [categoryStruct_id_app]; simp`. -/

/-- Left-unitor coherence for `evaluationPseudo`. -/
lemma eval_left_unitor (u : x ⟶ y) (α : F ⟶ G) :
    evalMap₂ (λ_ u).hom (λ_ α).hom
      = (evalMapComp (𝟙 x) (𝟙 F) u α).hom ≫
        (F.mapId x).hom ▷ evalMap u α ≫ (λ_ (evalMap u α)).hom := by
  sorry

/-- Right-unitor coherence for `evaluationPseudo`.  Its content is `α.naturality (𝟙 y)` against
the two `mapId`s. -/
lemma eval_right_unitor (u : x ⟶ y) (α : F ⟶ G) :
    evalMap₂ (ρ_ u).hom (ρ_ α).hom
      = (evalMapComp u α (𝟙 y) (𝟙 G)).hom ≫
        evalMap u α ◁ (G.mapId y).hom ≫ (ρ_ (evalMap u α)).hom := by
  sorry

/-- Left-whiskering coherence for `evaluationPseudo`. -/
lemma eval_whisker_left (u : x ⟶ y) (α : F ⟶ G) {v v' : y ⟶ z} {β β' : G ⟶ H}
    (σ : v ⟶ v') (Γ : β ⟶ β') :
    evalMap₂ (u ◁ σ) (α ◁ Γ)
      = (evalMapComp u α v β).hom ≫ evalMap u α ◁ evalMap₂ σ Γ ≫
        (evalMapComp u α v' β').inv := by
  sorry

/-- Right-whiskering coherence for `evaluationPseudo`. -/
lemma eval_whisker_right {u u' : x ⟶ y} {α α' : F ⟶ G} (σ : u ⟶ u') (Γ : α ⟶ α')
    (v : y ⟶ z) (β : G ⟶ H) :
    evalMap₂ (σ ▷ v) (Γ ▷ β)
      = (evalMapComp u α v β).hom ≫ evalMap₂ σ Γ ▷ evalMap v β ≫
        (evalMapComp u' α' v β).inv := by
  sorry

/-- Associator coherence for `evaluationPseudo`.  The largest of the five: three `mapComp`s and
two `naturality` slides to align, with `F.map₂_associator` as its input. -/
lemma eval_associator (s : x ⟶ y) (δ : F ⟶ G) (u : y ⟶ z) (α : G ⟶ H)
    (v : z ⟶ t) (β : H ⟶ E) :
    evalMap₂ (α_ s u v).hom (α_ δ α β).hom
      = (evalMapComp (s ≫ u) (δ ≫ α) v β).hom ≫
        (evalMapComp s δ u α).hom ▷ evalMap v β ≫
        (α_ (evalMap s δ) (evalMap u α) (evalMap v β)).hom ≫
        evalMap s δ ◁ (evalMapComp u α v β).inv ≫
        (evalMapComp s δ (u ≫ v) (α ≫ β)).inv := by
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
