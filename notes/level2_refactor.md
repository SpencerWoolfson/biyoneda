# Level 2 refactor — the evaluation pseudofunctor (branch `level2-gadget-refactor`)

**Goal.** The `*_core` lemmas have very long statements. Level 2 asks whether the underlying
pseudofunctors can be *assembled from general gadgets* instead of hand-rolled, so their coherence
obligations are inherited rather than re-proved.

## Finding 1 — Mathlib has no evaluation pseudofunctor

`grep -r evaluation Mathlib/CategoryTheory/Bicategory/` returns **zero hits**. There is no
bicategorical analogue of `CategoryTheory.evaluation`, and no two-variable hom-pseudofunctor.
So Level 2 means *building* the gadget, not reusing one.

## Finding 2 — `yonedaEvaluation'` IS the general evaluation pseudofunctor (verified by `rfl`)

Nothing in the old `yonedaEvaluation'` was Yoneda-specific. Verified in a probe:

```lean
example : (yonedaEvaluation' (B := B)) = evaluationPseudoCat Bᵒᵖ := rfl   -- ✓ compiles
```

Also checked: the whole 627-line region (lines 334–952 of the old `Basic.lean`) contains **no**
`op2`/`unop`/`yoneda₀`/`postcomp₂` — it is entirely `Bᵒᵖ`-agnostic. Generalising `Bᵒᵖ ↦ C`
required **no proof changes whatsoever**.

## Finding 3 — the target bicategory cannot be generalised for free

A fully general `C × (C ⥤ᵖ D) ⥤ᵖ D` does **not** typecheck with the existing `mapId` field:

```
x.2.mapId x.1  has type  x.2.map (𝟙 x.1) ≅ 𝟙 (x.2.obj x.1)
but is expected  (𝟙 x).2.app x.1 ≫ x.2.map (𝟙 x).1 ≅ 𝟙 (x.2.obj x.1)
```

i.e. the hand-rolled definition **silently relies on `Cat` being `Bicategory.Strict`** (the left
unitor `𝟙 ≫ f` reducing definitionally). Inserting an explicit `λ_` typechecks but is then no
longer `rfl`-equal to the old definition. Hence `evaluationPseudo` is general in `C`, `Cat`-valued.
Generalising the target `D` is a separate, non-definitional construction.

## What landed

- `Biyoneda/ForMathlib.lean` — gained the four general helpers formerly in `Basic.lean`
  (`Cat.Hom₂.congr_app`, `Cat.Hom₂.ext_app`, `Cat.toCatHom₂_toNatTrans`,
  `modification_naturality_app`), now inside `namespace CategoryTheory` so dot-notation resolves.
- `Biyoneda/Evaluation.lean` — **new, 663 lines, compiles clean with ZERO sorries.** Contains the
  general `evaluationPseudo : C × (C ⥤ᵖ Cat) ⥤ᵖ Cat` and its five `evaluation_*_core` lemmas,
  all parameterised by an arbitrary bicategory `C`.
- `Biyoneda/Basic.lean` — **2192 → 1555 lines (−637)**; `yonedaEvaluation'` is now
  `evaluationPseudo (C := Bᵒᵖ)`.

## The one regression (open)

`forwards_naturality_comp_core` (`Basic.lean` ~555) no longer closes. Its proof is a delicate
*ordered* `erw`/`iterate` chain, and the term shapes it was tuned against shifted once
`yonedaEvaluation'` became an alias. Symptom: `simp only [← Functor.map_comp]` reports
`simp made no progress`; making that step tolerant just moves the failure one step later
(`erw [Functor.map_id, Category.comp_id]` fails to match).

Tried and **ruled out**: `abbrev`/`@[reducible]` on `yonedaEvaluation'` (to restore the original
unfolding depth) — identical failure, so this is *not* a transparency-depth problem.

Next moves for whoever picks this up:
1. Harvest the goal at the break point (a `trace_state` there already worked once) and re-tune the
   `iterate 6 (first | … )` counts — the count is load-bearing, exactly as it was for
   `map₂_associator` in the earlier golf campaign.
2. Or restate `forwards_naturality_comp_core` against `evaluationPseudo` directly and re-derive.
3. Or (lowest risk, loses the line savings) keep the original `yonedaEvaluation'` body in
   `Basic.lean` and have `Evaluation.lean` carry the general gadget plus an `rfl` bridge lemma.

### Original tactic block, preserved verbatim

```lean
  simp only [← Functor.map_comp]
  simp only [Cat.Hom.comp_toFunctor, Functor.comp_obj]
  iterate erw [Category.comp_id]
  iterate (first
      | erw [Cat.Hom.hom_inv_id_toNatTrans_app]
      | erw [Cat.Hom.inv_hom_id_toNatTrans_app])
  erw [Functor.map_id, Category.comp_id]
  simp only [Functor.map_comp, Category.assoc]
  erw [(g.2.naturality g.1).hom.toNatTrans.naturality]
  have hpush2 := congrArg (g.2.app c.1).toFunctor.map
    ((f.2.naturality g.1).hom.toNatTrans.naturality
      ((Z.naturality f.1).hom.toNatTrans.app (𝟙 (unop a.1))))
  simp only [Cat.Hom.comp_toFunctor, Functor.comp_map, Functor.comp_obj,
    Functor.map_comp] at hpush2
  erw [reassoc_of% hpush2]
  erw [(g.2.naturality g.1).hom.toNatTrans.naturality_assoc]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp]
  have hHead_t : (Z.app c.1).toFunctor.map ((λ_ (f.1 ≫ g.1).unop).hom ≫ (ρ_ (f.1 ≫ g.1).unop).inv) ≫
        (Z.app c.1).toFunctor.map
            (((yoneda₀ (unop a.1)).mapComp f.1 g.1).hom.toNatTrans.app (𝟙 (unop a.1))) ≫
          (Z.naturality g.1).hom.toNatTrans.app
            (((yoneda₀ (unop a.1)).map f.1).toFunctor.obj (𝟙 (unop a.1)))
      = (Z.app c.1).toFunctor.map (
          ((postcompComp₂ g.1.unop f.1.unop).hom.as.app c.1).toNatTrans.app (𝟙 (unop c.1)) ≫
          ((postcomp₂ f.1.unop).app c.1).toFunctor.map
              ((λ_ g.1.unop).hom ≫ (ρ_ g.1.unop).inv) ≫
          ((postcomp₂ f.1.unop).naturality g.1).hom.toNatTrans.app (𝟙 (unop b.1))) ≫
        (Z.app c.1).toFunctor.map
            (((yoneda₀ (unop a.1)).map g.1).toFunctor.map
              ((λ_ f.1.unop).hom ≫ (ρ_ f.1.unop).inv)) ≫
          (Z.naturality g.1).hom.toNatTrans.app
            (((yoneda₀ (unop a.1)).map f.1).toFunctor.obj (𝟙 (unop a.1))) := by
    erw [← Functor.map_comp_assoc]; erw [forwards_naturality_comp_head]
    erw [Functor.map_comp_assoc]; rfl
  erw [hHead_t]
  -- LHS now has `Zc.map(ymgu) ≫ (Z.naturality g.1)` adjacent; transport it through Z.nat g.1.
  erw [(Z.naturality g.1).hom.toNatTrans.naturality
    ((λ_ f.1.unop).hom ≫ (ρ_ f.1.unop).inv)]
  -- step 2: transport the factor through `f.2.naturality g.1` (inside `G.map`).
  have hT2 : ∀ {M : ↑(a.2.obj c.1)}
      (A : (Z.app c.1).toFunctor.obj
          (((postcomp₂ (g.1.unop ≫ f.1.unop)).app c.1).toFunctor.obj (𝟙 (unop c.1))) ⟶ M)
      (Bb : M ⟶ (Z.app b.1 ≫ a.2.map g.1).toFunctor.obj (𝟙 (unop b.1) ≫ f.1.unop)),
      (f.2.app c.1).toFunctor.map
          (A ≫ Bb ≫ (Z.app b.1 ≫ a.2.map g.1).toFunctor.map
            ((λ_ f.1.unop).hom ≫ (ρ_ f.1.unop).inv)) ≫
        (f.2.naturality g.1).hom.toNatTrans.app
          ((Z.app b.1).toFunctor.obj
            (((yoneda₀ (unop a.1)).map f.1).toFunctor.obj (𝟙 (unop a.1))))
      = (f.2.app c.1).toFunctor.map (A ≫ Bb) ≫
          (f.2.naturality g.1).hom.toNatTrans.app
            ((Z.app b.1).toFunctor.obj (𝟙 (unop b.1) ≫ f.1.unop)) ≫
            (b.2.map g.1).toFunctor.map
              ((f.2.app b.1).toFunctor.map
                ((Z.app b.1).toFunctor.map ((λ_ f.1.unop).hom ≫ (ρ_ f.1.unop).inv))) := by
    intro M A Bb
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc]
    erw [(f.2.naturality g.1).hom.toNatTrans.naturality
      ((Z.app b.1).toFunctor.map ((λ_ f.1.unop).hom ≫ (ρ_ f.1.unop).inv))]
    erw [← Functor.map_comp_assoc]; rfl
  erw [hT2]
  -- step 3: transport through `g.2.naturality g.1` (top level; has a trailing tail → reassoc).
  have hT3 : ∀ {M : ↑(b.2.obj c.1)}
      (A' : (f.2.app c.1).toFunctor.obj ((Z.app c.1).toFunctor.obj
          (((postcomp₂ (g.1.unop ≫ f.1.unop)).app c.1).toFunctor.obj (𝟙 (unop c.1)))) ⟶ M)
      (Bb' : M ⟶ (b.2.map g.1).toFunctor.obj ((f.2.app b.1).toFunctor.obj
          ((Z.app b.1).toFunctor.obj (𝟙 (unop b.1) ≫ f.1.unop)))),
      (g.2.app c.1).toFunctor.map
          (A' ≫ Bb' ≫ (b.2.map g.1).toFunctor.map
            ((f.2.app b.1).toFunctor.map
              ((Z.app b.1).toFunctor.map ((λ_ f.1.unop).hom ≫ (ρ_ f.1.unop).inv)))) ≫
        (g.2.naturality g.1).hom.toNatTrans.app
          ((f.2.app b.1).toFunctor.obj ((Z.app b.1).toFunctor.obj
            (((yoneda₀ (unop a.1)).map f.1).toFunctor.obj (𝟙 (unop a.1)))))
      = (g.2.app c.1).toFunctor.map (A' ≫ Bb') ≫
          (g.2.naturality g.1).hom.toNatTrans.app
            ((f.2.app b.1).toFunctor.obj ((Z.app b.1).toFunctor.obj (𝟙 (unop b.1) ≫ f.1.unop))) ≫
            (c.2.map g.1).toFunctor.map
              ((g.2.app b.1).toFunctor.map
                ((f.2.app b.1).toFunctor.map
                  ((Z.app b.1).toFunctor.map ((λ_ f.1.unop).hom ≫ (ρ_ f.1.unop).inv)))) := by
    intro M A' Bb'
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc]
    erw [(g.2.naturality g.1).hom.toNatTrans.naturality
      ((f.2.app b.1).toFunctor.map
        ((Z.app b.1).toFunctor.map ((λ_ f.1.unop).hom ≫ (ρ_ f.1.unop).inv)))]
    erw [← Functor.map_comp_assoc]; rfl
  erw [reassoc_of% hT3]
  erw [Category.id_comp]
  simp only [Cat.Hom.comp_toFunctor, Functor.comp_map]
  iterate (first | erw [← Functor.map_comp_assoc] | erw [← Functor.map_comp])
  iterate erw [Category.assoc]
  iterate erw [← Functor.map_comp]
  dsimp only [postcomp₂, postcomposingCat, postcomp, Functor.toCatHom]
  iterate (first | erw [← Functor.map_comp_assoc] | erw [← Functor.map_comp])
  rfl
```
