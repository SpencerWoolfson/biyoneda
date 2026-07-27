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

## The regression — RESOLVED

`forwards_naturality_comp_core` broke after the alias landed. **Root cause:** its proof begins

```lean
dsimp only [yonedaPairing, yonedaEvaluation']
```

which used to unfold `yonedaEvaluation'` all the way to its record literal.  Once
`yonedaEvaluation'` became `evaluationPseudo (C := Bᵒᵖ)`, that `dsimp` stops one step short —
it produces `evaluationPseudo` and cannot unfold further, because `evaluationPseudo` is not in
the list.  Every later `erw` in the ordered chain was then matching against a differently-shaped
term.

**Fix:** add `evaluationPseudo` to the unfold list (two sites in `Basic.lean`, ~493 and ~583):

```lean
dsimp only [yonedaPairing, yonedaEvaluation', evaluationPseudo]
```

With that, the original 96-line tactic chain works **verbatim** — no re-tuning needed.
Basic.lean is back to **6 sorries, the same as `master`**, with zero regressions.

Ruled out along the way: `abbrev`/`@[reducible]` on `yonedaEvaluation'` (identical failure — it
is a *dsimp unfold-list* problem, not a transparency-depth one).

**Lesson (generalises to any alias refactor):** when a `def` is replaced by an alias for a more
general one, every `simp`/`dsimp` unfold list mentioning it needs the general name added too.
Ordered `erw` chains are the first thing to break, and they break *downstream* of the real cause.

## API for `evaluationPseudo`

Added at the end of `Evaluation.lean` (all verified):

| lemma | content |
|---|---|
| `evaluationPseudo_obj` / `_map` / `_mapId` | the structure fields, by `rfl` |
| `evaluationPseudo_map_obj` | `.map f` on a point |
| `evaluationPseudo_map₂_app` | component of `map₂` |
| `evaluationPseudo_mapId_hom_app` | component of `mapId` |
| `evaluationPseudo_mapComp_hom_app` | **component of `mapComp` with the strict-`Cat` associator identities already cancelled** |
| `evaluationPseudo_mapComp_inv_app` | inverse form |

The `mapComp` component lemmas are the valuable ones: they state in a single rewrite what the
existing proofs derive by hand with `iterate 6 (first | erw [Cat.Hom.inv_hom_id_toNatTrans_app] | …)`.
They are deliberately **not** `@[simp]`, matching the `ForMathlib` policy.
