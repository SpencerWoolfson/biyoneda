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

## Statement de-noising (using the API's insight)

The `*_core` statements were long partly because they bake in **identity 2-cells** — artefacts of
the unreduced pasting, each costing 2–4 lines. Stripping them (the field's `simpa` bridges the
difference) shrank the unitor cores substantially:

| lemma | statement lines | `𝟙` in statement |
|---|---|---|
| `evaluation_left_unitor_core` | 14 → **10** | 7 → 3 |
| `evaluation_right_unitor_core` | 20 → **11** | 13 → 4 |

The remaining `𝟙`s are genuine identity *1-cells* (`𝟙 a.1`), not noise.

`evaluation_associator_core` (68-line statement, 9 identity 2-cells) was **attempted and reverted**:
removing them requires balanced-paren surgery across a deeply nested term and the automated pass
left the expression unbalanced. Doing it needs a careful hand edit; the 279-line proof below it
makes the risk/benefit poor until the rest of the project settles.

## Why the cores can't just be restated via the API

Worth recording, because it looks like an obvious win and is not: the `evaluation_*_core` lemmas
are consumed *inside* `evaluationPseudo`'s own coherence fields, so they **cannot mention
`evaluationPseudo`** — that would be circular. They are obliged to speak in raw, expanded terms.
This is the structural reason their statements are long, and it caps how far cosmetic cleanup can
go. Shortening them further means changing how the pseudofunctor is *built* (e.g. assembling it
from smaller gadgets so the fields are inherited), not how the cores are *stated*.

## Cutting down the core lemmas — generalising the transported point

Measured the repetition instead of guessing.  In `evaluation_associator_core` alone:

| repeated expression | occurrences |
|---|---|
| `P1 = (f.2.app a.1).toFunctor.obj Z` | **66** |
| `P2 = (g.2.app a.1).toFunctor.obj P1` | 35 |
| `P3 = (h.2.app a.1).toFunctor.obj P2` | 17 |

So the cores are dominated by re-spelling the same *transported point*.  The fix is to take the
transported point as a **free variable** rather than rebuilding it from `Z` each time:

```lean
-- before:  (Z : ↑(a.2.obj a.1))   ... with ((f.2.app a.1).toFunctor.obj Z) written 10-18×
-- after:   (W : ↑(b.2.obj a.1))   ... written simply W
```

This also makes the lemmas strictly **more general** (they now hold for an arbitrary `W`, not only
for transported points); the call site instantiates `W := (f.2.app a.1).toFunctor.obj Z`.

Applicability was checked per core by counting `Z` occurrences *outside* `P1`:

| core | `P1`× | bare `Z` outside `P1` | generalised? |
|---|---|---|---|
| `evaluation_whisker_left_core` | 10 | **0** | yes |
| `evaluation_associator_core` | 18 | 1 | yes — see below |
| `evaluation_whisker_right_core` | 3 | 7 | no (point enters directly) |
| `evaluation_left_unitor_core` | 2 | 3 | no |
| `evaluation_right_unitor_core` | 4 | 1 | no |

The associator's single blocking `Z` sits in `((α_ f g h).hom.2.as.app a.1).toNatTrans.app Z`,
which is **definitionally the identity** (`Cat` is strict).  Recording that as

```lean
lemma prod_associator_snd_as_app_app … :
    ((α_ f g h).hom.2.as.app a.1).toNatTrans.app Z = 𝟙 _ := rfl
```

lets the statement use `𝟙` instead, unblocking the generalisation and letting `Functor.map_id`
collapse the whole first factor of the LHS.  At the call site it must be applied with `erw`
(the usual `Cat` strictness diamond), not `rw`.

### Result

| core | statement lines | statement chars |
|---|---|---|
| `evaluation_whisker_left_core` | 25 → **16** | 1438 → 1056 |
| `evaluation_associator_core` | 68 → **30** | 3904 → 2599 |
| **all five cores** | | 7836 → **6149 (−21%)** |

Build green, `Basic.lean` unchanged at 6 sorries.

### Still open

`whisker_right` / the two unitor cores take the point directly and so do not generalise this way.
Reducing them further would need the deeper change: assembling `evaluationPseudo` from smaller
gadgets so the coherence fields are *inherited* rather than proved, which would remove the cores
entirely rather than shortening them.
