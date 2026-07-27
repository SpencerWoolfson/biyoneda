# Scoping: the two-variable hom-pseudofunctor `Bᵒᵖ × B ⥤ᵖ Cat`

**Question.** Mathlib's 1-categorical `yonedaPairing` is a one-line composite

```lean
def yonedaPairing : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁) ⥤ Type max u₁ v₁ :=
  Functor.prod yoneda.op (𝟭 _) ⋙ Functor.hom (Cᵒᵖ ⥤ Type v₁)
```

Can our bicategorical `yonedaPairing` be rebuilt the same way, so its hand-rolled fields (and the
parked P4 `mapComp` sorry) disappear?

## Verdict: feasible for the gadget, but the *composite* needs three new gadgets, not one

### Verified by experiment (probe compiled)

1. **All primitives exist and are general.** `Bicategory.precomp` / `postcomp` /
   `precomposing` / `postcomposing` (`Bicategory/Basic.lean` 462–486), plus the `Cat`-level
   `precomposingCat` / `postcomposingCat`, `leftUnitorNatIsoCat`, `rightUnitorNatIsoCat`,
   `associatorNatIso{Right,Left,Middle}Cat` (`Bicategory/Yoneda.lean` 32–78).
2. **`obj` and `map` assemble and typecheck**:
   ```lean
   obj p := Cat.of (unop p.1 ⟶ p.2)
   map {p q} fg := (precomp p.2 fg.1.unop ⋙ postcomp (unop q.1) fg.2).toCatHom
   ```
3. **`map₂` data assembles** — `(η.1.unop2 ▷ h) ▷ fg.2 ≫ (fg'.1.unop ≫ h) ◁ η.2`.
4. **`mapId` data assembles** — `ρ_ _ ≪≫ λ_ h`.
5. **Strong precedent**: Mathlib's own one-variable analogues are *four lines each* with **every
   coherence field auto-discharged** by the autoparams:
   ```lean
   def yoneda₀ (x : B) : Pseudofunctor Bᵒᵖ Cat where
     toPrelaxFunctor := PrelaxFunctor.mkOfHomFunctors …
     mapId a := leftUnitorNatIsoCat (unop a) x
     mapComp f g := associatorNatIsoRightCat g.unop f.unop x
   ```
   Note `associatorNatIsoMiddleCat` (the pre/post **exchange**) already exists and is exactly the
   extra coherence the two-variable case needs — the library anticipates this construction.

### Friction found (measured, not guessed)

6. **`mapComp` does not come free.** `bicategoricalIso _ _` **fails**:
   ```
   failed to synthesize  BicategoricalCoherence
     (((fg ≫ gh).1.unop ≫ h) ≫ (fg ≫ gh).2) ((gh.1.unop ≫ (fg.1.unop ≫ h) ≫ fg.2) ≫ gh.2)
   ```
   The product-and-opposite projections (`(fg ≫ gh).1.unop`) are not in structural normal form, so
   the coherence instance search cannot engage. It needs a `dsimp`/`show` normalisation first, or a
   hand-built associator chain. **This is the same friction our existing hand-rolled
   `yonedaPairing` already suffers**, and it is why `set_option
   backward.isDefEq.respectTransparency false` decorates most of `Bicategory/Yoneda.lean`.

### The main unknown

7. Whether the five coherence fields fall to `cat_disch` once the data is in place. Mathlib's
   one-variable precedent says yes; but the two-variable case has strictly more coherence, and
   point 6 shows the product/op projections actively interfere with the automation. **Not
   de-risked.** This is the item that decides whether the project is days or weeks.

## Scope correction: one gadget is not enough

Rebuilding `yonedaPairing` as a composite needs **three** missing pieces, not one — all confirmed
absent from `Mathlib/CategoryTheory/Bicategory/` (zero grep hits each):

| needed | 1-cat version | bicategorical status |
|---|---|---|
| hom-pseudofunctor `Kᵒᵖ × K ⥤ᵖ Cat` | `Functor.hom` (3 lines) | absent — scoped here |
| `Pseudofunctor.prod` | `Functor.prod` | absent |
| `Pseudofunctor.op` | `Functor.op` | absent |

And note our pairing needs the hom-pseudofunctor of `K = Bᵒᵖ ⥤ᵖ Cat` (the *functor* bicategory),
whose hom-categories are `StrongTrans` with modifications — so `precomp`/`postcomp` there are
whiskering of strong transformations. Generic in `K`, so the construction still applies, but it is
the heavier instance to test against.

## Recommendation

Treat this as a **separate project**, not a refactor of the current file. Suggested order, with a
kill switch after step 2:

1. Build `homPseudo` for a *general* bicategory `B` (`Bᵒᵖ × B ⥤ᵖ Cat`), data first.
2. **Decision point:** hammer the five coherence fields with `cat_disch` / `bicategory`. If they
   close (with at most a normalising `dsimp` for the projections), continue; if they need bespoke
   `erw` chains of the kind in `evaluation_associator_core`, stop — the composite route would then
   cost *more* than the hand-rolled `yonedaPairing` it replaces.
3. Only then `Pseudofunctor.prod` and `Pseudofunctor.op`, and finally rewire `yonedaPairing`.

Cheaper work that is already scoped and lower risk: the universe-lift extraction (task #9) and the
six remaining sorries.

## Unrelated finding worth keeping

Mathlib's 1-categorical `yonedaEvaluation` is
`evaluationUncurried Cᵒᵖ (Type v₁) ⋙ uliftFunctor` — confirming both halves of our level-2 work
(`evaluationPseudo` = bicategorical `evaluationUncurried`; `catPseudoULift` = `uliftFunctor`).
Its `map` is `x.2.map f.1 ≫ f.2.app y.1`; **ours is the other diagonal**,
`f.2.app x.1 ≫ y.2.map f.1`. Equal in a 1-category by naturality, only *isomorphic* for a strong
transformation. Decide deliberately before upstreaming.
