# Zulip draft

**Where:** `leanprover.zulipchat.com`, stream **#mathlib4**, new topic:
`bicategorical Yoneda — upstreaming an evaluation pseudofunctor`

(If you'd rather start smaller/lower-stakes, ask the "does this exist?" question alone in
**#Is there code for X?** first, then follow up in #mathlib4.)

**Before posting:** push (18 commits are local-only — the GitHub link would show stale code), and
re-check the "missing from Mathlib" claims against current master; this repo pins Mathlib v4.29.0.

---

Hi all — I've been formalising the **Yoneda lemma for bicategories** on top of
`Mathlib.CategoryTheory.Bicategory.Yoneda`, and I'd like advice on getting the general-purpose
parts upstream.

Repo: https://github.com/SpencerWoolfson/biyoneda

The headline statement is

```lean
def yonedaLemma : BiEquiv (@yonedaPairing B _) (@yonedaEvaluation B _)
```

i.e. `StrongTrans (yoneda₀ b) F ≃ F.obj b`, as a biequivalence of pseudofunctors on
`Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat)` — deliberately mirroring the 1-categorical
`yonedaLemma : yonedaPairing C ≅ yonedaEvaluation C`.

**Status, honestly:** the main development still has 6 `sorry`s (the backwards-direction
coherence, and the unit/counit isos). But in the course of it I factored out two pieces that are
complete, fully general, and — as far as I can tell — missing from Mathlib. Those are what I'd
like to upstream first, independently of whether the main theorem ever lands.

### 1. An evaluation pseudofunctor

Mathlib has `evaluationUncurried : C × (C ⥤ D) ⥤ D` for 1-categories, and builds
`yonedaEvaluation` from it. I can't find a bicategorical analogue —
`grep -r evaluation Mathlib/CategoryTheory/Bicategory/` returns nothing. So I built one:

```lean
/-- The evaluation pseudofunctor `C × (C ⥤ᵖ Cat) ⥤ᵖ Cat`, `(c, F) ↦ F.obj c`. -/
def evaluationPseudo (C : Type u₁) [Bicategory C] : C × (C ⥤ᵖ Cat) ⥤ᵖ Cat where
  obj x := x.2.obj x.1
  map {x y} f := f.2.app x.1 ≫ y.2.map f.1
  map₂ {x y f g} η := (η.2.as.app x.1 ▷ y.2.map f.1) ≫ (_ ◁ y.2.map₂ η.1)
  mapId x := x.2.mapId x.1
  mapComp := …
```

It's about 700 lines with all coherence proved and no sorries. Two design questions I'd
genuinely like input on before shaping a PR:

- **Why `Cat`-valued rather than a general target `D`?** The `mapId` field above is just
  `x.2.mapId x.1`, which typechecks *only* because `Cat` is `Bicategory.Strict` — the left unitor
  `𝟙 ≫ F.map (𝟙 _)` reduces definitionally. Over a general `D` the field needs an explicit `λ_`,
  which is a genuinely different (non-defeq) definition. Is the general-`D` version the one that
  belongs in Mathlib, and is leaning on strictness here a mistake I should undo?
- **Which diagonal of the naturality square?** Mathlib's `evaluationUncurried.map` is
  `x.2.map f.1 ≫ f.2.app y.1`; I wrote `f.2.app x.1 ≫ y.2.map f.1`. For a 1-categorical natural
  transformation these agree; for a *strong* transformation they're only isomorphic. I assume I
  should match Mathlib's convention — any reason not to?

### 2. `Cat`'s coherence 2-cells are literally `𝟙`

`Cat` is strict, so its associator and unitor 2-cells are identity natural transformations.
Mathlib states their components through `eqToHom (by simp)` (`Cat.associator_hom_app`,
`Cat.leftUnitor_hom_app`, …), and that proof is `rfl` only at *default* transparency — so `simp`,
which matches at reducible transparency, can't fire `eqToHom_refl` on them, and proofs get pushed
onto `erw`. All of these hold by `rfl`:

```lean
theorem Cat.associator_hom_toNatTrans_app (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E) (X : B) :
    (α_ F G H).hom.toNatTrans.app X = 𝟙 _ := rfl
```

(likewise `associator_inv`, `leftUnitor_hom/inv`, `rightUnitor_hom/inv`). Switching my proofs over
to these took one declaration from ~22s to ~4s of elaboration, just by letting `simp` do cleanup
that `erw` had been doing.

Would a PR adding these be welcome — or better, would changing the existing `Cat.*_app` lemmas to
produce `𝟙` directly be acceptable, since that seems like the real fix?

### Asks

I haven't contributed to Mathlib before, so concretely:

1. Is the right move a small PR for (2) first, with (1) as a separate new-file PR?
2. Where should a bicategorical evaluation pseudofunctor live —
   `Mathlib/CategoryTheory/Bicategory/Products/…`, or alongside `Bicategory/Yoneda.lean`?
3. Is anyone already working on bicategorical Yoneda / a hom-pseudofunctor? I also found no
   `Pseudofunctor.prod`, `Pseudofunctor.op`, or two-variable hom-pseudofunctor, which is what
   would be needed to build `yonedaPairing` as a composite the way the 1-categorical one is.

Happy to adapt naming and style to whatever reviewers prefer.

*(Disclosure: I've used AI assistance on parts of this — proofs, docstrings and CI setup. Every
proof is machine-checked by Lean, and I've reviewed the code, but I'd rather say so up front.)*
