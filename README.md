# Bicategorical Yoneda Lemma in Lean 4

[![Lean Action CI](https://github.com/SpencerWoolfson/biyoneda/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/SpencerWoolfson/biyoneda/actions/workflows/lean_action_ci.yml)

A Lean 4 / Mathlib formalization of the **Yoneda lemma for bicategories**.

## Mathematical Statement

The classical Yoneda lemma identifies natural transformations out of a representable functor with elements of the represented set. In the bicategorical setting this bijection upgrades to a natural **equivalence of categories**: for a bicategory $\mathcal{B}$ and a pseudofunctor $F : \mathcal{B}^{\mathrm{op}} \to \mathbf{Cat}$, there is an equivalence

$$\mathbf{StrongTrans}(\mathcal{Y}_0(b),\, F) \;\simeq\; F(b)$$

natural in $b \in \mathcal{B}^{\mathrm{op}}$ and $F$, where $\mathcal{Y}_0(b)$ is the representable pseudofunctor sending $a \mapsto \mathcal{B}(a, b)$.

Rather than constructing this equivalence object-by-object, the formalization expresses it as a biequivalence of pseudofunctors

$$\mathtt{yonedaPairing} \simeq \mathtt{yonedaEvaluation}$$

on the product bicategory $\mathcal{B}^{\mathrm{op}} \times [\mathcal{B}^{\mathrm{op}}, \mathbf{Cat}]$.

## Status

**This is work in progress. The main theorem is not yet fully proved.**

The project builds with no errors, but 12 declarations still contain `sorry`, and the
headline `yonedaLemma` depends on `sorryAx` through them. Concretely:

| | |
|---|---|
| Build | 0 errors |
| Declarations using `sorry` | 12 |
| `yonedaLemma` axioms | `propext`, `sorryAx`, `Classical.choice`, `Quot.sound` |

**Both sides of the equivalence are now `sorryAx`-free.** `yonedaPairing` and
`yonedaEvaluation` — and the three gadgets under them, `catPseudoULift` (`UniverseLift.lean`),
`homPseudo` (`Gadgets.lean`) and `evaluationPseudo` (`Evaluation.lean`) — all depend only on
`propext`, `Classical.choice` and `Quot.sound`. There is no longer any root of `sorryAx` in a
coherence field.

What remains is entirely in the **assembly layers**: the two strong transformations between
those pseudofunctors (`Forwards.lean`, `Backwards.lean`) and the unit/counit isomorphisms
(`Unit.lean`). Each `sorry` is marked at its site with the residual goal and what has been
tried.

`BackwardsNaturality.lean` — the naturality isomorphism of the backward transformation — is
sorry-free as of 2026-09-02.

`scripts/verify-build.sh` gates CI on both a sorry ratchet and a per-declaration axiom
check, so neither the count nor the set of `sorryAx`-dependent declarations can grow
unnoticed. A green CI badge means "did not regress", not "fully proved".

## Key Definitions

| Lean name | Mathematical meaning |
|---|---|
| `yonedaPairing` | Pseudofunctor $(b, F) \mapsto \mathbf{StrongTrans}(\mathcal{Y}_0(b), F)$ |
| `yonedaEvaluation` | Pseudofunctor $(b, F) \mapsto F(b)$ |
| `yonedaLemmaForwards` | Strong transformation $\Phi : P \to E$, evaluating at $\mathrm{id}_b$ |
| `yonedaLemmaBackwards` | Strong transformation $\Psi : E \to P$, sending $s$ to $(a, f) \mapsto F(f)(s)$ |
| `yonedaHomInvId` | Unit isomorphism $\Psi \circ \Phi \cong \mathrm{id}_P$ |
| `yonedaInvHomId` | Counit isomorphism $\Phi \circ \Psi \cong \mathrm{id}_E$ |
| `yonedaLemma` | The assembled `BiEquiv` witnessing the equivalence |
| `catPseudoULift` | Universe-lifting pseudofunctor needed to type-match the two sides |

## Repository Structure

```
biyoneda/
├── Biyoneda/
│   ├── ForMathlib.lean            # General Cat/bicategory lemmas staged for upstreaming
│   ├── UniverseLift.lean          # `catLift` / `catPseudoULift` and their stripping lemmas
│   ├── Gadgets.lean               # Pseudofunctor `prod`, `op`, `homPseudo`
│   ├── TransIntoCats.lean         # `StrongTransIntoCats` and its lifts
│   ├── Evaluation*.lean           # The evaluation pseudofunctor and its coherence cores
│   ├── Pairing.lean               # `yonedaPairing`
│   ├── Forwards.lean              # Φ : pairing ⟶ evaluation
│   ├── Backwards*.lean            # Ψ : evaluation ⟶ pairing
│   ├── Unit.lean                  # Unit and counit isos
│   ├── BiEquiv.lean               # Internal equivalence in a bicategory
│   ├── Yoneda.lean                # The assembled theorem
│   └── CompositePairing.lean      # `yonedaPairing` as a composite of gadgets; axiom checks
├── paper/                         # Paper source (Biyoneda.tex, preamble, references)
├── Biyoneda.pdf                   # Compiled paper (built by CI)
├── scripts/verify-build.sh        # Sorry ratchet + axiom gate, run by CI
├── Makefile                       # `make` to compile the paper locally
├── lakefile.toml
└── lean-toolchain                 # Lean 4 v4.33.0 / Mathlib v4.33.0
```

## Paper

A write-up of the formalization is in [`paper/Biyoneda.tex`](paper/Biyoneda.tex).
The compiled PDF is kept up to date by CI and can be read directly on GitHub: **[Biyoneda.pdf](Biyoneda.pdf)**.

To compile the paper locally (requires a TeX Live installation):

```bash
make
```

## Building the Lean Code

**Prerequisites:** [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) with `elan` (the Lean version manager). The correct toolchain is pinned in `lean-toolchain` and will be fetched automatically.

```bash
lake exe cache get   # download prebuilt Mathlib artifacts
lake build           # build the project
```

The first `lake exe cache get` step downloads compiled Mathlib oleans so you do not need to rebuild Mathlib from scratch (~20 min without cache).

## Dependencies

- [Lean 4](https://github.com/leanprover/lean4) `v4.33.0`
- [Mathlib4](https://github.com/leanprover-community/mathlib4) `v4.33.0`

Specifically, the formalization builds on:
- `Mathlib.CategoryTheory.Bicategory.Yoneda`
- `Mathlib.CategoryTheory.Category.ULift`

## Notes on AI

This project makes substantial use of AI assistance, including for proofs, not just comments, documentation, and CI setup. Everything that is proved is machine-checked by Lean — but see **Status** above: a number of results are still `sorry`, so "it builds" is not the same as "it is proved". Please apply appropriate scrutiny, and check `#print axioms` on anything you intend to rely on.

## License

Released under the Apache License 2.0, matching the Mathlib ecosystem. See [LICENSE](LICENSE).

## References

- J. Bénabou, *Introduction to bicategories*, 1967.
- N. Johnson and D. Yau, *2-Dimensional Categories*, Oxford University Press, 2021. ([arXiv](https://arxiv.org/abs/2002.06055))
- T. Leinster, *Higher Operads, Higher Categories*, Cambridge University Press, 2004. ([arXiv](https://arxiv.org/abs/math/0305049))
- The Mathlib Community, *Mathlib4*, 2024. ([GitHub](https://github.com/leanprover-community/mathlib4))
