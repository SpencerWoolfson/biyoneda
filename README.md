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
| `CatPseudoULift` | Universe-lifting pseudofunctor needed to type-match the two sides |

## Repository Structure

```
biyoneda/
├── Biyoneda/
│   └── Basic.lean          # All definitions and proofs
├── paper/
│   ├── Biyoneda.tex        # Paper source
│   ├── preamble.tex        # LaTeX packages and macros
│   └── references.bib      # Bibliography
├── Biyoneda.pdf            # Compiled paper (built by CI)
├── Makefile                # `make` to compile the paper locally
├── lakefile.toml
└── lean-toolchain          # Lean 4 v4.29.0 / Mathlib v4.29.0
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

- [Lean 4](https://github.com/leanprover/lean4) `v4.29.0`
- [Mathlib4](https://github.com/leanprover-community/mathlib4) `v4.29.0`

Specifically, the formalization builds on:
- `Mathlib.CategoryTheory.Bicategory.Yoneda`
- `Mathlib.CategoryTheory.Category.ULift`

## Notes on AI

I have been experimenting with use of AI in formalization. I have had some limited success with it writing the lean code succses but I have used it for comments, documentation, and setting up the git actions in the repo. I have given a cursory look at all of the things it has written and corrected any small errors I have found. I plan to give a more detailed look at it in the future. Please be warned to take these things with a grain of salt.

## References

- J. Bénabou, *Introduction to bicategories*, 1967.
- N. Johnson and D. Yau, *2-Dimensional Categories*, Oxford University Press, 2021. ([arXiv](https://arxiv.org/abs/2002.06055))
- T. Leinster, *Higher Operads, Higher Categories*, Cambridge University Press, 2004. ([arXiv](https://arxiv.org/abs/math/0305049))
- The Mathlib Community, *Mathlib4*, 2024. ([GitHub](https://github.com/leanprover-community/mathlib4))
