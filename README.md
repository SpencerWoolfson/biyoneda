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

**Complete.** `yonedaLemma` is proved: no `sorry` anywhere in the development, and
`#print axioms Biyoneda.yonedaLemma` reports only `propext`, `Classical.choice` and
`Quot.sound`.

| | |
|---|---|
| Build | 0 errors |
| Declarations using `sorry` | 0 |
| `yonedaLemma` axioms | `propext`, `Classical.choice`, `Quot.sound` |

The development closed in dependency order.  The three pseudofunctor gadgets under the
statement went first — `catPseudoULift` (`UniverseLift.lean`), `homPseudo` (`Gadgets.lean`,
which took `yonedaPairingComposite` and `yonedaPairing` with it), and `evaluationPseudo`
(`Evaluation.lean`, which took `yonedaEvaluation`).  Then the two strong transformations:
`yonedaLemmaBackwards` on 2026-09-03 and `yonedaLemmaForwards` on 2026-09-05, each reduced to
one fibre lemma (`backwards_comp_core`, `forwards_naturality_comp_core`) through
`naturality_comp_assoc_core` — the associativity coherence a strong transformation's
`naturality` satisfies against the two pseudofunctors' `mapComp`s, at a point.  Finally the
unit and the counit, both on 2026-09-05.

The unit was built inside out: the components at a point, at a fibre and at an object
(`yonedaHomInvIdFunctorIso`, `yonedaHomInvIdObjIso`, `yonedaHomInvIdNatIso`), then the
modification square (`yonedaHomInvIdIso`).  Each layer rests on a core stated in unbundled
variables, because inside the definitions the evaluation point `𝟙 b₀` is not type-correct at
`implicit` transparency and no rewriting tactic can fire there.  The counit reduces to
`counit_core`, a coherence between a strong transformation's `naturality_comp`, its
`naturality_id`, and the two `mapComp`-against-unitor identities of the codomain.

`scripts/verify-build.sh` gates CI on a sorry ratchet (now at zero) and a per-declaration
axiom check asserted by `#print axioms` lines in `Biyoneda/CompositePairing.lean`, so neither
a `sorry` nor a `sorryAx` dependency can reappear unnoticed.

## Key Definitions

| Lean name | Mathematical meaning |
|---|---|
| `yonedaPairing` | Pseudofunctor $(b, F) \mapsto \mathbf{StrongTrans}(\mathcal{Y}_0(b), F)$ |
| `yonedaEvaluation` | Pseudofunctor $(b, F) \mapsto F(b)$ |
| `yonedaLemmaForwards` | Strong transformation $\Phi : P \to E$, evaluating at $\mathrm{id}_b$ |
| `yonedaLemmaBackwards` | Strong transformation $\Psi : E \to P$, sending $s$ to $(a, f) \mapsto F(f)(s)$ |
| `yonedaHomInvId` | Unit isomorphism $\Psi \circ \Phi \cong \mathrm{id}_P$ |
| `yonedaInvHomId` | Counit isomorphism $\Phi \circ \Psi \cong \mathrm{id}_E$ |
| `yonedaLemma` | The assembled `Bicategory.Equivalence` (`≌`) witnessing the equivalence |
| `catPseudoULift` | Universe-lifting pseudofunctor needed to type-match the two sides |

## Repository Structure

```
biyoneda/
├── Biyoneda/
│   ├── ForMathlib.lean            # General Cat/bicategory lemmas staged for upstreaming
│   ├── UniverseLift.lean          # `catLift` / `catPseudoULift` and their stripping lemmas
│   ├── Gadgets.lean               # Pseudofunctor `prod`, `op`, `homPseudo`
│   ├── TransIntoCats.lean         # `StrongTransIntoCats` and its lifts
│   ├── StrongTransLemmas.lean     # General strong-transformation lemmas, at a point
│   ├── Evaluation.lean            # The evaluation pseudofunctor and its coherence cores
│   ├── Pairing.lean               # `yonedaPairing`
│   ├── Forwards.lean              # Φ : pairing ⟶ evaluation
│   ├── Backwards*.lean            # Ψ : evaluation ⟶ pairing
│   ├── Unit.lean                  # Unit and counit isos
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

This project makes substantial use of AI assistance, including for proofs, not just comments, documentation, and CI setup. Everything here is machine-checked by Lean, and `#print axioms Biyoneda.yonedaLemma` reports no `sorryAx` — but "the kernel accepts it" is not the same as "the statement says what you think it says". Please apply appropriate scrutiny to the *definitions*, and check `#print axioms` on anything you intend to rely on.

## License

Released under the Apache License 2.0, matching the Mathlib ecosystem. See [LICENSE](LICENSE).

## References

- J. Bénabou, *Introduction to bicategories*, 1967.
- N. Johnson and D. Yau, *2-Dimensional Categories*, Oxford University Press, 2021. ([arXiv](https://arxiv.org/abs/2002.06055))
- T. Leinster, *Higher Operads, Higher Categories*, Cambridge University Press, 2004. ([arXiv](https://arxiv.org/abs/math/0305049))
- The Mathlib Community, *Mathlib4*, 2024. ([GitHub](https://github.com/leanprover-community/mathlib4))
