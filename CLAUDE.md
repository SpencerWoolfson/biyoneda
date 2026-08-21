# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

A Lean 4 / Mathlib formalization of the **bicategorical Yoneda lemma**. See `README.md` for the
mathematical statement and `Biyoneda/*.lean` module docstrings for per-file detail — those are
thorough and current; this file covers only what spans several files or is easy to get wrong.

## Commands

```bash
lake exe cache get   # download prebuilt Mathlib oleans — run once, before the first build
lake build           # full build; ~30s warm, and Mathlib from scratch is ~20 min without cache
make                 # compile paper/Biyoneda.tex → Biyoneda.pdf (needs TeX Live)
```

There is no test suite. **The build is the test**, and a green build is not the finish line —
see "Verification" below.

### Fast iteration

A full `lake build` re-elaborates whole files. For experiments, write a scratch module inside
the package and compile only it:

```bash
lake env lean Biyoneda/Probe.lean
```

This uses the cached Mathlib oleans, takes seconds, and writes no build artifacts, so it is
safe to run alongside other work. Batch several candidate proofs into one probe file and read
all the errors at once. **Delete the probe when done** — anything under `Biyoneda/` is picked up
by the build, and `Biyoneda/Probe.lean` is not gitignored.

## Verification

**`#print axioms` is ground truth, not the absence of warnings.** This project has been burned
by the difference (commit `9cdce1a`, and `Gadgets.lean:102-109` documents the mechanism).

- `cat_disch` / `aesop_cat` try `sorry_if_sorry` first, which closes *any* goal whose statement
  mentions `sorry`. So while a definition carries `sorryAx`, autoparam fields in declarations
  that mention it may be silently discharged rather than proved. They break later, when the
  root sorry is finally closed.
- Counting sorries: grep the build log for `declaration uses`, **not** `uses 'sorry'` — the
  message quotes sorry in *backticks*, so the quoted form silently returns 0 and makes a
  sorried build look clean.
- The warning count exceeds the literal `sorry` count. As of the 2026-08-18 audit: 5 literal
  sorries in 4 declarations, but 6 warnings — the extra two are honestly-proven lemmas that
  inherit `sorryAx` through their *statements*.
- A declaration with an *error* in any field emits no sorry warnings at all, so a disappeared
  warning may be a masked failure rather than a success.

**Current axiom state:** `yonedaPairing`'s `mapComp` sorry (`Biyoneda/Basic.lean:185`) is the
single root contaminant. `yonedaPairing`, `yonedaLemmaForwards`, `yonedaLemmaBackwards`,
`yonedaLemma`, `yonedaHomInvIdObjIso`, and `forwards_naturality_comp_core` all carry `sorryAx`.
`yonedaEvaluation'` and everything in the general layer are clean. Treat "proven" claims about
anything touching `yonedaPairing` as provisional until that root closes.

## Architecture

Three layers, wired in `Biyoneda.lean`:

1. **General / upstreamable — all sorry-free.** `ForMathlib` (Cat and bicategory lemmas missing
   from Mathlib), `UniverseLift` (`Cat` universe machinery), `BiEquiv` (un-adjointed internal
   equivalence), `Evaluation` (`evaluationPseudo`, the bicategorical `evaluationUncurried`).
   Nothing here mentions Yoneda. This layer is staged for a Mathlib PR.
2. **The development.** `Basic.lean` — half the project's ~3,000 lines, 48 declarations, and
   every remaining sorry.
3. **Experimental.** `Gadgets` (`Pseudofunctor.prod`/`.op`/`homPseudo` — all complete) and
   `CompositePairing`. **`Basic` does not import these**; they exist to rebuild `yonedaPairing`
   as a composite the way Mathlib's 1-categorical Yoneda does. Read `CompositePairing.lean`'s
   header before touching that idea — the swap was attempted and reverted, and the reasons are
   recorded there.

### Cross-cutting constraints

- **Two universes.** `yonedaEvaluation'` lands in `Cat.{w, v}`; `yonedaPairing` lands in
  `Cat.{max u (max v w), ...}`. `catPseudoULift` promotes the former so the two are comparable.
  Universe plumbing appears throughout `Basic.lean` and is not incidental complexity.
- **`Cat` strictness is load-bearing.** `evaluationPseudo`'s `mapId` field is `x.2.mapId x.1`,
  which typechecks *only* because `Cat` is `Bicategory.Strict` and the left unitor reduces
  definitionally. Generalizing the target from `Cat` to an arbitrary `D` is a different
  construction, not a refactor.

## Proof-engineering gotchas

**Instance diamonds are the main time sink.** When a simp lemma that obviously matches refuses
to fire, or `erw` times out, suspect that the goal's `𝟙`/`≫`/`◁`/`▷` were elaborated through a
different-but-defeq instance path than the lemma's. Do not respond by re-running simp with more
lemmas — switch tools.

- `ForMathlib`'s `Cat.associator_hom_toNatTrans_app` and siblings are the project's canonical
  simp-normal form: Mathlib states these components through `eqToHom (by simp)`, which is `rfl`
  only at *default* transparency, so `simp` (which matches at reducible transparency) can't fire
  `eqToHom_refl` on them and proofs get pushed onto `erw`. Switching to the `_toNatTrans_app`
  forms took one declaration from ~22s to ~4s.
- **That recipe does not apply universally.** Goals descending from `StrongTrans.vcomp`'s
  naturality come through a *generic-bicategory* `Bicategory.homCategory` projection path — a
  different diamond, which these lemmas do not address. See `Basic.lean:964-968`. Attempts to
  golf `strongTrans_comp_naturality_hom_app` and its siblings failed twice for this reason.
- `erw` is dense here (110 calls in `Basic.lean`, 59 in `Evaluation.lean`). Existing chains are
  load-bearing and fragile against term-shape shifts — change them one at a time, with a build
  between.
- Bare `simp` is sometimes deliberate. The compiler's suggested `simp only [...]` replacements
  are not always safe: substituting them in `yonedaHomInvIdObjIso` broke a downstream `erw` by
  changing the intermediate goal shape, for no measurable heartbeat gain.
- `set_option maxHeartbeats` at `Basic.lean:431` (500k) and `Evaluation.lean:240` (400k) have
  **measured** floors recorded in adjacent comments. Don't lower them speculatively.

## Conventions

- Mathlib style throughout: ≤100-char lines, `←` not `<-`, `fun x ↦`, copyright header on every
  file, module docstring, docstrings on essentially every declaration. Match it.
- `lakefile.toml` sets `relaxedAutoImplicit = false` and `maxSynthPendingDepth = 3`; the Mathlib
  standard linter set is on. New code is expected to pass it.
- Mathlib is pinned to `v4.29.0`. `.github/workflows/update.yml` can bump it but its schedule is
  commented out, so updates are manual and deliberate.
- `Gadgets.lean:246` needs `set_option backward.isDefEq.respectTransparency false`. It is a
  compatibility flag and will eventually be removed upstream — expect that file to need work at
  the toolchain bump that drops it.

## Working notes

`notes/` holds WIP context — parked-proof goal dumps, measurement records, the unposted Zulip
draft, and a tech-debt audit. **It is gitignored on purpose** (it was untracked in `f328e36`;
the decision was deliberate, do not re-track it). Park stalled proofs there rather than leaving
broken half-states in the source: save the working proof prefix, the exact residual goal, and
one or two candidate next moves, then revert the field to a clean `sorry`.

Note that `CompositePairing.lean:30` and `Gadgets.lean:301` cite `notes/level2_refactor.md`,
which is not in the repository — those references dangle for anyone reading on GitHub.
