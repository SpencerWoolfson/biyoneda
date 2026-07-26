# P3 backwards coherence — WIP (resume here)

**Goal:** close the three `yonedaLemmaBackwards` coherence sorries (Basic.lean ~1844–1846):
`naturality_naturality`, `naturality_id`, `naturality_comp`. Mirror of the finished P2 forwards
work (`yonedaLemmaForwards` + `forwards_naturality_*_core`).

## The three goal states (harvested 2026-07-25)

Standard StrongTrans coherence obligations, 2-cells in `Cat`:
- **naturality_naturality** `{a b f g} η`:
  `yonedaEvaluation.map₂ η ▷ B_b ≫ N_g = N_f ≫ B_a ◁ yonedaPairing.map₂ η`
- **naturality_id** `a`:
  `N_{𝟙} ≫ B_a ◁ (yonedaPairing.mapId a).hom = (yonedaEvaluation.mapId a).hom ▷ B_a ≫ (λ_ B_a).hom ≫ (ρ_ B_a).inv`
- **naturality_comp** `{a b c} f g`:
  `N_{f≫g} ≫ B_a ◁ (yonedaPairing.mapComp f g).hom = (yonedaEvaluation.mapComp f g).hom ▷ B_c ≫ α_ ≫
   yonedaEvaluation.map f ◁ N_g ≫ α_.inv ≫ N_f ▷ yonedaPairing.map g ≫ α_`
  where `B_x := { toFunctor := yonedaLemmaBackwardsFunctor x }` (the `.app`), and
  `N_x := (Cat.Hom.isoMk (NatIso.ofComponents (fun X ↦ backwardsNaturalityIso x X) _)).hom` (the `.naturality`).

## The descent pattern — ESTABLISHED (verified compiles to a clean fibre-morphism goal)

Backwards lands in `yonedaPairing` (StrongTrans), source `yonedaEvaluation` is ULift-lifted. The
working descent (for `naturality_naturality`; the others are analogous):
```lean
  naturality_naturality {a b f g} η := by
    apply Cat.Hom₂.ext_app          -- Cat 2-cell (natTrans) → .toNatTrans.app
    intro X
    obtain ⟨x⟩ := X                  -- strip the ULift on the yonedaEvaluation source
    dsimp only [yonedaEvaluation, Pseudofunctor.comp, catPseudoULift, catLift, ULiftHom.up,
      Functor.comp]
    apply homCategory.ext            -- modification → per-component
    intro γ
    apply Cat.Hom₂.ext_app           -- that component (a natTrans) → .app
    intro ZZ
    dsimp
    -- GOAL NOW: a concrete morphism equation in a fibre category, but HUGE and un-reduced
    --   (still has catLiftEquiv, yonedaPairing.map₂ η, backwardsNaturalityIso, … unfolded literally).
    sorry
```
(`Cat.Hom₂.ext_app` as the 2nd descent step FAILED — must use `homCategory.ext` for the modification,
then `Cat.Hom₂.ext_app` for its natTrans component. Order matters.)

## Next steps (the remaining work, per obligation)

1. **Reduce** the descended goal with a big `simp only [...]` — the backwards analogue of the forwards
   fields' reduction (`Cat.Hom.toNatTrans_comp, NatTrans.comp_app, Cat.whiskerLeft_toNatTrans,
   Cat.whiskerRight_toNatTrans, whiskerLeft_app, whiskerRight_app, yonedaEvaluation_map₂_app_down,
   Cat.Hom.isoMk_hom, Cat.toCatHom₂_toNatTrans, NatIso.ofComponents_hom_app, …` + backwards-specific:
   `backwardsNaturalityIso`, `isoMk_hom_as_app`, `catLiftEquiv` reductions). Harvest the residual with
   `trace_state`.
2. **Build a core lemma** `backwards_naturality_naturality_core …` stating the reduced content
   (clean fibre-morphism equation) and prove it — mirror `forwards_naturality_naturality_core`
   (~Basic.lean 1072). The content should reduce to the object-level backwards coherence, which is
   ALREADY proven in `yonedaLemmaBackwardsFunctorObj` (Basic.lean ~1500):
   `naturality_naturality := Cat.Hom₂.ext_app fun X ↦ Cat.Hom₂.congr_app
      (x.2.toOplax.mapComp_naturality_right (op X) g) eval`; likewise `mapComp_id_component`,
   `mapComp_assoc_component` for id/comp. So the cores likely wrap `mapComp_naturality_right` /
   `mapComp_id_component` / `mapComp_assoc_component`.
3. Close the field with `exact backwards_naturality_naturality_core …`.
4. **NEW: use the ForMathlib golf from the start** — the Cat coherence in these goals produces the
   same `eqToHom` cleanup; use `Cat.associator_hom_toNatTrans_app` etc. + `simpa … using core` rather
   than an `iterate … erw` cleanup (see `instance-diamonds.md` § eqToHom-strictness). This keeps the
   new proofs fast and clean.

Order: naturality_naturality (easiest) → naturality_id → naturality_comp (hardest, the associator one,
watch for the P2/P4 defeq-toxicity if `postcompComp₂` shows up). Budget each ~a focused session.
