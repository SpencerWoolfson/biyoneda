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

## naturality_naturality — REDUCED TO A CLEAN CORE (2026-07-25), blocked on lift-plumbing

The descent + the RIGHT reduction simp (NOT the blunt `dsimp only [yonedaEvaluation, …]`, which
over-unfolds `B` into a 238-line record) collapses the goal to a clean 5-line statement. Working prefix:
```lean
  naturality_naturality {a b f g} η := by
    apply Cat.Hom₂.ext_app
    intro X
    obtain ⟨x⟩ := X
    simp only [Cat.Hom.toNatTrans_comp, NatTrans.comp_app, Cat.whiskerLeft_toNatTrans,
      Cat.whiskerRight_toNatTrans, whiskerLeft_app, whiskerRight_app, yonedaEvaluation_map₂_app_down,
      Cat.Hom.isoMk_hom, Cat.toCatHom₂_toNatTrans, NatIso.ofComponents_hom_app, id_eq,
      isoMk_hom_as_app, homCategory_comp_as_app, Functor.mapIso_hom, Iso.trans_hom, Iso.symm_hom]
    -- GOAL (verified, 5 lines) — this is `backwards_naturality_naturality_core η x`:
    --   (yonedaLemmaBackwardsFunctor b).map { down := (yonedaEvaluation'.map₂ η).toNatTrans.app x } ≫
    --       (backwardsNaturalityIso g { down := x }).hom =
    --     (backwardsNaturalityIso f { down := x }).hom ≫
    --       (yonedaPairing.map₂ η).toNatTrans.app ((yonedaLemmaBackwardsFunctor a).obj { down := x })
    sorry
```
`yonedaEvaluation_map₂_app_down` is the key ULift-stripping lemma (keeps `B` opaque). This clean goal
is the **naturality of `backwardsNaturalityIso` in the 1-cell parameter** and should be a standalone
`backwards_naturality_naturality_core` lemma.

**The remaining blocker (bounded lift-plumbing):** proving that clean goal needs the modification
descent `apply homCategory.ext; intro γ; apply Cat.Hom₂.ext_app; intro ZZ`, but that re-exposes a
`ULift.rec` from `(yonedaLemmaBackwardsFunctor b).map { down := m }` (its def routes through
`(catLiftEquiv _).inverse.map`). The `ULift.rec` is **stuck** because its scrutinee is
`(yonedaEvaluation.map g).toFunctor.obj { down := x }`, not a literal `{down := …}` — so `dsimp`/`simp`
won't fire it. **Fix to find next session:** a reduction lemma for `(yonedaEvaluation.map g).obj
{down := x}` → `{down := (yonedaEvaluation'.map g).obj x}` (the `.obj` analogue of
`yonedaEvaluation_map_map_down` at ~1148 — grep for an existing one or add it), applied BEFORE the
descent so the `ULift.rec` scrutinee becomes a constructor; then `(yonedaLemmaBackwardsFunctor b).map
{down:=m}` reduces via its `@[simp]` lemma + `catLiftEquiv`/`ULiftHom.equiv` (cf. the `simp
[catLiftEquiv, …]` at ~1985) to `(b.2.map ZZ.op).map m`, and the core closes by `mapComp`/naturality
(mirror `backwards_natural_core` ~1787). Alternatively, build a `catLift_hom₂`-style helper that maps
the lifted `.map` cleanly the way `catLift_hom₂_ext` does for the forwards side. The *math* is done;
this is the lift bookkeeping.

## naturality_naturality — ~90% DONE (2026-07-25), the lift-plumbing fix WORKS

The lift-plumbing fix = a `rfl` reduction lemma for the backwards functor's `.map` component (add it
to Basic near `yonedaEvaluation_map_map_down`):
```lean
lemma back_map_comp (x : Bᵒᵖ × (Bᵒᵖ ⥤ᵖ Cat.{w, v})) {A₀ B₀ : ↑(yonedaEvaluation'.obj x)}
    (m : A₀ ⟶ B₀) (c : Bᵒᵖ) (W : ↑((yoneda₀ (unop x.1)).obj c)) :
    (((((yonedaLemmaBackwardsFunctor x).map { down := m }).as.app c).toNatTrans).app W)
      = (x.2.map (Quiver.Hom.op W)).toFunctor.map m := rfl
```
(Stating `m` generic — with the source/target implicit — makes the `.map`'s internal `rcases` fire,
so it's `rfl`. It must be applied with **`erw`**, not `simp`/`rw` — the StrongTrans homCategory diamond.)

Full VERIFIED proof prefix (compiles to a clean fibre-morphism equation):
```lean
  naturality_naturality {a b f g} η := by
    apply Cat.Hom₂.ext_app
    intro X
    obtain ⟨x⟩ := X
    simp only [Cat.Hom.toNatTrans_comp, NatTrans.comp_app, Cat.whiskerLeft_toNatTrans,
      Cat.whiskerRight_toNatTrans, whiskerLeft_app, whiskerRight_app, yonedaEvaluation_map₂_app_down,
      Cat.Hom.isoMk_hom, Cat.toCatHom₂_toNatTrans, NatIso.ofComponents_hom_app, id_eq,
      isoMk_hom_as_app, homCategory_comp_as_app, Functor.mapIso_hom, Iso.trans_hom, Iso.symm_hom]
    apply homCategory.ext
    intro γ
    erw [homCategory_comp_as_app, homCategory_comp_as_app]      -- distribute the modification comp
    apply Cat.Hom₂.ext_app
    intro ZZ
    dsimp only [backwardsNaturalityIso, backwardsNaturalityIsoApp]
    simp only [Cat.Hom.toNatTrans_comp, NatTrans.comp_app, isoMk_hom_as_app, Cat.Hom.isoMk_hom,
      Cat.toCatHom₂_toNatTrans, NatIso.ofComponents_hom_app, Iso.trans_hom, Iso.symm_hom,
      Iso.app_hom, Cat.Hom.toNatIso, Iso.app_inv]
    erw [back_map_comp]                                          -- <-- the lift-plumbing fix; LHS now fully reduced
    dsimp only [yonedaPairing]
    simp only [NatTrans.toCatHom₂_toNatTrans, Cat.toCatHom₂_toNatTrans]
    dsimp only [yonedaPairingMap₂, yonedaPairingMapFunctor, Functor.whiskerLeft,
      Functor.whiskerRight, precomposing, postcomposing, precomposingCat, postcomposingCat,
      postcomposing₂]
    erw [homCategory_comp_as_app]
    simp only [Cat.Hom.toNatTrans_comp, NatTrans.comp_app, Cat.whiskerLeft_toNatTrans,
      Cat.whiskerRight_toNatTrans, whiskerLeft_app, whiskerRight_app, whiskerRight_as_app,
      whiskerLeft_as_app, isoMk_hom_as_app, Cat.toCatHom₂_toNatTrans, Cat.Hom.isoMk_hom]
    -- REMAINING GOAL (verified, ~12 lines) — a naturality square in the fibre b.2.obj γ:
    --   (b.2.map ZZ.op).map ((yonedaEvaluation'.map₂ η).app x) ≫ mapComp(g,ZZ).inv ≫ nat(g, g≫ZZ).inv
    --     = (mapComp(f,ZZ).inv ≫ nat(f, f≫ZZ).inv) ≫
    --         ((postcomp f.2).obj S).app γ |>.map (ZZ ◁ η.1.unop2) ≫
    --         ((precomp b.2 (postcomp₂ g.1.unop)).map (S ◁ η.2)).as.app γ |>.toNatTrans.app ZZ
    sorry
```
**LHS is fully reduced** (the lift-plumbing worked). The ONLY thing left is reducing the two RHS
`yonedaPairing.map₂` component terms (the `η.1` part `… .map (ZZ ◁ η.1.unop2)` and the `η.2` part
`(precomp …).map (S ◁ η.2).as.app γ …`) to explicit fibre morphisms — a further deep-but-mechanical
reduction of `postcomp`/`precomp` on the strong transformation `S = yonedaLemmaBackwardsFunctorObj a
{down:=x}`. **Then the whole equation closes by naturality** — mirror `backwards_natural_core`
(~1787): `rw [reassoc_of% ((b.2.mapComp _ _).inv.toNatTrans.naturality _), (f.2.naturality _).inv.toNatTrans.naturality _]`
and match. So: reduce the two RHS terms (find the `postcomp`/`precomp` `_app`/`_map` component lemmas
by first-diff, as with the associator golf), then the naturality close. `back_map_comp` + this prefix
are the reusable scaffolding for naturality_id and naturality_comp too.
