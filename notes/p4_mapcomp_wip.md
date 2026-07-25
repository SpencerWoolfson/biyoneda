# P4 `yonedaPairing.mapComp` naturality — WIP (resume here)

**Status (2026-07-25):** `mapId` naturality is DONE and committed (`30387f1`). `mapComp`
naturality (Basic.lean ~line 323, the second `?_` of the `NatIso.ofComponents` in the `mapComp`
field) is **mathematically solved but blocked on a performance wall** in the endgame. 7 explicit
sorries; this is one of them.

## The math is done

The goal (after `apply homCategory.ext; intro b; dsimp`) is naturality of the `mapComp` component
iso w.r.t. the modification `η : X ⟶ Y`. The only non-coherence content is a single interchange
of `η` past the coherence 2-cell `φ := (postcompComp₂ g.1.unop f.1.unop).hom.as.app b`. Descending
to points reduces it to exactly `η`'s `NatTrans.naturality` against `φ`.

## The working reduction (verified in a probe)

In the `mapComp` field, replace the second bullet's `sorry` with:

```lean
· intro X Y η                       -- MUST rename from `f` (the field's `intro X Y f` shadows
  apply homCategory.ext             --   the outer 1-cell `f`; use `η` so `f`, `g` stay in scope)
  intro b
  dsimp
  ext Z
  simp only [Cat.Hom.toNatTrans_comp, NatTrans.comp_app, Cat.whiskerLeft_toNatTrans,
    Cat.whiskerRight_toNatTrans, whiskerLeft_app, whiskerRight_app,
    Cat.associator_hom_app, Cat.associator_inv_app, Category.assoc, Category.id_comp,
    Category.comp_id, Functor.comp_obj, eqToHom_refl, eqToHom_map, eqToHom_trans,
    Cat.Hom.comp_toFunctor, Functor.comp_map, Functor.map_comp,
    NatTrans.naturality, NatTrans.naturality_assoc]
  -- goal here (VERIFIED): g2.map(f2.map(η_a ≫ Y.map φZ)) = g2.map(f2.map(X.map φZ ≫ η_b))
  --   where g2 = g.2.app b, f2 = f.2.app b, φZ = (postcompComp₂ ..).hom.as.app b .toNatTrans.app Z
  have hnat := ((η.as.app b).toNatTrans.naturality
    (((postcompComp₂ g.1.unop f.1.unop).hom.as.app b).toNatTrans.app Z)).symm
  simp only [Pseudofunctor.StrongTrans.comp_app, Cat.Hom.comp_toFunctor,
    Functor.comp_obj] at hnat        -- normalizes hnat's η index to MATCH the goal exactly
  simp only [← Functor.map_comp]      -- combine to g2.map(f2.map(hnat.LHS)) = g2.map(f2.map(hnat.RHS))
  -- ⟹ goal is now literally `congrArg (g2.map ∘ f2.map) hnat`.  <<< PERF WALL: see below
  sorry
```

Everything above the final `sorry` is **verified and fast** (~4 s): after the two `simp only`s,
`hnat.LHS`/`hnat.RHS` are syntactically identical to the goal's inner terms (confirmed by
`trace_state`). So the goal is exactly `g2.map (f2.map hnat.LHS) = g2.map (f2.map hnat.RHS)`.

## The perf wall (what's blocking, what was tried)

Closing that last step **times out (>150 s wall)** with every approach tried, because `g.2.app b`,
`f.2.app b`, and the object indices contain `postcompComp₂`/`postcomp₂` (both carry
`set_option backward.isDefEq.respectTransparency false` in Mathlib — defeq-toxic). Any tactic that
*unifies against* the huge bundled goal term explodes:

- `exact congrArg _ (congrArg _ hnat)` — timeout (HO/dependent-`map` unification)
- `exact congrArg (g.2.app b).toFunctor.map (congrArg (f.2.app b).toFunctor.map hnat)` — timeout
- `apply congrArg; apply congrArg; exact hnat` — timeout
- `congr 2; exact hnat` — timeout
- `simp only [← Functor.map_comp, hnat]` — timeout (hnat has huge `≫`-headed LHS → slow matching)
- `rw [hnat]` / `conv_lhs => rw [hnat]` — timeout (motive over huge term)
- standalone `lemma map_map_congr (F G) (h : m = n) : G.map (F.map m) = G.map (F.map n)` +
  `exact map_map_congr _ _ hnat` — timeout, even `with_reducible` — timeout
- `generalize (…postcompComp₂…app Z) = φ` then close — timeout (objects still toxic)

Note: the SPLIT lemmas `Cat.Hom.comp_toFunctor, Functor.comp_map` in the big `simp` turn the single
`(f2≫g2).map` into `g2.map (f2.map ..)`; they also normalize the goal's η index into
`(postcomp₂ f).app.obj ((postcomp₂ g).app.obj Z)`. That's why `NatTrans.naturality` fires on the LHS
but NOT the RHS inside the big simp (RHS index isn't *reducibly* equal to `cod φ`), so the big simp
alone can't finish — hence the manual `hnat`.

## Candidate next approaches (for a fresh session)

1. **Abandon `ext Z` (point descent).** It is what drags `postcompComp₂` down to object level and
   creates the toxicity. Instead close at the **natTrans (Cat 2-cell) level** using the interchange
   `key := whisker_exchange (postcompComp₂ g.1.unop f.1.unop).hom.as.app b (η.as.app b)`
   (VERIFIED to typecheck: `P ◁ η ≫ φ ▷ Y = φ ▷ X ≫ (Pg≫Pf) ◁ η`). The blocker there is *adjacency*:
   in the raw/`bicategory_nf`'d goal, `η` and `φ` are separated by associator **morphisms**
   (`bicategory` handles those but then can't do the opaque interchange; `simp only
   [whisker_exchange_assoc]` doesn't fire because non-adjacent). Need to push `η` adjacent to `φ`
   via `associator_naturality_{left,middle,right}` / `whisker_assoc` **then** `key` **then**
   `bicategory`. This keeps `postcompComp₂` opaque (never unfolded) → should avoid the toxicity.
   Contrast: `mapId` worked at natTrans level in ONE line (`simp only [whisker_exchange_assoc];
   bicategory`) precisely because its coherence chain had `η` and `φ` already adjacent.
2. **If keeping point descent:** abstract *both* the toxic morphism `φ` AND its source/target
   **objects** (`(postcomp₂ (g≫f)).app b .obj Z`, etc.) to opaque locals before the closer, so the
   final congruence never unfolds `postcomp₂`. Generalizing φ alone was not enough.
3. Try a `maxHeartbeats`-bumped run in the background to see if any closer is *slow-but-terminating*
   (would at least give a (too-slow) proof to then optimize).

Approach 1 is most promising — it sidesteps the root cause (point-level `postcompComp₂` toxicity).
