# Phase 2 WIP: yonedaLemmaForwards coherence (updated 2026-07-24)

STATUS: `naturality_naturality` and `naturality_id` are **CLOSED**.
Remaining: `naturality_comp`.

## The iteration harness (do this first when resuming)
The single biggest win this session. `Biyoneda/Basic.lean` builds to an olean even with
sorries, so a probe file that **imports** it iterates in ~6 s instead of a ~40 s full rebuild:

```lean
-- Biyoneda/Probe.lean   (delete when done; it is scratch)
import Biyoneda.Basic
open CategoryTheory Bicategory Bicategory.Opposite Opposite Pseudofunctor StrongTrans Functor
open scoped Pseudofunctor.StrongTrans
universe u v w v₁ v₂ u₁ u₂
attribute [local instance] uliftCategory
variable {B : Type u} [Bicategory.{w, v} B]

set_option maxHeartbeats 800000 in
def yonedaLemmaForwardsProbe : StrongTrans (@yonedaPairing B _) (@yonedaEvaluation B _) where
  -- copy the real def verbatim, rename, work the sorried fields here
```
`lake env lean Biyoneda/Probe.lean` — 6 s. Port the finished field proof back afterwards.
Harvest goal states with `field := by trace_state; sorry`.

## What `naturality_naturality` needed (now in Basic.lean)
Two new lemmas before `yonedaLemmaForwards`:

* `forwards_naturality_naturality_Z` — the evaluation-point ("Z-side") identity. This is the
  real mathematical content: 2-naturality of `Z.naturality` in `η.1`
  (`Z.naturality_naturality`) reconciled with the two unitor spellings by
  **`Bicategory.rightUnitor_inv_naturality`**.
* `forwards_naturality_naturality_core` — the whole obligation in the unlifted fibre. Splits
  `η = (η.1, η.2)`: `modification_naturality_app η.2 f.1` for the modification part,
  `Cat.Hom₂.congr_app (g.2.naturality_naturality η.1)` for the base 2-cell, then pulls the
  `η.2` component to the front with `NatTrans.naturality`/`naturality_assoc`, peels it with
  `congrArg`, and finishes via the Z-lemma.

Field proof = `apply catLift_hom₂_ext; intro Z` + `dsimp only [yonedaLemmaForwardsFunctor]` +
one `simp only` (see the file) + `exact forwards_naturality_naturality_core η Z`.

### The reduction pipeline that exposes the core (reusable for id/comp)
`dsimp only [yonedaPairing, Cat.toCatHom₂_toNatTrans, yonedaPairingMap₂, yonedaEvaluation',
postcomposing₂, postcomposingCat]` then a `simp only` with
`precomposing_map_app, postcomposing_map_app, precomposing_obj, postcomposing_obj, precomp_map,
Cat.toCatHom₂_toNatTrans, whiskerLeft_as_app, whiskerRight_as_app, homCategory_comp_as_app,
Cat.Hom.toNatTrans_comp, Cat.whiskerLeft/whiskerRight_toNatTrans, whiskerLeft_app,
whiskerRight_app, Iso.app_hom, Cat.Hom.toNatIso` then
`Pseudofunctor.StrongTrans.comp_app, Functor.comp_map, postcomp₂, postcomposingCat,
postcomp_obj, Cat.Hom.comp_toFunctor, Bicategory.id_whiskerLeft`.
This takes a pairing/evaluation 2-cell equation all the way down to `.toNatTrans.app` form.

### Lemma-name facts learned the hard way (all `#check`ed)
* It is **`Iso.app_hom`**, NOT `NatIso.app_hom` (which does not exist), that reduces
  `((Cat.Hom.toNatIso e).app p).hom`. Pair it with unfolding `Cat.Hom.toNatIso`.
* `precomposing`/`postcomposing`/`precomp`/`postcomp` are `@[simps]`; the functor-valued ones
  generate `_map_app` (e.g. `precomposing_map_app`), not `_map`.
* `postcomposing₂` is **not** `@[simps]` — it must be `dsimp`-unfolded.
* `((yoneda₀ a).map₂ η.1).toNatTrans.app (𝟙 _)` reduces to `η.1.unop2 ▷ 𝟙 _`
  via `dsimp [yoneda₀, precomposing, precomposingCat]`.
* Reducing a `Cat.Hom₂.congr_app` hypothesis: do the **whisker/comp `simp only` FIRST, then
  `dsimp [yoneda₀, …]`**. The other order makes the whisker lemmas silently no-op.

### Diamond friction — budget for it
Nearly every associativity/functoriality step needs `erw`, not `rw`: the `L1 ≫ Lmid` boundary
`≫` and the fibre `≫` sit on a different instance path than generic `Category.assoc` /
`Functor.map_comp` match at reducible transparency. Concretely: `erw [Category.assoc]`,
`erw [← Functor.map_comp_assoc]`, `erw [Iso.inv_hom_id_assoc]`.
Also: `conv_lhs/conv_rhs => rw [...]` is the way to target one side (plain `rw` and repeated
`erw` both keep re-hitting the LHS, and `slice` did not help here).
And `congr` on `gb.map P ≫ gng = gb.map Q ≫ gng` raises a spurious `.obj` goal (P and Q have
syntactically different codomains via `f.1` vs `g.1`) — **do not `congr` there**; instead
combine with `← Functor.map_comp_assoc`, `rw` the Z-lemma, and split back with
`Functor.map_comp_assoc`. That is why the Z-lemma's RHS is stated **left-associated**.

## What `naturality_id` needed (now in Basic.lean) — SOLVED
The previous session's blocker was the `(𝟙 a)`-degeneracy. **It is fully reducible**; here is
the exact recipe (the old note's fear that it might have to be transcribed verbatim was wrong):

* `Bicategory.prod_id_fst` / `prod_id_snd` turn `(𝟙 a).1`/`(𝟙 a).2` into `𝟙 a.1`/`𝟙 a.2`.
  (`obtain ⟨a1,a2⟩ := a` does **not** do this, and a bare `show … from rfl` rewrite does not
  fire either — you need these two generated lemmas.)
* `Pseudofunctor.StrongTrans.categoryStruct_id_app` collapses `(𝟙 a.2).app a.1` to `𝟙 _`,
  then `Cat.Hom.id_map` kills the surrounding `.toFunctor.map`.
* `Pseudofunctor.StrongTrans.categoryStruct_id_naturality_hom` (note the `categoryStruct_`
  prefix — plain `id_app`/`id_naturality` do **not** exist) rewrites the identity
  transformation's naturality iso to `ρ_ ≫ λ_⁻¹`.

Then `Cat.rightUnitor_hom_app`/`Cat.leftUnitor_inv_app` reduce the Cat unitors to `eqToHom`,
`erw [eqToHom_refl, eqToHom_refl]` turns them into `𝟙`, and the trailing `≫ 𝟙` must be cleared
with `erw [Category.comp_id]` — but **only after** `simp only [Cat.Hom.comp_toFunctor,
Cat.Hom.id_toFunctor, Functor.comp_obj, Functor.id_obj]` has normalised the object spelling
inside the `𝟙`; before that, `rw` fails with "motive is not type correct" and `simp` makes no
progress. (This is the propositional `≫ 𝟙` trap: `exact core` can never bridge it.)

The core, `forwards_naturality_id_core`, is the unit coherence relating `yonedaPairing.mapId`
to `a.2.mapId`. Its proof is driven by **`Z.naturality_id a.1`** (the unit coherence of `Z`
itself, taken component-wise with `Cat.Hom₂.congr_app`). After that rewrite both sides are pure
unitor data: `dsimp [postcompId₂, bicategoricalIso]` makes them explicit, and the only real
content left is **`Bicategory.unitors_equal`** (`(λ_ (𝟙 x)).hom = (ρ_ (𝟙 x)).hom`).
The functor-category unitor tails need `dsimp [Functor.leftUnitor, Functor.rightUnitor]` and
then `erw [NatTrans.comp_app, …]` — their `≫`/`𝟙` are `Cat` 2-cell ops, so plain `simp` will
not touch them.

Note `forwards_naturality_id_core` reports `declaration uses sorry`. That is **inherited**:
its statement mentions `yonedaPairing.mapId`, whose own `NatIso.ofComponents` naturality field
is still sorried (task #1, `Biyoneda/Basic.lean` ~line 306). The core's own proof is complete.

## Remaining: naturality_comp — ~95% done, the hard part is PROVEN

**`notes/naturality_comp_partial.lean.txt` is a compiling probe file** (only the final
`u_f`-transport of `fnc_core` is `sorry`ed). Copy it to `Biyoneda/Probe.lean` and resume.

**The genuine mathematical content is done: `fnc_head` is proven and integrated.**
`fnc_head` is the head unit-coherence in `B`'s hom-categories — `u_{f≫g}` composed with the
yoneda `mapComp` equals the `postcompComp₂` reorganisation with `u_g`, `u_f`. The key discovery:
`(yoneda₀).mapComp`, `postcompComp₂` (= `Bicategory.yoneda.mapComp`), and `postcomp₂.naturality`
are all built from `associatorNatIso{Right,Middle,Left}Cat`, i.e. **pure associators/unitors**,
so `fnc_head` closes by:
```
erw [show (yoneda₀ _).map g.1 |>.map u_f = g.1.unop ◁ u_f from rfl,
     show (postcomp₂ _).app c.1 |>.map u_g = u_g ▷ f.1.unop from rfl]  -- these .map's are rfl whiskerings
dsimp only [postcompComp₂, yoneda, postcomp₂, yoneda₀, associatorNatIso{Right,Middle,Left}Cat]
simp only [Cat.Hom.isoMk_hom/inv, Cat.toCatHom₂_toNatTrans, Iso.symm_hom,
  NatIso.ofComponents_hom/inv_app, homCategory_comp_as_app, isoMk_{inv,hom}_as_app]
bicategory
```

**`fnc_head` is integrated into `fnc_core`** via `hHead_t` — a `have` stating the head equality
*with the trailing `Z.naturality g.1` factor included* (so plain `rw` can't reach it but the
whole `F.map`-argument subterm can), proven `erw [← Functor.map_comp_assoc]; erw [fnc_head]; rfl`,
then `erw [hHead_t]`. This is the pattern for rewriting under `G.map (F.map _)` wrappers when the
bicategory-hom diamond blocks combining maps: **state the full wrapper-argument subterm as a
`have` and `erw` it.**  (Sharp lesson learned the hard way: a `str.replace`-based edit whose
target string didn't match leaves the file unchanged and every "experiment" silently re-runs the
old proof — verify edits actually landed before concluding a tactic "fails".)

### What is left — the mechanical `u_f`-transport (verified tractable)
After `erw [hHead_t]` both sides are postcomp-form and differ ONLY by the position of the single
`u_f = (λ_ f.1.unop).hom ≫ (ρ_ f.1.unop).inv` factor: LHS carries `(yoneda₀).map g.1 |>.map u_f`
at the head (just before `Z.naturality g.1`); RHS carries `Z.app b.1 |>.map u_f` in the tail.
Transport it through the three naturality squares. The three transport identities are each just
`(_.naturality g.1).hom.toNatTrans.naturality u_f`; the first is **verified**:
`Zc.map ((yoneda₀).map g.1 |>.map m) ≫ (Z.naturality g.1).hom.app Y
   = (Z.naturality g.1).hom.app X ≫ (a.2.map g.1).map (Z.app b.1 |>.map m)`
(literally `(Z.naturality g.1).hom.toNatTrans.naturality m`), then analogously through
`f.2.naturality g.1` and `g.2.naturality g.1` to reach the tail. Do each as a `hHead_t`-style
`have`+`erw` (state the wrapper-argument subterm including the adjacent nat factor). Both sides
then match and it closes.

### Reusable lemmas already in the partial (all verified):

* `yonedaEvaluation_map_map_down` — the missing sibling of the `_app_down` family:
  `(yonedaEvaluation.map f).toFunctor.map {down := m} = {down := (yonedaEvaluation'.map f)…m}`.
  Needed because `naturality_comp`'s RHS applies `yonedaEvaluation.map g` to a lifted 2-cell.
* `comp_naturality_hom_app` — **reusable**: the component form of a *composite* strong
  transformation's naturality constraint,
  `((η ≫ θ).naturality k).hom.app x = (θ.app _).map ((η.naturality k).hom.app x) ≫
  (θ.naturality k).hom.app ((η.app _).obj x)`. Proved from
  `categoryStruct_comp_naturality_hom` + the `iterate … erw [eqToHom_refl] …` idiom.
* The `naturality_comp` **field proof** (descent + reduction), verified to reduce the whole
  obligation to `fnc_core` by `exact`.
* `fnc_head` (the head coherence, proven — see above) and its integration `hHead_t`.

### The reduction inside `fnc_core` that reaches the postcomp-form (all in the partial)
1. `rw [comp_naturality_hom_app]` splits the LHS's `(f.2 ≫ g.2).naturality (f.1 ≫ g.1)`.
2. Unfold `yonedaPairing`/`yonedaEvaluation'`, then `dsimp only [Functor.toCatHom]` to turn
   `(yonedaPairing.map f).obj Z` into `postcomp₂ f.1.unop ≫ Z ≫ f.2`, then
   `rw [comp_naturality_hom_app, comp_naturality_hom_app]` for the RHS's nested naturality.
3. `simp only [Pseudofunctor.StrongTrans.naturality_comp_hom_app]` — **the key telescoping
   step**. Rewrites all three `naturality (f.1 ≫ g.1)` at once (for `Z`, `f.2`, `g.2`); the
   `mapComp`s then cancel in a chain (`c.2` vs `g.2`'s, `b.2` vs `f.2`'s, `a.2` vs `Z`'s).
4. Cancel those three inv/hom pairs (needs `erw`; trailing `≫ 𝟙` needs the object spelling
   normalised by `Cat.Hom.comp_toFunctor, Functor.comp_obj` first — same trap as `naturality_id`).
5. Push the `f.1`-parts rightward through the naturality squares:
   `have h := congrArg (outerFunctor).map ((…naturality…).hom.toNatTrans.naturality m)`,
   `simp only [Cat.Hom.comp_toFunctor, Functor.comp_map, Functor.comp_obj, Functor.map_comp] at h`,
   then **`erw [reassoc_of% h]`** (plain `erw [h]` fails — the pair is `A ≫ (B ≫ rest)`).
6. `erw [hHead_t]` — applies `fnc_head` under the wrappers (see above). Now both sides are
   postcomp-form and only the `u_f`-transport remains (documented above).

### Global warning (applies to the whole obligation)
Every associativity / `Functor.map_comp` / map-combine step needs `erw`, not `rw`/`simp`: the
`≫` sit on the bicategory-hom instance path (a diamond), invisible at reducible transparency.
`simp only [Functor.map_comp]` eventually "makes no progress" for that reason. To rewrite a fact
under `G.map (F.map _)` wrappers, state the *whole wrapper-argument subterm* (including adjacent
factors so it is a genuine subterm) as a `have` and `erw` it — this is what `hHead_t` does.
Budget for this friction; it is the whole difficulty, not the mathematics.
