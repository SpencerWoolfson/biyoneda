import Biyoneda.Evaluation
namespace Probe
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Pseudofunctor
open scoped CategoryTheory.Pseudofunctor.StrongTrans
universe u v w
variable {C : Type u} [Bicategory.{w, v} C]
variable {x y z : C} {F G H : C ⥤ᵖ Cat.{w, v}}

-- p1: evalMapComp specialised at the identity on the LEFT, already normalised
lemma p1 (u : x ⟶ y) (α : F ⟶ G) :
    (evalMapComp (𝟙 x) (𝟙 F) u α).hom
      = (F.mapComp (𝟙 x) u).hom ▷ (𝟙 (F.obj y) ≫ α.app y) ≫
        (α_ (F.map (𝟙 x)) (F.map u) (𝟙 (F.obj y) ≫ α.app y)).hom ≫
        F.map (𝟙 x) ◁ ((α_ (F.map u) (𝟙 (F.obj y)) (α.app y)).inv ≫
          ((ρ_ (F.map u)).hom ≫ (λ_ (F.map u)).inv) ▷ α.app y ≫
          (α_ (𝟙 (F.obj x)) (F.map u) (α.app y)).hom) ≫
        (α_ (F.map (𝟙 x)) (𝟙 (F.obj x)) (F.map u ≫ α.app y)).inv := rfl

-- p2: LHS of left_unitor, already normalised
lemma p2 (u : x ⟶ y) (α : F ⟶ G) :
    evalMap₂ (λ_ u).hom (λ_ α).hom
      = F.map₂ (λ_ u).hom ▷ (𝟙 (F.obj y) ≫ α.app y) ≫
        F.map u ◁ (λ_ (α.app y)).hom := rfl

-- p3: evalMapComp specialised at the identity on the RIGHT
lemma p3 (u : x ⟶ y) (α : F ⟶ G) :
    (evalMapComp u α (𝟙 y) (𝟙 G)).hom
      = (F.mapComp u (𝟙 y)).hom ▷ (α.app y ≫ 𝟙 (G.obj y)) ≫
        (α_ (F.map u) (F.map (𝟙 y)) (α.app y ≫ 𝟙 (G.obj y))).hom ≫
        F.map u ◁ ((α_ (F.map (𝟙 y)) (α.app y) (𝟙 (G.obj y))).inv ≫
          (α.naturality (𝟙 y)).hom ▷ 𝟙 (G.obj y) ≫
          (α_ (α.app y) (G.map (𝟙 y)) (𝟙 (G.obj y))).hom) ≫
        (α_ (F.map u) (α.app y) (G.map (𝟙 y) ≫ 𝟙 (G.obj y))).inv := rfl

-- p4: LHS of right_unitor
lemma p4 (u : x ⟶ y) (α : F ⟶ G) :
    evalMap₂ (ρ_ u).hom (ρ_ α).hom
      = F.map₂ (ρ_ u).hom ▷ (α.app y ≫ 𝟙 (G.obj y)) ≫
        F.map u ◁ (ρ_ (α.app y)).hom := rfl

example (u : x ⟶ y) (α : F ⟶ G) :
    evalMap₂ (λ_ u).hom (λ_ α).hom
      = (evalMapComp (𝟙 x) (𝟙 F) u α).hom ≫
        (F.mapId x).hom ▷ evalMap u α ≫ (λ_ (evalMap u α)).hom := by
  rw [p2, p1, F.map₂_left_unitor]
  dsimp only [evalMap]
  bicategory_nf
  simp
  slice_rhs 3 4 => rw [Bicategory.triangle_assoc]

example (u : x ⟶ y) (α : F ⟶ G) :
    evalMap₂ (ρ_ u).hom (ρ_ α).hom
      = (evalMapComp u α (𝟙 y) (𝟙 G)).hom ≫
        evalMap u α ◁ (G.mapId y).hom ≫ (ρ_ (evalMap u α)).hom := by
  sorry
end Probe
