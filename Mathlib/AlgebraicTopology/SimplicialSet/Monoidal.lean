import Mathlib.AlgebraicTopology.SimplicialSet
import Mathlib.CategoryTheory.ChosenFiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes

universe v u

open Simplicial CategoryTheory MonoidalCategory

namespace SSet

instance : ChosenFiniteProducts SSet.{v} where
  terminal := FunctorToTypes.functorEmptyLimitCone _
  product := FunctorToTypes.binaryProductLimitCone

def unitHomEquiv (K : SSet.{v}) : (𝟙_ _ ⟶ K) ≃ K _[0] where
  toFun φ := φ.app _ PUnit.unit
  invFun x :=
    { app := fun Δ _ => K.map (SimplexCategory.const Δ.unop [0] 0).op x
      naturality := fun Δ Δ' f => by
        ext ⟨⟩
        dsimp
        rw [← FunctorToTypes.map_comp_apply]
        rfl }
  left_inv φ := by
    ext Δ ⟨⟩
    dsimp
    rw [← FunctorToTypes.naturality]
    rfl
  right_inv x := by simp

@[simp]
lemma leftUnitor_hom_apply (K : SSet.{v}) {Δ : SimplexCategoryᵒᵖ} (x : (𝟙_ _ ⊗ K).obj Δ) :
  (λ_ K).hom.app Δ x = x.2 := rfl

@[simp]
lemma leftUnitor_inv_apply (K : SSet.{v}) {Δ : SimplexCategoryᵒᵖ} (x : K.obj Δ) :
  (λ_ K).inv.app Δ x = ⟨PUnit.unit, x⟩ := rfl

@[simp]
lemma rightUnitor_hom_apply (K : SSet.{v}) {Δ : SimplexCategoryᵒᵖ} (x : (K ⊗ 𝟙_ _).obj Δ) :
  (ρ_ K).hom.app Δ x = x.1 := rfl

@[simp]
lemma rightUnitor_inv_apply (K : SSet.{v}) {Δ : SimplexCategoryᵒᵖ} (x : K.obj Δ) :
  (ρ_ K).inv.app Δ x = ⟨x, PUnit.unit⟩ := rfl

@[simp]
lemma whiskerLeft_apply (K : SSet.{v}) {L L' : SSet.{v}} (g : L ⟶ L')
    {Δ : SimplexCategoryᵒᵖ} (x : (K ⊗ L).obj Δ) :
    (K ◁ g).app Δ x = ⟨x.1, g.app Δ x.2⟩ := rfl

@[simp]
lemma whiskerRight_apply {K K' : SSet.{v}} (f : K ⟶ K') (L : SSet.{v})
    {Δ : SimplexCategoryᵒᵖ} (x : (K ⊗ L).obj Δ) :
    (f ▷ L).app Δ x = ⟨f.app Δ x.1, x.2⟩ := rfl

@[simp]
lemma associator_hom_apply (K L M : SSet.{v}) {Δ : SimplexCategoryᵒᵖ} (x : ((K ⊗ L) ⊗ M).obj Δ) :
  (α_ K L M).hom.app Δ x = ⟨x.1.1, x.1.2, x.2⟩ := rfl

@[simp]
lemma associator_inv_apply (K L M : SSet.{v}) {Δ : SimplexCategoryᵒᵖ} (x : (K ⊗ L ⊗ M).obj Δ) :
  (α_ K L M).inv.app Δ x = ⟨⟨x.1, x.2.1⟩, x.2.2⟩ := rfl

end SSet
