import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.CategoryTheory.Triangulated.SpectralObjectNew

open CategoryTheory Category Limits Triangulated

variable (C : Type _) [Category C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

namespace HomotopyCategory

open CochainComplex.MappingCone

@[simps]
noncomputable def composableArrowsFunctor : ComposableArrows (CochainComplex C ℤ) 1 ⥤ CochainComplex C ℤ where
  obj f := CochainComplex.mappingCone (f.map' 0 1)
  map {f₁ f₂} φ := map' _ _ (φ.app 0) (φ.app 1) (ComposableArrows.naturality' φ 0 1)
  map_id f := map'_id _
  map_comp φ₁ φ₂ := map'_comp _ _ _ _ _ _ _ (ComposableArrows.naturality' φ₁ 0 1)
      (ComposableArrows.naturality' φ₂ 0 1)

set_option maxHeartbeats 400000 in
noncomputable def spectralObjectMappingCone :
    SpectralObjectNew (HomotopyCategory C (ComplexShape.up ℤ)) (CochainComplex C ℤ) where
  ω₁ := composableArrowsFunctor C ⋙ HomotopyCategory.quotient _ _
  δ' :=
    { app := fun D => ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapTriangle.obj (mappingConeCompTriangle (D.map' 0 1) (D.map' 1 2))).mor₃
      naturality := fun D₁ D₂ φ => by
        obtain ⟨_, _, _, f, g, rfl⟩ := ComposableArrows.mk₂_surjective D₁
        obtain ⟨_, _, _, f', g', rfl⟩ := ComposableArrows.mk₂_surjective D₂
        have eq := mappingConeCompTriangle_mor₃_naturality f g f' g'
          { τ₀ := φ.app 0
            τ₁ := φ.app 1
            τ₂ := φ.app 2
            commf := (ComposableArrows.naturality' φ 0 1).symm
            commg := (ComposableArrows.naturality' φ 1 2).symm }
        dsimp at eq ⊢
        simp only [assoc, ← Functor.map_comp_assoc]
        erw [eq]
        simp only [Functor.map_comp, assoc]
        rw [Functor.commShiftIso_hom_naturality]
        rfl }
  distinguished' D := by
    obtain ⟨_, _, _, f, g, rfl⟩ := ComposableArrows.mk₂_surjective D
    exact mappingConeCompTriangle_distinguished f g

end HomotopyCategory
