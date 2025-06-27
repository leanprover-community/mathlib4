/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.CategoryTheory.Triangulated.SpectralObject

/-!
# The spectral object with values in the homotopy category
-/

open CategoryTheory Category Limits Triangulated

variable (C : Type _) [Category C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

namespace HomotopyCategory

open CochainComplex.mappingCone

@[simps]
noncomputable def composableArrowsFunctor :
    ComposableArrows (CochainComplex C ℤ) 1 ⥤ CochainComplex C ℤ where
  obj f := CochainComplex.mappingCone (f.map' 0 1)
  map {f₁ f₂} φ := map _ _ (φ.app 0) (φ.app 1) (ComposableArrows.naturality' φ 0 1)
  map_id f := map_id _
  map_comp φ₁ φ₂ := by
    apply map_comp

noncomputable def spectralObjectMappingCone :
    SpectralObject (HomotopyCategory C (ComplexShape.up ℤ)) (CochainComplex C ℤ) where
  ω₁ := composableArrowsFunctor C ⋙ HomotopyCategory.quotient _ _
  δ' :=
    { app := fun D => ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapTriangle.obj
        (CochainComplex.mappingConeCompTriangle (D.map' 0 1) (D.map' 1 2))).mor₃
      naturality := fun D₁ D₂ φ => by
        obtain ⟨_, _, _, f, g, rfl⟩ := ComposableArrows.mk₂_surjective D₁
        obtain ⟨_, _, _, f', g', rfl⟩ := ComposableArrows.mk₂_surjective D₂
        have eq := CochainComplex.mappingConeCompTriangle_mor₃_naturality f g f' g' φ
        dsimp at eq ⊢
        simp only [assoc, ← Functor.map_comp_assoc]
        erw [eq]
        simp only [Functor.map_comp, assoc]
        rw [Functor.commShiftIso_hom_naturality]
        rfl }
  distinguished' D := by
    obtain ⟨_, _, _, f, g, rfl⟩ := ComposableArrows.mk₂_surjective D
    exact HomotopyCategory.mappingConeCompTriangleh_distinguished f g

end HomotopyCategory
