import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.CategoryTheory.Triangulated.SpectralObject

open CategoryTheory Category Limits Triangulated

variable (C : Type _) [Category C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

namespace HomotopyCategory

open CochainComplex.MappingCone

noncomputable def spectralObjectMappingCone :
    SpectralObject (HomotopyCategory C (ComplexShape.up ℤ)) (CochainComplex C ℤ) where
  ω₁ := arrowFunctor C ⋙ HomotopyCategory.quotient _ _
  δ :=
    { app := fun D => ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapTriangle.obj (mappingConeCompTriangle D.f D.g)).mor₃
      naturality := fun D₁ D₂ φ => by
        have eq := mappingConeCompTriangle_mor₃_naturality D₁.f D₁.g D₂.f D₂.g φ
        dsimp at eq ⊢
        simp only [assoc, ← Functor.map_comp_assoc, eq]
        simp only [Functor.map_comp, assoc, Functor.commShiftIso_hom_naturality] }
  distinguished' := fun D => mappingConeCompTriangle_distinguished D.f D.g

end HomotopyCategory
