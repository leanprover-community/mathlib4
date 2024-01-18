import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.SpectralObject

open CategoryTheory Triangulated

variable (C : Type _) [Category C] [Abelian C] [HasDerivedCategory C]

namespace DerivedCategory

noncomputable def spectralObjectMappingCone :
    SpectralObjectNew (DerivedCategory C) (CochainComplex C ℤ) :=
    (HomotopyCategory.spectralObjectMappingCone C).mapTriangulatedFunctor Qh

end DerivedCategory
