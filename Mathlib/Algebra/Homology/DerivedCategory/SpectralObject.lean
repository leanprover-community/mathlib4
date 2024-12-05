/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.SpectralObject

/-!
# The mapping cone spectral object

-/
open CategoryTheory Triangulated

variable (C : Type _) [Category C] [Abelian C] [HasDerivedCategory C]

namespace DerivedCategory

noncomputable def spectralObjectMappingCone :
    SpectralObject (DerivedCategory C) (CochainComplex C ℤ) :=
    (HomotopyCategory.spectralObjectMappingCone C).mapTriangulatedFunctor Qh

end DerivedCategory
