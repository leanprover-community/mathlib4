/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
# Exact functors

In this file, it is shown that additive functors which preserves homology
also preserves finite limits and finite colimits.

TODO: provive alternate characterizations of left/right exact functors
in terms of preservation of exactness.

-/

namespace CategoryTheory

open Limits ZeroObject

namespace Functor

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  (F : C ⥤ D) [F.Additive] [F.PreservesHomology] [HasZeroObject C]

/-- An additive functor which preserves homology preserves finite limits. -/
noncomputable def preservesFiniteLimitsOfPreservesHomology
    [HasFiniteProducts C] [HasKernels C] : PreservesFiniteLimits F := by
  have := fun {X Y : C} (f : X ⟶ Y) => PreservesHomology.preservesKernel F f
  have : HasBinaryBiproducts C := HasBinaryBiproducts.of_hasBinaryProducts
  have : HasEqualizers C := Preadditive.hasEqualizers_of_hasKernels
  have : HasZeroObject D :=
    ⟨F.obj 0, by rw [IsZero.iff_id_eq_zero, ← F.map_id, id_zero, F.map_zero]⟩
  exact preservesFiniteLimitsOfPreservesKernels F

/-- An additive which preserves homology preserves finite colimits. -/
noncomputable def preservesFiniteColimitsOfPreservesHomology
    [HasFiniteCoproducts C] [HasCokernels C] : PreservesFiniteColimits F := by
  have := fun {X Y : C} (f : X ⟶ Y) => PreservesHomology.preservesCokernel F f
  have : HasBinaryBiproducts C := HasBinaryBiproducts.of_hasBinaryCoproducts
  have : HasCoequalizers C := Preadditive.hasCoequalizers_of_hasCokernels
  have : HasZeroObject D :=
    ⟨F.obj 0, by rw [IsZero.iff_id_eq_zero, ← F.map_id, id_zero, F.map_zero]⟩
  exact preservesFiniteColimitsOfPreservesCokernels F

end Functor

end CategoryTheory
