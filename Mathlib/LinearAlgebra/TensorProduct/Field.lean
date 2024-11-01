/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.LinearAlgebra.TensorProduct.Subalgebra
import Mathlib.FieldTheory.Adjoin
import Mathlib.LinearAlgebra.Dimension.Free

/-!

# Some results on fields whose proof requires tensor product

This file contains some results on fields whose proof relies on tensor product
(specifically, `Subalgebra.mulMap`).

-/

variable {F E : Type*} [Field F] [Field E] [Algebra F E]
variable (A B : IntermediateField F E)

open Module

namespace IntermediateField

/-- If `A` and `B` are intermediate fields, and at least one them are algebraic, then the rank of
`A ⊔ B` is less than or equal to the product of that of `A` and `B`. Note that this result is
also true without algebraic assumption, but the proof becomes very complicated. -/
theorem rank_sup_le_of_isAlgebraic
    (halg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F B) :
    Module.rank F ↥(A ⊔ B) ≤ Module.rank F A * Module.rank F B := by
  have := A.toSubalgebra.rank_sup_le_of_free B.toSubalgebra
  rwa [← sup_toSubalgebra_of_isAlgebraic A B halg] at this

/-- If `A` and `B` are intermediate fields, then the `Module.finrank` of
`A ⊔ B` is less than or equal to the product of that of `A` and `B`. -/
theorem finrank_sup_le :
    finrank F ↥(A ⊔ B) ≤ finrank F A * finrank F B := by
  by_cases h : FiniteDimensional F A
  · have := Subalgebra.finrank_sup_le_of_free A.toSubalgebra B.toSubalgebra
    change _ ≤ finrank F A * finrank F B at this
    rwa [← sup_toSubalgebra_of_left A B] at this
  rw [FiniteDimensional, ← rank_lt_aleph0_iff, not_lt] at h
  have := LinearMap.rank_le_of_injective _ <| Submodule.inclusion_injective <|
    show Subalgebra.toSubmodule A.toSubalgebra ≤ Subalgebra.toSubmodule (A ⊔ B).toSubalgebra by simp
  rw [show finrank F A = 0 from Cardinal.toNat_apply_of_aleph0_le h,
    show finrank F ↥(A ⊔ B) = 0 from Cardinal.toNat_apply_of_aleph0_le (h.trans this), zero_mul]

end IntermediateField
