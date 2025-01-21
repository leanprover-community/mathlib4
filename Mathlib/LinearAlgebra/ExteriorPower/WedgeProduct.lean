/-
Copyright (c) 2024 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison
-/

import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
Documentation
-/

namespace exteriorPower

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

#check Matrix.vecCons
#check Matrix.vecTail

theorem mul_ιMulti_left {k : ℕ} (m : M) (v : Fin k → M) :
  (ExteriorAlgebra.ι R m) * (ιMulti R k v : ExteriorAlgebra R M) =
  ιMulti R (k + 1) (Matrix.vecCons m v) := by
  simp only [ιMulti_apply, ExteriorAlgebra.ιMulti_succ_apply, Matrix.cons_val_zero,
    Matrix.tail_cons]

theorem mul_ιMulti_left_degree {k : ℕ} (m : M) (v : Fin k → M) :
  (ExteriorAlgebra.ι R m) * (ιMulti R k v) ∈ ⋀[R]^(k+1) M := by
  rw [mul_ιMulti_left]
  exact (Set.range_subset_iff.mp (ExteriorAlgebra.ιMulti_range R (k+1))) _

theorem mul_ιMulti_degree {k l : ℕ} (v : Fin k → M) (w : Fin l → M) :
  ((ιMulti R k v) : ExteriorAlgebra R M) * (ιMulti R l w) ∈ ⋀[R]^(k+l) M := by
  induction' k with k hk
  · simp only [zero_add, ιMulti_apply, ExteriorAlgebra.ιMulti_zero_apply, one_mul]
    exact (Set.range_subset_iff.mp (ExteriorAlgebra.ιMulti_range R l)) _
  · rw [ιMulti_apply, ExteriorAlgebra.ιMulti_succ_apply, ← ιMulti_apply]
    rw [mul_assoc]
    sorry

theorem mul_degree {k l : ℕ} (α : ⋀[R]^k M) (β : ⋀[R]^l M) :
  (α : ExteriorAlgebra R M) * β ∈ ⋀[R]^(k+l) M := by


  sorry

end exteriorPower
