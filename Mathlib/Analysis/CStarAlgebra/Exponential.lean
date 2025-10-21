/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Analysis.Normed.Algebra.Exponential

/-! # The exponential map from selfadjoint to unitary
In this file, we establish various properties related to the map
`fun a ↦ NormedSpace.exp ℂ A (I • a)` between the subtypes `selfAdjoint A` and `unitary A`.

## TODO

* Show that any exponential unitary is path-connected in `unitary A` to `1 : unitary A`.
* Prove any unitary whose distance to `1 : unitary A` is less than `1` can be expressed as an
  exponential unitary.
* A unitary is in the path component of `1` if and only if it is a finite product of exponential
  unitaries.
-/

open NormedSpace -- For `NormedSpace.exp`.

section Star

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [ContinuousStar A]
  [CompleteSpace A] [StarModule ℂ A]

open Complex

/-- The map from the selfadjoint real subspace to the unitary group. This map only makes sense
over ℂ. -/
@[simps]
noncomputable def selfAdjoint.expUnitary (a : selfAdjoint A) : unitary A :=
  have : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  ⟨exp ((I • a.val) : A), exp_mem_unitary_of_mem_skewAdjoint (a.prop.smul_mem_skewAdjoint conj_I)⟩

open selfAdjoint

@[simp]
lemma selfAdjoint.expUnitary_zero : expUnitary (0 : selfAdjoint A) = 1 := by
  ext
  simp

@[fun_prop]
lemma selfAdjoint.continuous_expUnitary : Continuous (expUnitary : selfAdjoint A → unitary A) := by
  simp only [continuous_induced_rng, Function.comp_def, selfAdjoint.expUnitary_coe]
  have : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℂ A
  fun_prop

theorem Commute.expUnitary_add {a b : selfAdjoint A} (h : Commute (a : A) (b : A)) :
    expUnitary (a + b) = expUnitary a * expUnitary b := by
  have : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  ext
  have hcomm : Commute (I • (a : A)) (I • (b : A)) := by
    unfold Commute SemiconjBy
    simp only [h.eq, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
  simpa only [expUnitary_coe, AddSubgroup.coe_add, smul_add] using exp_add_of_commute hcomm

theorem Commute.expUnitary {a b : selfAdjoint A} (h : Commute (a : A) (b : A)) :
    Commute (expUnitary a) (expUnitary b) :=
  calc
    selfAdjoint.expUnitary a * selfAdjoint.expUnitary b =
        selfAdjoint.expUnitary b * selfAdjoint.expUnitary a := by
      rw [← h.expUnitary_add, ← h.symm.expUnitary_add, add_comm]

end Star
