/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Analysis.NormedSpace.Exponential

#align_import analysis.normed_space.star.exponential from "leanprover-community/mathlib"@"1e3201306d4d9eb1fd54c60d7c4510ad5126f6f9"

/-! # The exponential map from selfadjoint to unitary
In this file, we establish various properties related to the map `fun a ↦ exp ℂ A (I • a)`
between the subtypes `selfAdjoint A` and `unitary A`.

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
  ⟨exp ℂ ((I • a.val) : A),
      exp_mem_unitary_of_mem_skewAdjoint _ (a.prop.smul_mem_skewAdjoint conj_I)⟩
#align self_adjoint.exp_unitary selfAdjoint.expUnitary

open selfAdjoint

theorem Commute.expUnitary_add {a b : selfAdjoint A} (h : Commute (a : A) (b : A)) :
    expUnitary (a + b) = expUnitary a * expUnitary b := by
  ext
  have hcomm : Commute (I • (a : A)) (I • (b : A)) := by
    unfold Commute SemiconjBy
    simp only [h.eq, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
  simpa only [expUnitary_coe, AddSubgroup.coe_add, smul_add] using exp_add_of_commute hcomm
#align commute.exp_unitary_add Commute.expUnitary_add

theorem Commute.expUnitary {a b : selfAdjoint A} (h : Commute (a : A) (b : A)) :
    Commute (expUnitary a) (expUnitary b) :=
  calc
    selfAdjoint.expUnitary a * selfAdjoint.expUnitary b =
        selfAdjoint.expUnitary b * selfAdjoint.expUnitary a := by
      rw [← h.expUnitary_add, ← h.symm.expUnitary_add, add_comm]
#align commute.exp_unitary Commute.expUnitary

end Star
