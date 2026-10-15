/-
Copyright (c) 2026 Karles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karles Marín
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Rank of Kronecker products with the identity

## Main results

* `Matrix.rank_kronecker_one`: `(A ⊗ₖ (1 : Matrix p p K)).rank = Fintype.card p * A.rank`.
-/

@[expose] public section

open Module
open scoped Kronecker

namespace Matrix

variable {m n p K : Type*} [Field K]

section Kronecker

variable [Fintype n] [Fintype p] [DecidableEq p]

private theorem kronecker_one_mulVec_apply (A : Matrix m n K) (v : n × p → K) (i : m) (k : p) :
    ((A ⊗ₖ (1 : Matrix p p K)) *ᵥ v) (i, k) = (A *ᵥ fun j => v (j, k)) i := by
  simp [mulVec, dotProduct, kroneckerMap_apply, one_apply, Fintype.sum_prod_type]

/-- `ker (A ⊗ₖ 1) ≃ (p → ker A)`. -/
private noncomputable def kerKroneckerOneEquiv (A : Matrix m n K) :
    LinearMap.ker (A ⊗ₖ (1 : Matrix p p K)).mulVecLin ≃ₗ[K] (p → LinearMap.ker A.mulVecLin) where
  toFun v k := ⟨fun j => (v : n × p → K) (j, k), by
    rw [LinearMap.mem_ker, mulVecLin_apply]
    funext i
    have hv : (A ⊗ₖ (1 : Matrix p p K)) *ᵥ (v : n × p → K) = 0 := v.2
    rw [← kronecker_one_mulVec_apply, hv]
    rfl⟩
  invFun w := ⟨fun q => (w q.2 : n → K) q.1, by
    rw [LinearMap.mem_ker, mulVecLin_apply]
    funext ⟨i, k⟩
    rw [kronecker_one_mulVec_apply]
    exact congrFun (w k).2 i⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The rank of `A ⊗ₖ 1` is `Fintype.card p` times the rank of `A`. -/
theorem rank_kronecker_one (A : Matrix m n K) :
    (A ⊗ₖ (1 : Matrix p p K)).rank = Fintype.card p * A.rank := by
  have hk := (kerKroneckerOneEquiv (p := p) A).finrank_eq
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hk
  have h1 := rank_add_finrank_ker_mulVecLin (A ⊗ₖ (1 : Matrix p p K))
  have h2 := rank_add_finrank_ker_mulVecLin A
  rw [Fintype.card_prod, hk] at h1
  have h3 : Fintype.card p * (A.rank + finrank K (LinearMap.ker A.mulVecLin)) =
      Fintype.card p * Fintype.card n := by
    rw [h2]
  rw [Nat.mul_add] at h3
  rw [Nat.mul_comm (Fintype.card n)] at h1
  omega

end Kronecker

end Matrix
