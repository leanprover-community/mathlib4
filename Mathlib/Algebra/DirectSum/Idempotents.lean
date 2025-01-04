/-
Copyright (c) 2025 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Jujian Zhang, Andrew Yang
-/
import Mathlib.RingTheory.Idempotents
import Mathlib.Algebra.DirectSum.Decomposition

/-!
# Decomposition of the identity of a ring into orthogonal idempotents
In this file we show that if a ring `R` can be decomposed into a direct sum
of (left) ideals `R = V1 ⊕ V2 ⊕ ⬝ ⬝ ⬝ ⊕ Vn` where `1 = e₁ + e₂ + ⬝ ⬝ ⬝ + eₙ`,
then each `eᵢ` is an idempotent and they are complete orthogonal idempotents.
-/

namespace DirectSum

section OrthogonalIdempotents

variable {R I : Type*} [Ring R] [DecidableEq I] (V : I → Ideal R) [Decomposition V]

/-- The decomposition of `(1 : R)` into the direct sum of ideals which is also the identity
  of the ring induced by the directsum.-/
def idempotent   (i : I) : R :=
  decompose V 1 i

lemma decompose_eq_mul_idempotent
    (x : R) (i : I) : decompose V x i = x * idempotent V i := by
  rw [← smul_eq_mul (a := x), idempotent, ← Submodule.coe_smul, ← smul_apply, ← decompose_smul,
    smul_eq_mul, mul_one]

lemma isIdempotentElem_idempotent (i : I) : IsIdempotentElem (idempotent V i : R) := by
  rw [IsIdempotentElem, ← decompose_eq_mul_idempotent, idempotent, decompose_coe, of_eq_same]

/-- If a ring can be decomposed into direct sum of finite left ideals `Vᵢ`
  where `1 = e₁ + ... + eₙ` and `eᵢ ∈ Vᵢ`, then `eᵢ` is a family of complete
  orthogonal idempotents.-/
theorem completeOrthogonalIdempotents_idempotent [Fintype I]:
    CompleteOrthogonalIdempotents fun i ↦ idempotent V i where
  idem := isIdempotentElem_idempotent V
  ortho := fun i j hij ↦ by
    simp only
    rw [← decompose_eq_mul_idempotent, idempotent, decompose_coe,
      of_eq_of_ne (h := hij), Submodule.coe_zero]
  complete := by
    classical
    simp_rw [idempotent]
    set e := decompose V 1 with e_eq
    have : ∑ i : I, e i = ∑ i ∈ e.support, (e i : R) := by
      symm
      have := Finset.sum_subset (α := I) (β := R) (s₁ := e.support) (s₂ := Finset.univ)
        (f := fun i ↦ e i) (Finset.subset_univ e.support) (fun i rfl hi ↦ by
          simp only [ZeroMemClass.coe_eq_zero]
          simp_all only [DFinsupp.mem_support_toFun, Decidable.not_not])
      simp only at this
      rw [this]
    rw [this]; exact sum_support_decompose V 1

end OrthogonalIdempotents

end DirectSum
