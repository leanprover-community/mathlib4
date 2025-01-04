/-
Copyright (c) 2025 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Jujian Zhang, Andrew Yang
-/
import Mathlib.RingTheory.Idempotents
import Mathlib.Algebra.DirectSum.Decomposition

/-!
# Decomposition of the identity of a ring into orthogonal idempotents
In this file we show that if a ring `R` can be decompose into direct sum
of (left) ideals `R = V1 ⊕ V2 ⊕ ⬝ ⬝ ⬝ ⊕ Vn` where `1 = e₁ + e₂ + ⬝ ⬝ ⬝ + eₙ`,
then each `eᵢ` is an idempotent and they are orthogonal to each other.
-/

variable {R I : Type*} [Ring R]

namespace DirectSum

section OrthogonalIdempotents

/-- The decomposition of `(1 : R)` into the direct sum of ideals which is also the identity
  of the ring induced by the directsum.-/
def idempotent [DecidableEq I] (V : I → Ideal R) [Decomposition V] (i : I) : R :=
  decompose V 1 i

lemma decompose_eq_mul_idempotent [DecidableEq I] (V : I → Ideal R) [Decomposition V]
    (x : R) (i : I) : decompose V x i = x * idempotent V i := by
  rw [← smul_eq_mul (a := x), idempotent, ← Submodule.coe_smul, ← smul_apply, ← decompose_smul,
    smul_eq_mul, mul_one]

lemma isIdempotentElem_idempotent [DecidableEq I] (V : I → Ideal R)
    [Decomposition V] (i) : IsIdempotentElem (idempotent V i : R) := by
  rw [IsIdempotentElem, idempotent, ← smul_eq_mul, ← Submodule.coe_smul, ← smul_apply,
    ← decompose_smul, smul_eq_mul, mul_one, decompose_coe, of_eq_same]

/-- If a ring can be decomposed into direct sum of left ideals `Vᵢ`
  where `1 = e₁ + ... + eₙ` and `eᵢ ∈ Vᵢ`, then `eᵢ` is a family of orthogonal
  idempotents.-/
theorem isOrthoIdempotent_idempotent [DecidableEq I] (V : I → Ideal R)
    [Decomposition V] :
    OrthogonalIdempotents (R := R) fun i ↦ idempotent V i where
  idem := isIdempotentElem_idempotent V
  ortho := fun i j hij ↦ by
    simp only
    rw [← smul_eq_mul, idempotent, idempotent, ← Submodule.coe_smul, ← smul_apply,
      ← decompose_smul, smul_eq_mul, mul_one, decompose_coe, of_eq_of_ne (h := hij),
      Submodule.coe_zero]

end OrthogonalIdempotents

end DirectSum
