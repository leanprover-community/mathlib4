/-
Copyright (c) 2026 Janos Wolosz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janos Wolosz
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Strictly upper triangular matrices

This file extends the upper triangular matrix API from `Mathlib.LinearAlgebra.Matrix.Block`.
A matrix is strictly upper triangular if its entries on and below the diagonal vanish.

## Main results

* `Matrix.isStrictlyUpperTriangular_iff`: strict upper triangularity is equivalent to upper
  triangularity together with a zero diagonal.
* `Matrix.IsUpperTriangular.diag_mul`: diagonal projection preserves products of upper triangular
  matrices.
* `Matrix.IsStrictlyUpperTriangular.mul_upperTriangular` and
  `Matrix.IsUpperTriangular.mul_strictlyUpperTriangular`: multiplying a strictly upper triangular
  matrix by an upper triangular matrix on either side preserves strict upper triangularity.
* `Matrix.IsUpperTriangular.commutator`: over a commutative ring, the commutator of two upper
  triangular matrices is strictly upper triangular.
* `Matrix.IsStrictlyUpperTriangular.trace_eq_zero`: strictly upper triangular matrices have
  zero trace.
-/

@[expose] public section

namespace Matrix

variable {R S ι : Type*}

/-- A matrix is strictly upper triangular if its entries on and below the diagonal vanish. -/
def IsStrictlyUpperTriangular [LE ι] [Zero R] (M : Matrix ι ι R) : Prop :=
  ∀ ⦃i j⦄, j ≤ i → M i j = 0

instance [LE ι] [Zero R] [Fintype ι] [DecidableLE ι] [DecidableEq R]
    (M : Matrix ι ι R) : Decidable M.IsStrictlyUpperTriangular :=
  decidable_of_iff (∀ ij : ι × ι, ij.2 ≤ ij.1 → M ij.1 ij.2 = 0)
    ⟨fun h i j hij => h (i, j) hij, fun h _ hij => h hij⟩

@[simp]
theorem isStrictlyUpperTriangular_zero [LE ι] [Zero R] :
    (0 : Matrix ι ι R).IsStrictlyUpperTriangular := fun _ _ _ => rfl

protected theorem IsStrictlyUpperTriangular.add [LE ι] [AddZeroClass R]
    {M N : Matrix ι ι R} (hM : M.IsStrictlyUpperTriangular) (hN : N.IsStrictlyUpperTriangular) :
    (M + N).IsStrictlyUpperTriangular := fun _ _ hij => by simp [hM hij, hN hij]

protected theorem IsStrictlyUpperTriangular.neg [LE ι] [NegZeroClass R]
    {M : Matrix ι ι R} (hM : M.IsStrictlyUpperTriangular) : (-M).IsStrictlyUpperTriangular :=
  fun _ _ hij => by simp [hM hij]

protected theorem IsStrictlyUpperTriangular.sub [LE ι] [SubNegZeroMonoid R]
    {M N : Matrix ι ι R} (hM : M.IsStrictlyUpperTriangular) (hN : N.IsStrictlyUpperTriangular) :
    (M - N).IsStrictlyUpperTriangular := fun _ _ hij => by simp [hM hij, hN hij]

protected theorem IsStrictlyUpperTriangular.smul [LE ι] [Zero R] [SMulZeroClass S R]
    {M : Matrix ι ι R} (hM : M.IsStrictlyUpperTriangular) (s : S) :
    (s • M).IsStrictlyUpperTriangular := fun _ _ hij => by simp [hM hij]

protected theorem IsStrictlyUpperTriangular.isUpperTriangular [Preorder ι] [Zero R]
    {M : Matrix ι ι R} (hM : M.IsStrictlyUpperTriangular) : M.IsUpperTriangular :=
  fun _ _ hij => hM hij.le

protected theorem IsStrictlyUpperTriangular.diag_eq_zero [Preorder ι] [Zero R]
    {M : Matrix ι ι R} (hM : M.IsStrictlyUpperTriangular) : M.diag = 0 :=
  funext fun _ => hM le_rfl

theorem isStrictlyUpperTriangular_iff [PartialOrder ι] [Zero R] {M : Matrix ι ι R} :
    M.IsStrictlyUpperTriangular ↔ M.IsUpperTriangular ∧ M.diag = 0 := by
  refine ⟨fun h => ⟨h.isUpperTriangular, h.diag_eq_zero⟩, ?_⟩
  rintro ⟨hu, hd⟩ i j hij
  rcases hij.eq_or_lt with he | hij
  · subst j
    exact congrFun hd i
  · exact hu hij

/-- Diagonal projection preserves products of upper triangular matrices. -/
theorem IsUpperTriangular.diag_mul [Fintype ι] [LinearOrder ι] [NonUnitalNonAssocSemiring R]
    {M N : Matrix ι ι R} (hM : M.IsUpperTriangular) (hN : N.IsUpperTriangular) :
    (M * N).diag = M.diag * N.diag := by
  ext i
  apply Finset.sum_eq_single i
  · intro j hj hji
    rcases lt_or_gt_of_ne hji with hij | hij
    · simp [hM hij]
    · simp [hN hij]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

section Multiplication

variable [Fintype ι] [LinearOrder ι] [NonUnitalNonAssocSemiring R] {M N : Matrix ι ι R}

protected theorem IsStrictlyUpperTriangular.mul_upperTriangular
    (hM : M.IsStrictlyUpperTriangular) (hN : N.IsUpperTriangular) :
    (M * N).IsStrictlyUpperTriangular := by
  apply isStrictlyUpperTriangular_iff.mpr
  refine ⟨hM.isUpperTriangular.mul hN, ?_⟩
  rw [hM.isUpperTriangular.diag_mul hN, hM.diag_eq_zero, zero_mul]

protected theorem IsUpperTriangular.mul_strictlyUpperTriangular
    (hM : M.IsUpperTriangular) (hN : N.IsStrictlyUpperTriangular) :
    (M * N).IsStrictlyUpperTriangular := by
  apply isStrictlyUpperTriangular_iff.mpr
  refine ⟨hM.mul hN.isUpperTriangular, ?_⟩
  rw [hM.diag_mul hN.isUpperTriangular, hN.diag_eq_zero, mul_zero]

protected theorem IsStrictlyUpperTriangular.mul
    (hM : M.IsStrictlyUpperTriangular) (hN : N.IsStrictlyUpperTriangular) :
    (M * N).IsStrictlyUpperTriangular := hM.mul_upperTriangular hN.isUpperTriangular

end Multiplication

/-- Over commutative coefficients, the commutator of upper triangular matrices is strictly
upper triangular. -/
theorem IsUpperTriangular.commutator [Fintype ι] [LinearOrder ι] [NonUnitalCommRing R]
    {M N : Matrix ι ι R} (hM : M.IsUpperTriangular) (hN : N.IsUpperTriangular) :
    (M * N - N * M).IsStrictlyUpperTriangular := by
  apply isStrictlyUpperTriangular_iff.mpr
  refine ⟨(hM.mul hN).sub (hN.mul hM), ?_⟩
  rw [Matrix.diag_sub, hM.diag_mul hN, hN.diag_mul hM, mul_comm, sub_self]

protected theorem IsStrictlyUpperTriangular.trace_eq_zero [Fintype ι] [Preorder ι]
    [AddCommMonoid R] {M : Matrix ι ι R} (hM : M.IsStrictlyUpperTriangular) : M.trace = 0 :=
  Finset.sum_eq_zero fun _ _ => hM le_rfl

end Matrix
