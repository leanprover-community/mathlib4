/-
Copyright (c) 2026 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu, Aristotle AI
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

import Mathlib.LinearAlgebra.InvariantBasisNumber
import Mathlib.LinearAlgebra.Matrix.SemiringInverse
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Linear independence and nonsingularity of matrices

In this file we formalize several theorems proved by Yi-Jia Tan in his paper [Tan2016]
*Free sets and free subsemimodules in a semimodule*. As consequences, we show that
commutative semirings satisfy the strong rank condition, and that the columns of a square matrix
are linearly independent if and only if the matrix is nonsingular (over a commutative ring,
a matrix is nonsingular if and only if its determinant is not a zero divisor).

## Main theorems

* `Matrix.Nonsingular.of_linearIndependent_col`: if the columns of a square matrix are linearly
  independent, then the matrix is nonsingular. Corollary 3.2(1) of [Tan2016].

* `Matrix.Nonsingular.linearIndependent_col`: if a matrix over a commutative semiring with
  cancellative addition is nonsingular, then its columns are linearly independent.
  Corollary 3.2(2) of [Tan2016].

* `CommSemiring.strongRankCondition_of_nontrivial`: a commutative semiring satisfies the strong
  rank condition.
-/

variable {R m n : Type*} [CommSemiring R] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
variable {A : Matrix n n R}

namespace Matrix

public section

lemma detpBalanced_iff_sub_mul_det_eq_zero {R : Type*} [CommRing R] {A : Matrix n n R} {a b : R} :
    A.DetpBalanced a b ↔ (a - b) * A.det = 0 := by
  grind [DetpBalanced, det_eq_detp_sub_detp]

lemma nonsingular_iff_det_mem_nonZeroDivisors {R : Type*} [CommRing R]
    {A : Matrix n n R} : A.Nonsingular ↔ A.det ∈ nonZeroDivisors R := by
  simp_rw [Nonsingular, detpBalanced_iff_sub_mul_det_eq_zero,
    ← nonZeroDivisorsRight_eq_nonZeroDivisors, mem_nonZeroDivisorsRight_iff]
  exact ⟨fun h x eq ↦ h x 0 (by simpa), fun h a b eq ↦ sub_eq_zero.mp <| h _ (by simpa)⟩

/-- If the columns of a square matrix are linearly independent, then the matrix is nonsingular. -/
theorem Nonsingular.of_linearIndependent_col (ind : LinearIndependent R A.col) : A.Nonsingular := by
  intro a b bal
  let P (r : ℕ) : Prop := ∀ (m : Type) [Fintype m] [DecidableEq m] (le : Fintype.card m = r)
    (f g : m → n), (A.submatrix f g).DetpBalanced a b
  classical
  let r := Nat.find ⟨_, show P _ from fun m _ _ eq ↦ bal.submatrix_of_card_le eq.ge⟩
  have hr : P r := Nat.find_spec _
  by_cases h0 : r = 0
  · simpa [DetpBalanced] using hr Empty (by simp [h0]) Empty.elim Empty.elim
  have := Nat.find_min _ (Nat.pred_lt h0)
  simp_rw [P] at this; push Not at this
  obtain ⟨m, _, _, eq, f, g, nbal⟩ := this
  have hg : ¬ g.Surjective :=
    fun surj ↦ nbal <| bal.submatrix_of_card_le (Fintype.card_le_of_surjective g surj) ..
  rw [Function.Surjective] at hg; push Not at hg
  obtain ⟨j₀, h₀⟩ := hg
  let D : Matrix m m R := A.submatrix f g
  let Aj (j : m) : Matrix m m R := A.submatrix f (Function.update g j j₀)
  let v (a b : R) : n →₀ R := ∑ j : m, .single (g j) (a * (Aj j).detp (-1) + b * (Aj j).detp 1) +
    .single j₀ (a * D.detp 1 + b * D.detp (-1))
  have veq := congr($(ind (a₁ := v a b) (a₂ := v b a) ?_) j₀)
  · exact (nbal <| by simpa [DetpBalanced, v, h₀] using veq).elim
  ext i
  let Ai := A.submatrix (Option.rec i f) (Option.rec j₀ g)
  have (s : ℤˣ) : Ai.detp s = ∑ j, detp (-s) (Aj j) * A.col (g j) i + detp s D * A.col j₀ i := by
    simp_rw [mul_comm]; rw [detp_option_expand_row_none, add_comm]
    congr!; ext
    simp only [submatrix_apply, Ai, Aj, Function.update]
    split_ifs <;> simp
  have (a b : R) : (v a b).linearCombination R A.col i = a * Ai.detp 1 + b * Ai.detp (-1) := by
    simp_rw [v, map_add, map_sum, Finsupp.linearCombination_single, Pi.add_apply, Finset.sum_apply,
      add_smul, Pi.add_apply, Finset.sum_add_distrib, Pi.smul_apply, smul_eq_mul, mul_assoc,
      ← Finset.mul_sum, add_add_add_comm, ← mul_add, this, neg_neg]
  rw [this, this]
  exact hr (Option m) (by rw [Fintype.card_option, eq]; exact Nat.succ_pred h0) ..

theorem Nonsingular.of_linearIndependent_row (ind : LinearIndependent R A.row) : A.Nonsingular := by
  rw [← nonsingular_transpose_iff]; exact .of_linearIndependent_col ind

theorem Nonsingular.of_leftRegular (h : IsLeftRegular A) : A.Nonsingular :=
  .of_linearIndependent_col (by rwa [← mulVec_injective_iff, ← isLeftRegular_iff_mulVec_injective])

theorem Nonsingular.of_rightRegular (h : IsRightRegular A) : A.Nonsingular :=
  .of_linearIndependent_row (by rwa [← vecMul_injective_iff, ← isRightRegular_iff_vecMul_injective])

variable [IsCancelAdd R]

/-- If a matrix over a commutative semiring with cancellative addition is nonsingular, then its
columns are linearly independent. Generalizes `Matrix.linearIndependent_cols_of_det_ne_zero`. -/
theorem Nonsingular.linearIndependent_col (hA : A.Nonsingular) : LinearIndependent R A.col :=
  mulVec_injective_iff.mp fun x y eq ↦ funext fun k ↦ hA _ _ <| show _ = _ by
    have hp := congr((A.adjp 1 *ᵥ $eq) k)
    have hm := congr((A.adjp (-1) *ᵥ $eq) k)
    simp_rw [mulVec_mulVec, mulVec, dotProduct, ← Finset.sum_erase_add _ _ (Finset.mem_univ k),
      ← Finset.filter_ne, adjp_mul_apply_eq] at hp hm
    iterate 2 rw [Finset.sum_congr rfl fun i h ↦ congr_arg (· * _) <|
      adjp_mul_apply_ne _ _ _ (Finset.mem_filter.mp h).2] at hp
    grind

theorem Nonsingular.linearIndependent_row (hA : A.Nonsingular) : LinearIndependent R A.row :=
  hA.transpose.linearIndependent_col

theorem linearIndependent_col_iff : LinearIndependent R A.col ↔ A.Nonsingular :=
  ⟨.of_linearIndependent_col, (·.linearIndependent_col)⟩

theorem linearIndependent_row_iff : LinearIndependent R A.row ↔ A.Nonsingular :=
  ⟨.of_linearIndependent_row, (·.linearIndependent_row)⟩

theorem isLeftRegular_iff_nonsingular : IsLeftRegular A ↔ A.Nonsingular := by
  rw [isLeftRegular_iff_mulVec_injective, mulVec_injective_iff, linearIndependent_col_iff]

theorem isRightRegular_iff_nonsingular : IsRightRegular A ↔ A.Nonsingular := by
  rw [isRightRegular_iff_vecMul_injective, vecMul_injective_iff, linearIndependent_row_iff]

lemma Nonsingular.mul {B : Matrix n n R} (hA : A.Nonsingular) (hB : B.Nonsingular) :
    (A * B).Nonsingular := by
  rw [← isLeftRegular_iff_nonsingular] at *
  exact hA.mul hB

omit [DecidableEq n] in
theorem isLeftRegular_iff_isRightRegular : IsLeftRegular A ↔ IsRightRegular A := by
  classical rw [isLeftRegular_iff_nonsingular, isRightRegular_iff_nonsingular]

omit [DecidableEq n] [Fintype n] in
/-- https://mathoverflow.net/questions/511862/transpose-symmetry-of-injectivity-of-linear-maps-over-semirings
asks whether this is still true without `IsCancelAdd R`. -/
theorem linearIndependent_col_iff_row [Finite n] :
    LinearIndependent R A.col ↔ LinearIndependent R A.row := by
  have := Fintype.ofFinite
  classical rw [linearIndependent_col_iff, ← nonsingular_transpose_iff, ← linearIndependent_col_iff]
  rfl

end

end Matrix

open Matrix

/-- A nontrivial commutative semiring satisfies the strong rank condition. -/
instance (priority := 100) CommSemiring.strongRankCondition_of_nontrivial [Nontrivial R] :
    StrongRankCondition R where
  le_of_fin_injective {n m} f hf := by
    let g : (Fin m → R) →ₗ[R] (Fin n → R) :=
      ⟨⟨fun x i ↦ if h : i < m then x ⟨i, h⟩ else 0, by aesop⟩, by aesop⟩
    by_contra! hnm
    have hg : Function.Injective g := fun x y eq ↦ funext fun i ↦ by
      simpa [g] using congr($eq ⟨i, i.prop.trans hnm⟩)
    let A := toLin'.symm (g ∘ₗ f)
    have hA : A.Nonsingular := .of_linearIndependent_col <| mulVec_injective_iff.mp <| by
      convert hg.comp hf; ext; simp [A, g]
    have : A.row ⟨m, hnm⟩ = 0 := by ext; simp [A, g]
    exact not_subsingleton R
      ⟨by simpa [Nonsingular, DetpBalanced, detp_eq_of_row_eq_zero _ this] using hA⟩
