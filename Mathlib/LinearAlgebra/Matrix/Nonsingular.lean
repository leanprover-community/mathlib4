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
variable (A : Matrix n n R)

namespace Matrix

public lemma nonsingular_iff_det_mem_nonZeroDivisors {R : Type*} [CommRing R]
    {A : Matrix n n R} : A.Nonsingular ↔ A.det ∈ nonZeroDivisors R := by
  rw [Nonsingular, det_eq_detp_sub_detp, ← nonZeroDivisorsRight_eq_nonZeroDivisors,
    mem_nonZeroDivisorsRight_iff]
  refine ⟨fun h x eq ↦ h x 0 (by simpa [mul_sub, sub_eq_zero, DetpBalanced] using eq),
    fun h a b eq ↦ sub_eq_zero.mp <| h _ ?_⟩
  convert sub_eq_zero.mpr eq using 1
  ring

variable {A}

/-- If the columns of a square matrix are linearly independent, then the matrix is nonsingular. -/
public theorem Nonsingular.of_linearIndependent_col (ind : LinearIndependent R A.col) :
    A.Nonsingular := fun a b bal ↦ by
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

/-- If a matrix over a commutative semiring with cancellative addition is nonsingular, then its
columns are linearly independent. Generalizes `Matrix.linearIndependent_cols_of_det_ne_zero`. -/
public theorem Nonsingular.linearIndependent_col [IsCancelAdd R]
    (hA : A.Nonsingular) : LinearIndependent R A.col :=
  mulVec_injective_iff.mp fun x y eq ↦ funext fun k ↦ hA _ _ <| show _ = _ by
    have hp := congr((A.adjp 1 *ᵥ $eq) k)
    have hm := congr((A.adjp (-1) *ᵥ $eq) k)
    simp_rw [mulVec_mulVec, mulVec, dotProduct, ← Finset.sum_erase_add _ _ (Finset.mem_univ k),
      ← Finset.filter_ne, adjp_mul_apply_eq] at hp hm
    iterate 2 rw [Finset.sum_congr rfl fun i h ↦ congr_arg (· * _) <|
      adjp_mul_apply_ne _ _ _ (Finset.mem_filter.mp h).2] at hp
    grind

public theorem linearIndependent_col_iff [IsCancelAdd R] :
    LinearIndependent R A.col ↔ A.Nonsingular :=
  ⟨.of_linearIndependent_col, (·.linearIndependent_col)⟩

omit [DecidableEq n] [Fintype n] in
theorem linearIndependent_col_iff_row [Finite n] [IsCancelAdd R] :
    LinearIndependent R A.col ↔ LinearIndependent R A.row := by
  have := Fintype.ofFinite
  classical rw [linearIndependent_col_iff, ← nonsingular_transpose_iff, ← linearIndependent_col_iff]
  rfl

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
    have : A ⟨m, hnm⟩ = 0 := by ext; simp [A, g]
    exact not_subsingleton R
      ⟨by simpa [Nonsingular, DetpBalanced, detp_eq_of_row_eq_zero _ this] using hA⟩
