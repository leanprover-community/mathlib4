/-
Copyright (c) 2026 Stephanie Alexander. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephanie Alexander
-/
module

public import Mathlib.Algebra.Star.CHSH
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Tightness of Tsirelson's inequality

`tsirelson_inequality` (in `Mathlib/Algebra/Star/CHSH.lean`) shows that for any CHSH tuple
`A₀ A₁ B₀ B₁` in an ordered `ℝ`-algebra,
`A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ √2 ^ 3 • 1`.
This file shows that the constant `√2 ^ 3 = 2 * √2` is optimal, completing the "Future work"
item in that file: we construct an explicit CHSH tuple in the \*-algebra of 4-by-4 real
matrices whose CHSH operator has `√2 ^ 3` as an eigenvalue, so that no smaller constant can
bound it in the Loewner order.

Concretely, viewing `Matrix (Fin 4) (Fin 4) ℝ` as `M₂(ℝ) ⊗ M₂(ℝ)` with the computational
basis `|00⟩, |01⟩, |10⟩, |11⟩`, we take the real Pauli matrices `X = !![0, 1; 1, 0]` and
`Z = !![1, 0; 0, -1]` and set

* `A₀ = X ⊗ 1`, `A₁ = Z ⊗ 1`,
* `B₀ = (√2)⁻¹ • (1 ⊗ (X + Z))`, `B₁ = (√2)⁻¹ • (1 ⊗ (X - Z))`.

The CHSH operator of this tuple acts on the (unnormalized) Bell vector `![1, 0, 0, 1]` as
multiplication by `√2 ^ 3`.

## Main results

* `TsirelsonInequality.isCHSHTuple`: the tuple above is a CHSH tuple;
* `TsirelsonInequality.chsh_mulVec`: its CHSH operator has `√2 ^ 3` as an eigenvalue;
* `TsirelsonInequality.isLeast_chsh_le_smul_one`: `√2 ^ 3` is the least `c : ℝ` such that
  the CHSH operator of this tuple is bounded by `c • 1` in the Loewner order;
* `TsirelsonInequality.sqrt_two_pow_three_le_of_forall_chsh_le`: any constant that bounds the
  CHSH operator of every CHSH tuple in every ordered real \*-algebra is at least `√2 ^ 3`.

## References

* [Tsirelson, *Quantum generalizations of Bell's inequality*][MR577178]
-/

@[expose] public section

open Matrix
open scoped MatrixOrder

namespace TsirelsonInequality

/-- The first observable of the first party: `X ⊗ 1` for the real Pauli `X`. -/
def A₀ : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]

/-- The second observable of the first party: `Z ⊗ 1` for the real Pauli `Z`. -/
def A₁ : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1]

/-- The first observable of the second party, scaled by `√2`: `1 ⊗ (X + Z)`. -/
def B₀' : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 1, 0, 0; 1, -1, 0, 0; 0, 0, 1, 1; 0, 0, 1, -1]

/-- The second observable of the second party, scaled by `√2`: `1 ⊗ (X - Z)`. -/
def B₁' : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-1, 1, 0, 0; 1, 1, 0, 0; 0, 0, -1, 1; 0, 0, 1, 1]

/-- The first observable of the second party: `(√2)⁻¹ • (1 ⊗ (X + Z))`. -/
noncomputable def B₀ : Matrix (Fin 4) (Fin 4) ℝ := (√2)⁻¹ • B₀'

/-- The second observable of the second party: `(√2)⁻¹ • (1 ⊗ (X - Z))`. -/
noncomputable def B₁ : Matrix (Fin 4) (Fin 4) ℝ := (√2)⁻¹ • B₁'

theorem A₀_mul_self : A₀ * A₀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A₀, Matrix.mul_apply, Fin.sum_univ_four]

theorem A₁_mul_self : A₁ * A₁ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A₁, Matrix.mul_apply, Fin.sum_univ_four]

theorem B₀'_mul_self : B₀' * B₀' = (2 : ℝ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [B₀', Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem B₁'_mul_self : B₁' * B₁' = (2 : ℝ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [B₁', Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem A₀_sa : star A₀ = A₀ := by
  rw [star_eq_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [A₀]

theorem A₁_sa : star A₁ = A₁ := by
  rw [star_eq_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [A₁]

theorem B₀'_sa : star B₀' = B₀' := by
  rw [star_eq_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [B₀']

theorem B₁'_sa : star B₁' = B₁' := by
  rw [star_eq_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [B₁']

theorem A₀_comm_B₀' : A₀ * B₀' = B₀' * A₀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A₀, B₀', Matrix.mul_apply, Fin.sum_univ_four]

theorem A₀_comm_B₁' : A₀ * B₁' = B₁' * A₀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A₀, B₁', Matrix.mul_apply, Fin.sum_univ_four]

theorem A₁_comm_B₀' : A₁ * B₀' = B₀' * A₁ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A₁, B₀', Matrix.mul_apply, Fin.sum_univ_four]

theorem A₁_comm_B₁' : A₁ * B₁' = B₁' * A₁ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A₁, B₁', Matrix.mul_apply, Fin.sum_univ_four]

/-- The real-Pauli quadruple `(X ⊗ 1, Z ⊗ 1, (√2)⁻¹ • (1 ⊗ (X + Z)), (√2)⁻¹ • (1 ⊗ (X - Z)))`
is a CHSH tuple. -/
theorem isCHSHTuple : IsCHSHTuple A₀ A₁ B₀ B₁ where
  A₀_inv := by rw [sq]; exact A₀_mul_self
  A₁_inv := by rw [sq]; exact A₁_mul_self
  B₀_inv := by
    rw [sq, B₀, smul_mul_smul_comm, B₀'_mul_self, smul_smul, sqrt_two_inv_mul_self]
    norm_num
  B₁_inv := by
    rw [sq, B₁, smul_mul_smul_comm, B₁'_mul_self, smul_smul, sqrt_two_inv_mul_self]
    norm_num
  A₀_sa := A₀_sa
  A₁_sa := A₁_sa
  B₀_sa := by rw [B₀, star_smul, B₀'_sa, star_trivial]
  B₁_sa := by rw [B₁, star_smul, B₁'_sa, star_trivial]
  A₀B₀_commutes := by rw [B₀, mul_smul_comm, smul_mul_assoc, A₀_comm_B₀']
  A₀B₁_commutes := by rw [B₁, mul_smul_comm, smul_mul_assoc, A₀_comm_B₁']
  A₁B₀_commutes := by rw [B₀, mul_smul_comm, smul_mul_assoc, A₁_comm_B₀']
  A₁B₁_commutes := by rw [B₁, mul_smul_comm, smul_mul_assoc, A₁_comm_B₁']

/-- The CHSH operator of the real-Pauli tuple, with a factor of `(√2)⁻¹` pulled out, is the integer
matrix `!![2, 0, 0, 2; 0, -2, 2, 0; 0, 2, -2, 0; 2, 0, 0, 2]`. -/
theorem chsh_eq :
    A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ =
      (√2)⁻¹ • !![2, 0, 0, 2; 0, -2, 2, 0; 0, 2, -2, 0; 2, 0, 0, 2] := by
  rw [B₀, B₁, mul_smul_comm, mul_smul_comm, mul_smul_comm, mul_smul_comm,
    ← smul_add, ← smul_add, ← smul_sub]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A₀, A₁, B₀', B₁'] <;> norm_num

/-- The CHSH operator of the real-Pauli tuple has `√2 ^ 3` as an eigenvalue, witnessed by the
(unnormalized) Bell vector `![1, 0, 0, 1]`.  Combined with `tsirelson_inequality` this shows
that Tsirelson's bound is tight. -/
theorem chsh_mulVec :
    (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁) *ᵥ ![1, 0, 0, 1] =
      √2 ^ 3 • ![1, 0, 0, 1] := by
  have h4 : (!![2, 0, 0, 2; 0, -2, 2, 0; 0, 2, -2, 0; 2, 0, 0, 2] :
      Matrix (Fin 4) (Fin 4) ℝ) *ᵥ ![1, 0, 0, 1] = (4 : ℝ) • ![1, 0, 0, 1] := by
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;> norm_num
  rw [chsh_eq, Matrix.smul_mulVec, h4, smul_smul]
  congr 1
  have h2 : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h0 : (√2 : ℝ) ≠ 0 := by positivity
  field_simp
  rw [show (√2 : ℝ) ^ 4 = ((√2 : ℝ) ^ 2) ^ 2 by ring, h2]
  norm_num

/-- Tsirelson's inequality for the real-Pauli tuple, in the Loewner order on real 4-by-4
matrices: the CHSH operator is at most `√2 ^ 3 • 1`. -/
theorem chsh_le_smul_one :
    A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤
      √2 ^ 3 • (1 : Matrix (Fin 4) (Fin 4) ℝ) :=
  tsirelson_inequality A₀ A₁ B₀ B₁ isCHSHTuple

/-- Tsirelson's inequality is tight for the real-Pauli tuple: any `c : ℝ` such that the CHSH
operator is at most `c • 1` in the Loewner order satisfies `√2 ^ 3 ≤ c`. -/
theorem sqrt_two_pow_three_le_of_chsh_le {c : ℝ}
    (h : A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ c • (1 : Matrix (Fin 4) (Fin 4) ℝ)) :
    √2 ^ 3 ≤ c := by
  have key := (Matrix.le_iff.mp h).dotProduct_mulVec_nonneg ![1, 0, 0, 1]
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, chsh_mulVec] at key
  simp only [dotProduct, Fin.sum_univ_four, Pi.star_apply, star_trivial, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three] at key
  linarith

/-- **Tsirelson's inequality is tight**: `√2 ^ 3` is the least `c : ℝ` bounding the CHSH
operator of the real-Pauli tuple by `c • 1` in the Loewner order. -/
theorem isLeast_chsh_le_smul_one :
    IsLeast {c : ℝ |
        A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ c • (1 : Matrix (Fin 4) (Fin 4) ℝ)}
      (√2 ^ 3) :=
  ⟨chsh_le_smul_one, fun _ hc => sqrt_two_pow_three_le_of_chsh_le hc⟩

/-- **Optimality of Tsirelson's bound**: any constant `c : ℝ` that bounds the CHSH operator of
every CHSH tuple in every ordered real \*-algebra satisfies `√2 ^ 3 ≤ c`; that is, the constant
in `tsirelson_inequality` cannot be improved. -/
theorem sqrt_two_pow_three_le_of_forall_chsh_le {c : ℝ}
    (h : ∀ (R : Type) [Ring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]
      [Algebra ℝ R] [IsOrderedModule ℝ R] [StarModule ℝ R] (A₀ A₁ B₀ B₁ : R),
      IsCHSHTuple A₀ A₁ B₀ B₁ → A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ c • 1) :
    √2 ^ 3 ≤ c :=
  sqrt_two_pow_three_le_of_chsh_le (h _ A₀ A₁ B₀ B₁ isCHSHTuple)

end TsirelsonInequality
