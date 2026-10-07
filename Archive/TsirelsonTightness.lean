/-
Copyright (c) 2026 Stephanie Alexander. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephanie Alexander
-/
module

public import Mathlib.Algebra.Star.CHSH
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.RingTheory.MatrixAlgebra
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Tightness of Tsirelson's inequality

`tsirelson_inequality` (in `Mathlib/Algebra/Star/CHSH.lean`) shows that for any CHSH tuple
`A₀ A₁ B₀ B₁` in an ordered `ℝ`-algebra,
`A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ √2 ^ 3 • 1`.
This file shows that the constant `√2 ^ 3 = 2 * √2` is optimal. We construct an explicit
CHSH tuple in the \*-algebra of 4-by-4 real matrices whose CHSH operator has `√2 ^ 3` as an
eigenvalue, so that no smaller constant can bound it in the Loewner order.

The construction is the usual two-qubit one. Starting from the real Pauli matrices
`X = !![0, 1; 1, 0]` and `Z = !![1, 0; 0, -1]` in `M₂(ℝ)`, we form the pure tensors

* `A₀ = X ⊗ₜ 1`, `A₁ = Z ⊗ₜ 1`,
* `B₀ = (√2)⁻¹ • (1 ⊗ₜ (X + Z))`, `B₁ = (√2)⁻¹ • (1 ⊗ₜ (X - Z))`

in `M₂(ℝ) ⊗[ℝ] M₂(ℝ)` and transport them to `M₄(ℝ)` along the ⋆-algebra equivalence
`TsirelsonInequality.tensorEquiv`, which is the Kronecker product
`Matrix.kroneckerStarAlgEquiv` followed by the reindexing `Matrix.reindexStarAlgEquiv` along
`finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4`. This orders the computational basis as
`|00⟩, |01⟩, |10⟩, |11⟩`. The CHSH axioms are then consequences of the tensor product structure:
the squares are computed with `Algebra.TensorProduct.tmul_pow`, self-adjointness with
`TensorProduct.star_tmul`, and the commutation of the `A`'s with the `B`'s with
`Algebra.TensorProduct.tmul_mul_tmul`, since the two parties act on different tensor factors.

The CHSH operator of this tuple acts on the (unnormalized) Bell vector `![1, 0, 0, 1]` as
multiplication by `√2 ^ 3`; this is checked on the explicit 4-by-4 matrices given by the
`_eq` lemmas.

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

@[expose] public noncomputable section

open Matrix TensorProduct Algebra.TensorProduct
open scoped MatrixOrder

namespace TsirelsonInequality

/-! ### The real Pauli matrices -/

/-- The real Pauli matrix `X`. -/
def X : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

/-- The real Pauli matrix `Z`. -/
def Z : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

lemma X_sq : X ^ 2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [X, sq]

lemma Z_sq : Z ^ 2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Z, sq]

lemma X_add_Z_sq : (X + Z) ^ 2 = (2 : ℝ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [X, Z, sq, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

lemma X_sub_Z_sq : (X - Z) ^ 2 = (2 : ℝ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [X, Z, sq, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

lemma star_X : star X = X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [X]

lemma star_Z : star Z = Z := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Z]

/-! ### The two-qubit observables -/

/-- The identification of `M₂(ℝ) ⊗[ℝ] M₂(ℝ)` with `M₄(ℝ)` as ⋆-algebras: the Kronecker product
followed by the reindexing along `finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4`, `(i, j) ↦ 2 * i + j`,
so that the computational basis is ordered `|00⟩, |01⟩, |10⟩, |11⟩`. -/
def tensorEquiv :
    Matrix (Fin 2) (Fin 2) ℝ ⊗[ℝ] Matrix (Fin 2) (Fin 2) ℝ ≃⋆ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℝ :=
  (kroneckerStarAlgEquiv (Fin 2) (Fin 2) ℝ).trans (reindexStarAlgEquiv ℝ ℝ finProdFinEquiv)

/-- The first observable of the first party: `X ⊗ 1`. -/
def A₀ : Matrix (Fin 4) (Fin 4) ℝ := tensorEquiv (X ⊗ₜ 1)

/-- The second observable of the first party: `Z ⊗ 1`. -/
def A₁ : Matrix (Fin 4) (Fin 4) ℝ := tensorEquiv (Z ⊗ₜ 1)

/-- The first observable of the second party: `(√2)⁻¹ • (1 ⊗ (X + Z))`. -/
def B₀ : Matrix (Fin 4) (Fin 4) ℝ := (√2)⁻¹ • tensorEquiv (1 ⊗ₜ (X + Z))

/-- The second observable of the second party: `(√2)⁻¹ • (1 ⊗ (X - Z))`. -/
def B₁ : Matrix (Fin 4) (Fin 4) ℝ := (√2)⁻¹ • tensorEquiv (1 ⊗ₜ (X - Z))

lemma A₀_eq : A₀ = !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [finProdFinEquiv, Fin.divNat, Fin.modNat, X, A₀, tensorEquiv]

lemma A₁_eq : A₁ = !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [finProdFinEquiv, Fin.divNat, Fin.modNat, Z, A₁, tensorEquiv]

lemma B₀_eq : B₀ = (√2)⁻¹ • !![1, 1, 0, 0; 1, -1, 0, 0; 0, 0, 1, 1; 0, 0, 1, -1] := by
  rw [B₀]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [finProdFinEquiv, Fin.divNat, Fin.modNat, X, Z, tensorEquiv]

lemma B₁_eq : B₁ = (√2)⁻¹ • !![-1, 1, 0, 0; 1, 1, 0, 0; 0, 0, -1, 1; 0, 0, 1, 1] := by
  rw [B₁]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [finProdFinEquiv, Fin.divNat, Fin.modNat, X, Z, tensorEquiv]

/-- Operators acting on different tensor factors commute. -/
lemma commute_tensorEquiv (a b : Matrix (Fin 2) (Fin 2) ℝ) :
    Commute (tensorEquiv (a ⊗ₜ 1)) (tensorEquiv (1 ⊗ₜ b)) := by
  rw [Commute, SemiconjBy, ← map_mul, ← map_mul, tmul_mul_tmul, tmul_mul_tmul, one_mul, mul_one,
    one_mul, mul_one]

/-- The real-Pauli quadruple `(X ⊗ 1, Z ⊗ 1, (√2)⁻¹ • (1 ⊗ (X + Z)), (√2)⁻¹ • (1 ⊗ (X - Z)))`
is a CHSH tuple. -/
theorem isCHSHTuple : IsCHSHTuple A₀ A₁ B₀ B₁ where
  A₀_inv := by rw [A₀, ← map_pow, tmul_pow, one_pow, X_sq, ← one_def, map_one]
  A₁_inv := by rw [A₁, ← map_pow, tmul_pow, one_pow, Z_sq, ← one_def, map_one]
  B₀_inv := by
    rw [B₀, smul_pow, ← map_pow, tmul_pow, one_pow, X_add_Z_sq, tmul_smul, map_smul, ← one_def,
      map_one, smul_smul, inv_pow, Real.sq_sqrt zero_le_two, inv_mul_cancel₀ two_ne_zero, one_smul]
  B₁_inv := by
    rw [B₁, smul_pow, ← map_pow, tmul_pow, one_pow, X_sub_Z_sq, tmul_smul, map_smul, ← one_def,
      map_one, smul_smul, inv_pow, Real.sq_sqrt zero_le_two, inv_mul_cancel₀ two_ne_zero, one_smul]
  A₀_sa := by rw [A₀, ← map_star, star_tmul, star_X, star_one]
  A₁_sa := by rw [A₁, ← map_star, star_tmul, star_Z, star_one]
  B₀_sa := by
    rw [B₀, star_smul, star_trivial, ← map_star, star_tmul, star_one, star_add, star_X, star_Z]
  B₁_sa := by
    rw [B₁, star_smul, star_trivial, ← map_star, star_tmul, star_one, star_sub, star_X, star_Z]
  A₀B₀_commutes := by rw [A₀, B₀]; exact ((commute_tensorEquiv X (X + Z)).smul_right _).eq
  A₀B₁_commutes := by rw [A₀, B₁]; exact ((commute_tensorEquiv X (X - Z)).smul_right _).eq
  A₁B₀_commutes := by rw [A₁, B₀]; exact ((commute_tensorEquiv Z (X + Z)).smul_right _).eq
  A₁B₁_commutes := by rw [A₁, B₁]; exact ((commute_tensorEquiv Z (X - Z)).smul_right _).eq

/-! ### Tightness -/

/-- The CHSH operator of the real-Pauli tuple, with a factor of `(√2)⁻¹` pulled out, is the integer
matrix `!![2, 0, 0, 2; 0, -2, 2, 0; 0, 2, -2, 0; 2, 0, 0, 2]`. -/
theorem chsh_eq :
    A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ =
      (√2)⁻¹ • !![2, 0, 0, 2; 0, -2, 2, 0; 0, 2, -2, 0; 2, 0, 0, 2] := by
  rw [A₀_eq, A₁_eq, B₀_eq, B₁_eq, mul_smul_comm, mul_smul_comm, mul_smul_comm, mul_smul_comm,
    ← smul_add, ← smul_add, ← smul_sub]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> norm_num

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
