/-
Copyright (c) 2026 Joel Cruz Cabrera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joel Cruz Cabrera
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# The Redheffer matrix and the Mertens function

The *zeta matrix* `Matrix.zetaMatrix R n` is the `n × n` divisibility matrix over `R` with entry
`1` at `(i, j)` when `i + 1 ∣ j + 1` (indices are `0`-based, so the matrix encodes divisibility on
`{1, …, n}`) and `0` otherwise. The *Redheffer matrix* `Matrix.redheffer R n` is the zeta matrix
with its first column replaced by ones.

The *Mertens function* `ArithmeticFunction.mertens n` is the summatory function of the Möbius
function, `∑ k ∈ Icc 1 n, μ k`.

## Main results

* `Matrix.det_zetaMatrix`: the zeta matrix is upper triangular with unit diagonal, so its
  determinant is `1`.
* `Matrix.det_redheffer`: **Redheffer's theorem** (1977),
  `det (redheffer R (n + 1)) = mertens (n + 1)` over any commutative ring `R`.

## Proof sketch

By linearity of the determinant in the first column, `det (redheffer R (n + 1))` is
`det (zetaMatrix R (n + 1))` plus the determinant of the zeta matrix whose first column is
`(0, 1, …, 1)`. By Cramer's rule the latter is the dot product of the first row of the inverse
of the zeta matrix with `(0, 1, …, 1)`, and that row is `(μ 1, …, μ (n + 1))` because
`μ * ζ = 1` (`ArithmeticFunction.moebius_mul_coe_zeta`). The sum `μ 2 + ⋯ + μ (n + 1)` is
`mertens (n + 1) - 1`.

## Implementation notes

Indices are `Fin n`, so the matrix on `{1, …, n}` is written with `i + 1` and `j + 1`. The
theorem is stated for `redheffer R (n + 1)`: the empty matrix has determinant `1` while
`mertens 0 = 0`. The matrices take their entries in any `R` with a `0` and a `1` (`R` is an
explicit argument, since nothing else determines it); the determinant results need `CommRing R`,
and `mertens` stays `ℤ`-valued, cast into `R`. `mertens` is an `ArithmeticFunction ℤ` (so
`mertens 0 = 0` is `map_zero`) with `mertens_apply` as its defining lemma; `zetaMatrix_apply` and
`redheffer_apply` are the `simp` normal forms of the two matrices.

Since `M n = 0` for infinitely many `n` (Odlyzko and te Riele's disproof of the Mertens
conjecture, [odlyzko1985]), the Redheffer matrix is singular infinitely often; the Riemann
hypothesis is equivalent to `M x = O(x ^ (1/2 + ε))` for every `ε > 0`. Neither fact is
formalised here.

## References

* [R. M. Redheffer, *Eine explizit lösbare Optimierungsaufgabe*][redheffer1977]
* [A. M. Odlyzko, H. J. J. te Riele, *Disproof of the Mertens conjecture*][odlyzko1985]

## Tags

mertens function, redheffer matrix, moebius function, determinant
-/

@[expose] public section

open Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace ArithmeticFunction

/-- The Mertens function `M n = ∑ k ∈ Icc 1 n, μ k`, the summatory function of the Möbius
function, as an arithmetic function. -/
def mertens : ArithmeticFunction ℤ := ⟨fun n ↦ ∑ k ∈ Icc 1 n, (μ k : ℤ), by simp⟩

theorem mertens_apply (n : ℕ) : mertens n = ∑ k ∈ Icc 1 n, (μ k : ℤ) := rfl

@[simp] theorem mertens_one : mertens 1 = 1 := by simp [mertens_apply]

theorem mertens_add_one (n : ℕ) : mertens (n + 1) = mertens n + μ (n + 1) := by
  rw [mertens_apply, mertens_apply, sum_Icc_succ_top (by omega)]

theorem mertens_eq_sum_fin (n : ℕ) : mertens n = ∑ i : Fin n, (μ ((i : ℕ) + 1) : ℤ) := by
  rw [mertens_apply, Fin.sum_univ_eq_sum_range (fun i ↦ (μ (i + 1) : ℤ)), range_eq_Ico,
    sum_Ico_add' (fun i ↦ (μ i : ℤ)) 0 n 1, Ico_add_one_right_eq_Icc]

end ArithmeticFunction

namespace Matrix

open ArithmeticFunction

variable (R : Type*)

section ZeroOne

variable [Zero R] [One R]

/-- The `n × n` zeta (divisibility) matrix: the `(i, j)` entry is `1` if `i + 1 ∣ j + 1` and `0`
otherwise. -/
def zetaMatrix (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  of fun i j ↦ if (i : ℕ) + 1 ∣ (j : ℕ) + 1 then 1 else 0

/-- The `n × n` Redheffer matrix: the zeta matrix with its first column replaced by ones. -/
def redheffer (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  of fun i j ↦ if (j : ℕ) = 0 ∨ (i : ℕ) + 1 ∣ (j : ℕ) + 1 then 1 else 0

@[simp] theorem zetaMatrix_apply (n : ℕ) (i j : Fin n) :
    zetaMatrix R n i j = if (i : ℕ) + 1 ∣ (j : ℕ) + 1 then 1 else 0 := rfl

@[simp] theorem redheffer_apply (n : ℕ) (i j : Fin n) :
    redheffer R n i j = if (j : ℕ) = 0 ∨ (i : ℕ) + 1 ∣ (j : ℕ) + 1 then 1 else 0 := rfl

theorem zetaMatrix_isUpperTriangular (n : ℕ) : (zetaMatrix R n).IsUpperTriangular := by
  intro i j hij
  simp only [id] at hij
  have : ¬ ((i : ℕ) + 1 ∣ (j : ℕ) + 1) := fun hd ↦ by
    have := Nat.le_of_dvd (by omega) hd
    omega
  simp [zetaMatrix_apply, this]

theorem redheffer_eq_updateCol (n : ℕ) :
    redheffer R (n + 1) = (zetaMatrix R (n + 1)).updateCol 0 (fun _ ↦ 1) := by
  ext i j
  by_cases hj : j = 0
  · subst hj; simp [redheffer_apply]
  · have hj0 : (j : ℕ) ≠ 0 := fun hh ↦ hj (Fin.ext (by simpa using hh))
    simp [hj, hj0, redheffer_apply, zetaMatrix_apply]

end ZeroOne

variable [CommRing R]

@[simp] theorem det_zetaMatrix (n : ℕ) : (zetaMatrix R n).det = 1 := by
  rw [det_of_isUpperTriangular (zetaMatrix_isUpperTriangular R n)]
  simp [zetaMatrix_apply]

theorem det_redheffer_eq_one_add (n : ℕ) :
    (redheffer R (n + 1)).det =
      1 + ((zetaMatrix R (n + 1)).updateCol 0 (fun i ↦ if i = 0 then 0 else 1)).det := by
  rw [redheffer_eq_updateCol]
  have hsplit : (fun _ : Fin (n + 1) ↦ (1 : R)) =
      (fun i ↦ if i = 0 then (1 : R) else 0) + (fun i ↦ if i = 0 then (0 : R) else 1) := by
    funext i; by_cases h : i = 0 <;> simp [h]
  rw [hsplit, det_updateCol_add]
  congr 1
  have hcol : (zetaMatrix R (n + 1)).updateCol 0 (fun i ↦ if i = 0 then (1 : R) else 0) =
      zetaMatrix R (n + 1) := by
    ext i j
    rw [updateCol_apply]
    by_cases hj : j = 0
    · subst hj; simp
    · simp [hj]
  rw [hcol, det_zetaMatrix]

/-- The row vector `(μ 1, μ 2, …, μ n)`. -/
def moebiusRow (n : ℕ) : Fin n → R := fun i ↦ (μ ((i : ℕ) + 1) : R)

theorem _root_.Nat.sum_fin_dvd_eq_sum_divisors {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    {n m : ℕ} (hm : m ≠ 0) (hmn : m ≤ n) :
    (∑ x : Fin n, if (x : ℕ) + 1 ∣ m then f ((x : ℕ) + 1) else 0) = ∑ d ∈ m.divisors, f d := by
  rw [Fin.sum_univ_eq_sum_range (fun x ↦ if x + 1 ∣ m then f (x + 1) else 0), range_eq_Ico,
    sum_Ico_add' (fun x ↦ if x ∣ m then f x else 0) 0 n 1, ← sum_filter]
  congr 1
  ext d
  simp only [mem_filter, mem_Ico, Nat.mem_divisors, hm, ne_eq, not_false_eq_true, and_true]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨⟨Nat.pos_of_dvd_of_pos h (Nat.pos_of_ne_zero hm),
    by have := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) h; omega⟩, h⟩⟩

theorem vecMul_moebiusRow_zetaMatrix (n : ℕ) :
    (moebiusRow R (n + 1)) ᵥ* zetaMatrix R (n + 1) = fun k ↦ if k = 0 then (1 : R) else 0 := by
  funext k
  simp only [vecMul, dotProduct, moebiusRow, zetaMatrix_apply]
  rw [show (∑ x : Fin (n + 1), (μ ((x : ℕ) + 1) : R) *
        (if (x : ℕ) + 1 ∣ (k : ℕ) + 1 then (1 : R) else 0)) =
      ∑ x : Fin (n + 1), (if (x : ℕ) + 1 ∣ (k : ℕ) + 1 then (μ ((x : ℕ) + 1) : R) else 0)
      from sum_congr rfl fun x _ ↦ by by_cases h : (x : ℕ) + 1 ∣ (k : ℕ) + 1 <;> simp [h]]
  rw [Nat.sum_fin_dvd_eq_sum_divisors (fun d ↦ (μ d : R)) (by omega) (by omega),
    ← Int.cast_sum, sum_divisors_moebius]
  by_cases hk : k = 0
  · subst hk; simp
  · simp [hk]

theorem moebiusRow_eq_vecMul_inv (n : ℕ) :
    moebiusRow R (n + 1) =
      (fun k ↦ if k = (0 : Fin (n + 1)) then (1 : R) else 0) ᵥ* (zetaMatrix R (n + 1))⁻¹ := by
  have hunit : IsUnit (zetaMatrix R (n + 1)).det := by simp
  have step := congrArg (· ᵥ* (zetaMatrix R (n + 1))⁻¹) (vecMul_moebiusRow_zetaMatrix R n)
  simpa [vecMul_vecMul, mul_nonsing_inv _ hunit] using step

theorem det_zetaMatrix_updateCol (n : ℕ) (u : Fin (n + 1) → R) :
    ((zetaMatrix R (n + 1)).updateCol 0 u).det = ∑ j, moebiusRow R (n + 1) j * u j := by
  rw [← cramer_apply]
  have hunit : IsUnit (zetaMatrix R (n + 1)).det := by simp
  have hc := det_smul_inv_mulVec_eq_cramer (zetaMatrix R (n + 1)) u hunit
  rw [det_zetaMatrix, one_smul] at hc
  rw [← hc, moebiusRow_eq_vecMul_inv R n]
  simp [mulVec, dotProduct, vecMul]

theorem sum_moebiusRow_add_one (n : ℕ) :
    (∑ j : Fin (n + 1), if j = 0 then (0 : R) else moebiusRow R (n + 1) j) =
      mertens (n + 1) - 1 := by
  rw [Fin.sum_univ_succ, mertens_eq_sum_fin, Fin.sum_univ_succ]
  push_cast
  simp [moebiusRow]

/-- **Redheffer's theorem**: the determinant of the `(n + 1) × (n + 1)` Redheffer matrix is the
Mertens function `M (n + 1) = ∑ k ∈ Icc 1 (n + 1), μ k`. -/
theorem det_redheffer (n : ℕ) : (redheffer R (n + 1)).det = mertens (n + 1) := by
  rw [det_redheffer_eq_one_add, det_zetaMatrix_updateCol]
  have h : (∑ j, moebiusRow R (n + 1) j * (if j = 0 then (0 : R) else 1)) =
      mertens (n + 1) - 1 := by
    rw [← sum_moebiusRow_add_one]
    refine sum_congr rfl fun j _ ↦ ?_
    by_cases hj : j = 0 <;> simp [hj]
  rw [h]; ring

end Matrix
