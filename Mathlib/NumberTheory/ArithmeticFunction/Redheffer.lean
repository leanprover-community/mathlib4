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

The *zeta matrix* `Matrix.zetaMatrix n` is the `n × n` divisibility matrix with entry `1` at
`(i, j)` when `i + 1 ∣ j + 1` (indices are `0`-based, so the matrix encodes divisibility on
`{1, …, n}`) and `0` otherwise. The *Redheffer matrix* `Matrix.redheffer n` is the zeta matrix
with its first column replaced by ones.

The *Mertens function* `ArithmeticFunction.mertens n` is the summatory function of the Möbius
function, `∑ k ∈ Icc 1 n, μ k`.

## Main results

* `Matrix.det_zetaMatrix`: the zeta matrix is upper triangular with unit diagonal, so its
  determinant is `1`.
* `Matrix.det_redheffer`: **Redheffer's theorem** (1977),
  `det (redheffer (n + 1)) = mertens (n + 1)`.

## Proof sketch

By linearity of the determinant in the first column, `det (redheffer (n + 1))` is
`det (zetaMatrix (n + 1))` plus the determinant of the zeta matrix whose first column is
`(0, 1, …, 1)`. By Cramer's rule the latter is the dot product of the first row of the inverse
of the zeta matrix with `(0, 1, …, 1)`, and that row is `(μ 1, …, μ (n + 1))` because
`μ * ζ = 1` (`ArithmeticFunction.moebius_mul_coe_zeta`). The sum `μ 2 + ⋯ + μ (n + 1)` is
`mertens (n + 1) - 1`.

## References

* R. M. Redheffer, *Eine explizit lösbare Optimierungsaufgabe*, Numerische Methoden bei
  Optimierungsaufgaben, Band 3, ISNM 36, Birkhäuser (1977), 213–216.
-/

@[expose] public section

open Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace ArithmeticFunction

/-- The Mertens function `M n = ∑ k ∈ Icc 1 n, μ k`, the summatory function of the Möbius
function, as an arithmetic function. -/
def mertens : ArithmeticFunction ℤ := ⟨fun n => ∑ k ∈ Icc 1 n, (μ k : ℤ), by simp⟩

theorem mertens_apply (n : ℕ) : mertens n = ∑ k ∈ Icc 1 n, (μ k : ℤ) := rfl

@[simp] theorem mertens_one : mertens 1 = 1 := by simp [mertens_apply]

theorem mertens_add_one (n : ℕ) : mertens (n + 1) = mertens n + μ (n + 1) := by
  rw [mertens_apply, mertens_apply, sum_Icc_succ_top (by omega)]

/-- `∑ i ∈ range n, μ (i + 2) = mertens (n + 1) - 1`: the Mertens function without its first
term `μ 1 = 1`. -/
theorem sum_range_moebius_add_two (n : ℕ) :
    (∑ i ∈ range n, (μ (i + 1 + 1) : ℤ)) = mertens (n + 1) - 1 := by
  induction n with
  | zero => simp
  | succ m ih => rw [sum_range_succ, ih, mertens_add_one (m + 1)]; ring

/-- The same sum written over `range (n + 1)` with the term for `0` set to zero. -/
theorem sum_range_ite_moebius (n : ℕ) :
    (∑ k ∈ range (n + 1), if k = 0 then (0 : ℤ) else μ (k + 1)) = mertens (n + 1) - 1 := by
  rw [sum_range_succ', ← sum_range_moebius_add_two n]
  simp

end ArithmeticFunction

namespace Matrix

open ArithmeticFunction

/-- The `n × n` zeta (divisibility) matrix: the `(i, j)` entry is `1` if `i + 1 ∣ j + 1` and `0`
otherwise. -/
def zetaMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  of fun i j => if (i : ℕ) + 1 ∣ (j : ℕ) + 1 then 1 else 0

/-- The `n × n` Redheffer matrix: the zeta matrix with its first column replaced by ones. -/
def redheffer (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  of fun i j => if (j : ℕ) = 0 ∨ (i : ℕ) + 1 ∣ (j : ℕ) + 1 then 1 else 0

theorem zetaMatrix_apply (n : ℕ) (i j : Fin n) :
    zetaMatrix n i j = if (i : ℕ) + 1 ∣ (j : ℕ) + 1 then 1 else 0 := rfl

theorem redheffer_apply (n : ℕ) (i j : Fin n) :
    redheffer n i j = if (j : ℕ) = 0 ∨ (i : ℕ) + 1 ∣ (j : ℕ) + 1 then 1 else 0 := rfl

/-- The zeta matrix is upper triangular: `i + 1 ∣ j + 1` forces `i ≤ j`. -/
theorem zetaMatrix_isUpperTriangular (n : ℕ) : (zetaMatrix n).IsUpperTriangular := by
  intro i j hij
  simp only [id] at hij
  have : ¬ ((i : ℕ) + 1 ∣ (j : ℕ) + 1) := fun hd => by
    have := Nat.le_of_dvd (by omega) hd
    omega
  simp [zetaMatrix_apply, this]

/-- The zeta matrix has determinant `1`. -/
@[simp] theorem det_zetaMatrix (n : ℕ) : (zetaMatrix n).det = 1 := by
  rw [det_of_isUpperTriangular (zetaMatrix_isUpperTriangular n)]
  simp [zetaMatrix_apply]

/-- The first column of the zeta matrix is the first standard basis vector. -/
theorem zetaMatrix_apply_zero (n : ℕ) (i : Fin (n + 1)) :
    zetaMatrix (n + 1) i 0 = if i = 0 then 1 else 0 := by
  rw [zetaMatrix_apply]
  by_cases h : i = 0
  · subst h; simp
  · simp [h]

/-- The Redheffer matrix is the zeta matrix with its first column set to ones. -/
theorem redheffer_eq_updateCol (n : ℕ) :
    redheffer (n + 1) = (zetaMatrix (n + 1)).updateCol 0 (fun _ => 1) := by
  ext i j
  by_cases hj : j = 0
  · subst hj; simp [redheffer_apply]
  · have hj0 : (j : ℕ) ≠ 0 := fun hh => hj (Fin.ext (by simpa using hh))
    simp [hj, hj0, redheffer_apply, zetaMatrix_apply]

/-- Linearity of the determinant in the first column: `det (redheffer (n + 1))` is `1` plus the
determinant of the zeta matrix with first column `(0, 1, …, 1)`. -/
theorem det_redheffer_eq_one_add (n : ℕ) :
    (redheffer (n + 1)).det
      = 1 + ((zetaMatrix (n + 1)).updateCol 0 (fun i => if i = 0 then 0 else 1)).det := by
  rw [redheffer_eq_updateCol]
  have hsplit : (fun _ : Fin (n + 1) => (1 : ℤ))
      = (fun i => if i = 0 then (1 : ℤ) else 0) + (fun i => if i = 0 then (0 : ℤ) else 1) := by
    funext i; by_cases h : i = 0 <;> simp [h]
  rw [hsplit, det_updateCol_add]
  congr 1
  have hcol : (zetaMatrix (n + 1)).updateCol 0 (fun i => if i = 0 then (1 : ℤ) else 0)
      = zetaMatrix (n + 1) := by
    ext i j
    rw [updateCol_apply]
    by_cases hj : j = 0
    · subst hj; simp [zetaMatrix_apply_zero]
    · simp [hj]
  rw [hcol, det_zetaMatrix]

/-- The row vector `(μ 1, μ 2, …, μ n)`. -/
def moebiusRow (n : ℕ) : Fin n → ℤ := fun i => (μ ((i : ℕ) + 1) : ℤ)

/-- A sum over `Fin n` with a divisibility indicator equals the sum over the divisors of `m`,
provided `1 ≤ m ≤ n` so that no divisor is out of range. -/
theorem sum_fin_dvd_eq_sum_divisors (n m : ℕ) (hm1 : 1 ≤ m) (hmn : m ≤ n) :
    (∑ x : Fin n, if (x : ℕ) + 1 ∣ m then (μ ((x : ℕ) + 1) : ℤ) else 0)
      = ∑ d ∈ m.divisors, (μ d : ℤ) := by
  rw [Fin.sum_univ_eq_sum_range (fun x => if x + 1 ∣ m then (μ (x + 1) : ℤ) else 0)]
  rw [← sum_filter]
  have hset : (range n).filter (fun i => i + 1 ∣ m) = m.divisors.image (· - 1) := by
    ext i
    simp only [mem_filter, mem_range, mem_image, Nat.mem_divisors]
    constructor
    · rintro ⟨hin, hdvd⟩
      exact ⟨i + 1, ⟨hdvd, by omega⟩, by omega⟩
    · rintro ⟨d, ⟨hdvd, -⟩, hd⟩
      have hdle : d ≤ m := Nat.le_of_dvd (by omega) hdvd
      have hdpos : 1 ≤ d := Nat.pos_of_dvd_of_pos hdvd (by omega)
      refine ⟨by omega, ?_⟩
      rw [← hd, show d - 1 + 1 = d by omega]
      exact hdvd
  rw [hset, sum_image]
  · refine sum_congr rfl fun d hd => ?_
    have hdpos : 1 ≤ d := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 (by omega)
    congr 1
    omega
  · intro a ha b hb hab
    have hapos : 1 ≤ a := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp ha).1 (by omega)
    have hbpos : 1 ≤ b := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hb).1 (by omega)
    simp only at hab
    omega

/-- `μ * ζ = 1` as a row-vector identity: `(μ 1, …, μ (n + 1)) ᵥ* zetaMatrix (n + 1)` is the
first standard basis vector. -/
theorem vecMul_moebiusRow_zetaMatrix (n : ℕ) :
    (moebiusRow (n + 1)) ᵥ* zetaMatrix (n + 1) = fun k => if k = 0 then (1 : ℤ) else 0 := by
  funext k
  simp only [vecMul, dotProduct, moebiusRow, zetaMatrix_apply]
  rw [show (∑ x : Fin (n + 1), (μ ((x : ℕ) + 1) : ℤ)
        * (if (x : ℕ) + 1 ∣ (k : ℕ) + 1 then (1 : ℤ) else 0))
      = ∑ x : Fin (n + 1), (if (x : ℕ) + 1 ∣ (k : ℕ) + 1 then (μ ((x : ℕ) + 1) : ℤ) else 0)
      from sum_congr rfl fun x _ => by by_cases h : (x : ℕ) + 1 ∣ (k : ℕ) + 1 <;> simp [h]]
  rw [sum_fin_dvd_eq_sum_divisors (n + 1) ((k : ℕ) + 1) (by omega) (by omega),
    sum_divisors_moebius]
  by_cases hk : k = 0
  · subst hk; simp
  · simp [hk]

/-- The first row of the inverse of the zeta matrix is `(μ 1, …, μ (n + 1))`. -/
theorem moebiusRow_eq_vecMul_inv (n : ℕ) :
    moebiusRow (n + 1)
      = (fun k => if k = (0 : Fin (n + 1)) then (1 : ℤ) else 0) ᵥ* (zetaMatrix (n + 1))⁻¹ := by
  have hunit : IsUnit (zetaMatrix (n + 1)).det := by simp
  have step := congrArg (· ᵥ* (zetaMatrix (n + 1))⁻¹) (vecMul_moebiusRow_zetaMatrix n)
  simpa [vecMul_vecMul, mul_nonsing_inv _ hunit] using step

/-- Cramer's rule for the zeta matrix: replacing its first column by `u` gives determinant
`∑ j, μ (j + 1) * u j`. -/
theorem det_zetaMatrix_updateCol (n : ℕ) (u : Fin (n + 1) → ℤ) :
    ((zetaMatrix (n + 1)).updateCol 0 u).det = ∑ j, moebiusRow (n + 1) j * u j := by
  rw [← cramer_apply]
  have hunit : IsUnit (zetaMatrix (n + 1)).det := by simp
  have hc := det_smul_inv_mulVec_eq_cramer (zetaMatrix (n + 1)) u hunit
  rw [det_zetaMatrix, one_smul] at hc
  rw [← hc, moebiusRow_eq_vecMul_inv n]
  simp [mulVec, dotProduct, vecMul]

/-- `μ 2 + ⋯ + μ (n + 1) = mertens (n + 1) - 1`, written as a sum over `Fin (n + 1)` that skips
the index `0`. -/
theorem sum_moebiusRow_succ (n : ℕ) :
    (∑ j : Fin (n + 1), if j = 0 then (0 : ℤ) else moebiusRow (n + 1) j)
      = mertens (n + 1) - 1 := by
  have hval : ∀ j : Fin (n + 1), (if j = 0 then (0 : ℤ) else moebiusRow (n + 1) j)
      = (fun k : ℕ => if k = 0 then (0 : ℤ) else μ (k + 1)) (j : ℕ) := by
    intro j
    by_cases hj : j = 0
    · subst hj; simp
    · have hj0 : (j : ℕ) ≠ 0 := fun hh => hj (Fin.ext (by simpa using hh))
      simp [moebiusRow, hj, hj0]
  simp_rw [hval]
  rw [Fin.sum_univ_eq_sum_range (fun k => if k = 0 then (0 : ℤ) else μ (k + 1)) (n + 1)]
  exact sum_range_ite_moebius n

/-- **Redheffer's theorem**: the determinant of the `(n + 1) × (n + 1)` Redheffer matrix is the
Mertens function `M (n + 1) = ∑ k ∈ Icc 1 (n + 1), μ k`. -/
theorem det_redheffer (n : ℕ) : (redheffer (n + 1)).det = mertens (n + 1) := by
  rw [det_redheffer_eq_one_add, det_zetaMatrix_updateCol]
  have h : (∑ j, moebiusRow (n + 1) j * (if j = 0 then (0 : ℤ) else 1))
      = mertens (n + 1) - 1 := by
    rw [← sum_moebiusRow_succ]
    refine sum_congr rfl fun j _ => ?_
    by_cases hj : j = 0 <;> simp [hj]
  rw [h]; ring

end Matrix
