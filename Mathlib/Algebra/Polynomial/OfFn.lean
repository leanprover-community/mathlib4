/-
Copyright (c) 2025 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Data.List.ToFinsupp
import Mathlib.LinearAlgebra.Pi
/-!
# `Polynomial.ofFn` and `Polynomial.toFn`

In this file we introduce `ofFn` and `toFn`, two functions that associate a polynomial to the vector
of its coefficients and vice versa. We prove some basic APIs for these functions.

## Main definitions

- `Polynomial.toFn n` associates to a polynomial the vector of its first `n` coefficients.
- `Polynomial.ofFn n` associates to a vector of length `n` the polynomial that has the entries of
  the vector as coefficients.
-/

namespace Polynomial

section toFn

variable {R : Type*} [Semiring R]

/-- `toFn n f` is the vector of the first `n` coefficients of the polynomial `f`. -/
def toFn (n : ℕ) : R[X] →ₗ[R] Fin n → R := LinearMap.pi (fun i ↦ lcoeff R i)

theorem toFn_zero (n : ℕ) : toFn n (0 : R[X]) = 0 := by simp

end toFn
section ofFn

variable {R : Type*} [Semiring R] [DecidableEq R]

/-- `ofFn n v` is the polynomial whose coefficients are the entries of the vector `v`. -/
def ofFn (n : ℕ) : (Fin n → R) →ₗ[R] R[X] where
  toFun v := ⟨(List.ofFn v).toFinsupp⟩
  map_add' x y := by
    ext i
    by_cases h : i < n
    · simp [h]
    · simp [h]
  map_smul' x p := by
    ext i
    by_cases h : i < n
    · simp [h]
    · simp [h]

theorem ofFn_zero (n : ℕ) : ofFn n (0 : Fin n → R) = 0 := by simp

@[simp]
theorem ofFn_zero' (v : Fin 0 → R) : ofFn 0 v = 0 := rfl

lemma ne_zero_of_ofFn_ne_zero {n : ℕ} {v : Fin n → R} (h : ofFn n v ≠ 0) : n ≠ 0 := by
  contrapose! h
  subst h
  simp

/-- If `i < n` the `i`-th coefficient of `ofFn n v` is `v i`. -/
@[simp]
theorem ofFn_coeff_eq_val_of_lt {n i : ℕ} (v : Fin n → R) (hi : i < n) :
    (ofFn n v).coeff i = v ⟨i, hi⟩ := by
  simp [ofFn, hi]

/-- If `n ≤ i` the `i`-th coefficient of `ofFn n v` is `0`. -/
@[simp]
theorem ofFn_coeff_eq_zero_of_ge {n i : ℕ} (v : Fin n → R) (hi : n ≤ i) : (ofFn n v).coeff i = 0 :=
  by simp [ofFn, Nat.not_lt_of_ge hi]

/-- `ofFn n v` has `natDegree` smaller than `n`. -/
theorem ofFn_natDegree_lt {n : ℕ} (h : 1 ≤ n) (v : Fin n → R) : (ofFn n v).natDegree < n := by
  rw [Nat.lt_iff_le_pred h, natDegree_le_iff_coeff_eq_zero]
  exact fun _ h ↦ ofFn_coeff_eq_zero_of_ge _ <| Nat.le_of_pred_lt h

/-- `ofFn n v` has `degree` smaller than `n`. -/
theorem ofFn_degree_lt {n : ℕ} (v : Fin n → R) : (ofFn n v).degree < n := by
  by_cases h : ofFn n v = 0
  · simp only [h, degree_zero]
    exact Batteries.compareOfLessAndEq_eq_lt.mp rfl
  · exact (natDegree_lt_iff_degree_lt h).mp
      <| ofFn_natDegree_lt (Nat.one_le_iff_ne_zero.mpr <| ne_zero_of_ofFn_ne_zero h) _

theorem ofFn_eq_sum_monomial {n : ℕ} (v : Fin n → R) : ofFn n v =
    ∑ i : Fin n, monomial i (v i) := by
  by_cases h : n = 0
  · subst h
    simp [ofFn]
  · rw [as_sum_range' (ofFn n v) n <| ofFn_natDegree_lt (Nat.one_le_iff_ne_zero.mpr h) v]
    simp [Finset.sum_range]

theorem toFn_comp_ofFn_eq_id (n : ℕ) (v : Fin n → R) : toFn n (ofFn n v) = v := by
  simp [toFn, ofFn, LinearMap.pi]

theorem injective_ofFn (n : ℕ) : Function.Injective (ofFn (R := R) n) :=
  Function.LeftInverse.injective <| toFn_comp_ofFn_eq_id n

omit [DecidableEq R] in
theorem surjective_toFn (n : ℕ) : Function.Surjective (toFn (R := R) n) :=
  open Classical in
  Function.RightInverse.surjective <| toFn_comp_ofFn_eq_id n

theorem ofFn_comp_toFn_eq_id_of_natDegree_lt {n : ℕ} {p : R[X]} (h_deg : p.natDegree < n) :
    ofFn n (toFn n p) = p := by
  ext i
  by_cases h : i < n
  · simp [h, toFn]
  · have : p.coeff i = 0 := coeff_eq_zero_of_natDegree_lt <| by cutsat
    simp_all

end ofFn

end Polynomial
