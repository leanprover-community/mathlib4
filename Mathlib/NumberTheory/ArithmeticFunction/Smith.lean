/-
Copyright (c) 2026 Joel Cruz Cabrera. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joel Cruz Cabrera
-/
module

public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.ArithmeticFunction.ZetaMatrixInv

/-!
# Smith's determinant

The *GCD matrix* of `f : ℕ → R` is the `n × n` matrix `Matrix.gcdMatrix n f` with entry
`f (gcd (i + 1) (j + 1))`. **Smith's determinant** (1875): if `f m = ∑ d ∣ m, g d` for every
`m ≥ 1` (i.e. `f = g * ζ` as arithmetic functions), then

  `det (gcdMatrix n f) = g 1 * g 2 * ⋯ * g n`.

The classical case is `f = id` and `g = φ` (Euler's totient, by `Nat.sum_totient`):
`det [gcd (i, j)] = φ 1 * ⋯ * φ n`.

## Main results

* `Matrix.gcdMatrix_eq_transpose_mul_mul`: the factorisation `gcdMatrix n f = Zᵀ * (D * Z)` with
  `Z` the zeta matrix and `D = diagonal (g ∘ (· + 1))`.
* `Matrix.det_gcdMatrix`: Smith's determinant, `det (gcdMatrix n f) = ∏ i, g (i + 1)`.
* `Matrix.det_gcdMatrix_id`: the classical statement with Euler's totient.
* `Matrix.det_gcdMatrix_sigma`, `Matrix.det_gcdMatrix_card_divisors`: the instances
  `f = σ k` (`det = ∏ (i + 1) ^ k`, so `n!` for `k = 1`) and `f = τ` (`det = 1`).

## Implementation notes

The entry-wise identity behind the factorisation is
`∑ k, [k + 1 ∣ i + 1] [k + 1 ∣ j + 1] g (k + 1) = ∑ d ∣ gcd (i + 1) (j + 1), g d`, obtained from
`Nat.sum_fin_dvd_dvd_eq_sum_divisors` with `a = 1` and `Nat.dvd_gcd_iff`.

## References

* [H. J. S. Smith, *On the value of a certain arithmetical determinant*][smith1875]

## Tags

smith determinant, gcd matrix, zeta matrix, totient, divisor function
-/

@[expose] public section

open Finset
open scoped ArithmeticFunction.sigma

namespace Matrix

variable {R : Type*}

/-- The GCD matrix of `f`: the `n × n` matrix with entry `f (gcd (i + 1) (j + 1))`. -/
def gcdMatrix (n : ℕ) (f : ℕ → R) : Matrix (Fin n) (Fin n) R :=
  of fun i j ↦ f (Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1))

@[simp] theorem gcdMatrix_apply (n : ℕ) (f : ℕ → R) (i j : Fin n) :
    gcdMatrix n f i j = f (Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1)) := rfl

theorem _root_.Nat.sum_fin_dvd_dvd_eq_sum_divisors_gcd {M : Type*} [AddCommMonoid M] (n : ℕ)
    (g : ℕ → M) (i j : Fin n) :
    (∑ k : Fin n, if (k : ℕ) + 1 ∣ (i : ℕ) + 1 ∧ (k : ℕ) + 1 ∣ (j : ℕ) + 1 then g ((k : ℕ) + 1)
      else 0) = ∑ d ∈ (Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1)).divisors, g d := by
  simpa [Nat.dvd_gcd_iff] using
    Nat.sum_fin_dvd_dvd_eq_sum_divisors n 1 (Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1)) g le_rfl
      (Nat.gcd_pos_of_pos_left _ (by omega)) (one_dvd _)
      ((Nat.gcd_le_left ((j : ℕ) + 1) (by omega)).trans (by omega))

variable [CommRing R]

/-- The factorisation behind Smith's determinant: `gcdMatrix n f = Zᵀ * (D * Z)` with `Z` the zeta
matrix and `D` the diagonal matrix of `g`, whenever `f m = ∑ d ∣ m, g d` for `m ≥ 1`. -/
theorem gcdMatrix_eq_transpose_mul_mul (n : ℕ) (f g : ℕ → R)
    (hfg : ∀ m, 0 < m → f m = ∑ d ∈ m.divisors, g d) :
    gcdMatrix n f =
      (zetaMatrix R n)ᵀ * (diagonal (fun i : Fin n ↦ g ((i : ℕ) + 1)) * zetaMatrix R n) := by
  ext i j
  rw [gcdMatrix_apply, hfg _ (Nat.gcd_pos_of_pos_left _ (by omega)),
    ← Nat.sum_fin_dvd_dvd_eq_sum_divisors_gcd n g i j, mul_apply]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [transpose_apply, zetaMatrix_apply, mul_apply]
  simp only [diagonal_apply, zetaMatrix_apply]
  rw [sum_eq_single k (fun b _ hb ↦ by simp [Ne.symm hb]) (by simp)]
  by_cases h1 : (k : ℕ) + 1 ∣ (i : ℕ) + 1 <;> by_cases h2 : (k : ℕ) + 1 ∣ (j : ℕ) + 1 <;>
    simp [h1, h2]

/-- **Smith's determinant** (1875): if `f m = ∑ d ∣ m, g d` for every `m ≥ 1`, then the
determinant of the GCD matrix of `f` is `g 1 * g 2 * ⋯ * g n`. -/
theorem det_gcdMatrix (n : ℕ) (f g : ℕ → R) (hfg : ∀ m, 0 < m → f m = ∑ d ∈ m.divisors, g d) :
    (gcdMatrix n f).det = ∏ i : Fin n, g ((i : ℕ) + 1) := by
  rw [gcdMatrix_eq_transpose_mul_mul n f g hfg, det_mul, det_transpose, det_mul, det_zetaMatrix,
    det_diagonal, one_mul, mul_one]

/-- The classical case of Smith's determinant: `det [gcd (i, j)] = φ 1 * φ 2 * ⋯ * φ n`. -/
theorem det_gcdMatrix_id (n : ℕ) :
    (gcdMatrix n (fun m ↦ (m : R))).det = ∏ i : Fin n, (Nat.totient ((i : ℕ) + 1) : R) :=
  det_gcdMatrix n (fun m ↦ (m : R)) (fun m ↦ (Nat.totient m : R)) fun m _ ↦ by
    rw [← Nat.cast_sum, Nat.sum_totient]

theorem det_gcdMatrix_sigma (n k : ℕ) :
    (gcdMatrix n (fun m ↦ (σ k m : R))).det = ∏ i : Fin n, (((i : ℕ) + 1 : ℕ) : R) ^ k :=
  det_gcdMatrix n (fun m ↦ (σ k m : R)) (fun m ↦ (m : R) ^ k) fun m _ ↦ by
    simp [ArithmeticFunction.sigma_apply]

theorem det_gcdMatrix_card_divisors (n : ℕ) :
    (gcdMatrix n (fun m ↦ (m.divisors.card : R))).det = 1 := by
  simpa using det_gcdMatrix n (fun m ↦ (m.divisors.card : R)) (fun _ ↦ (1 : R)) fun m _ ↦ by simp

end Matrix
