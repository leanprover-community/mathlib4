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

## Implementation notes

`Matrix.zetaMatrix n` is a matrix over `ℤ`; here it is mapped into `R` by `Int.cast`, which keeps
`det = 1` (`RingHom.map_det`). The entry-wise identity behind the factorisation is
`∑ k, [k + 1 ∣ i + 1] [k + 1 ∣ j + 1] g (k + 1) = ∑ d ∣ gcd (i + 1) (j + 1), g d`, obtained from
`Matrix.sum_fin_dvd_dvd_eq_sum_divisors` with `a = 1` and `Nat.dvd_gcd_iff`.

## References

* [H. J. S. Smith, *On the value of a certain arithmetical determinant*][smith1875]

## Tags

smith determinant, gcd matrix, zeta matrix, totient
-/

@[expose] public section

open Finset

namespace Matrix

variable {R : Type*}

/-- The GCD matrix of `f`: the `n × n` matrix with entry `f (gcd (i + 1) (j + 1))`. -/
def gcdMatrix (n : ℕ) (f : ℕ → R) : Matrix (Fin n) (Fin n) R :=
  of fun i j ↦ f (Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1))

@[simp] theorem gcdMatrix_apply (n : ℕ) (f : ℕ → R) (i j : Fin n) :
    gcdMatrix n f i j = f (Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1)) := rfl

variable [CommRing R]

theorem zetaMatrix_map_intCast_apply (n : ℕ) (i j : Fin n) :
    (zetaMatrix n).map (Int.cast : ℤ → R) i j = if (i : ℕ) + 1 ∣ (j : ℕ) + 1 then 1 else 0 := by
  simp [map_apply, apply_ite (Int.cast : ℤ → R)]

theorem det_zetaMatrix_map_intCast (n : ℕ) : ((zetaMatrix n).map (Int.cast : ℤ → R)).det = 1 := by
  have h := (Int.castRingHom R).map_det (zetaMatrix n)
  rw [det_zetaMatrix, map_one, RingHom.mapMatrix_apply] at h
  simpa using h.symm

theorem sum_fin_dvd_dvd_eq_sum_divisors_gcd (n : ℕ) (g : ℕ → R) (i j : Fin n) :
    (∑ k : Fin n, if (k : ℕ) + 1 ∣ (i : ℕ) + 1 ∧ (k : ℕ) + 1 ∣ (j : ℕ) + 1 then g ((k : ℕ) + 1)
      else 0) = ∑ d ∈ (Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1)).divisors, g d := by
  have hpos : 0 < Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1) := Nat.gcd_pos_of_pos_left _ (by omega)
  have hle : Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1) ≤ n :=
    (Nat.gcd_le_left ((j : ℕ) + 1) (by omega)).trans (by omega)
  have h := sum_fin_dvd_dvd_eq_sum_divisors n 1 (Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1)) g le_rfl hpos
    (one_dvd _) hle
  simp only [one_dvd, true_and, Nat.div_one] at h
  rw [← h]
  refine sum_congr rfl fun k _ ↦ ?_
  simp [Nat.dvd_gcd_iff]

/-- The factorisation behind Smith's determinant: `gcdMatrix n f = Zᵀ * (D * Z)` with `Z` the zeta
matrix and `D` the diagonal matrix of `g`, whenever `f m = ∑ d ∣ m, g d` for `m ≥ 1`. -/
theorem gcdMatrix_eq_transpose_mul_mul (n : ℕ) (f g : ℕ → R)
    (hfg : ∀ m, 0 < m → f m = ∑ d ∈ m.divisors, g d) :
    gcdMatrix n f =
      ((zetaMatrix n).map (Int.cast : ℤ → R))ᵀ *
        (diagonal (fun i : Fin n ↦ g ((i : ℕ) + 1)) * (zetaMatrix n).map (Int.cast : ℤ → R)) := by
  ext i j
  rw [gcdMatrix_apply, hfg _ (Nat.gcd_pos_of_pos_left _ (by omega)),
    ← sum_fin_dvd_dvd_eq_sum_divisors_gcd n g i j, mul_apply]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [transpose_apply, zetaMatrix_map_intCast_apply, mul_apply]
  simp only [diagonal_apply, zetaMatrix_map_intCast_apply]
  rw [sum_eq_single k (fun b _ hb ↦ by simp [Ne.symm hb]) (by simp)]
  by_cases h1 : (k : ℕ) + 1 ∣ (i : ℕ) + 1 <;> by_cases h2 : (k : ℕ) + 1 ∣ (j : ℕ) + 1 <;>
    simp [h1, h2]

/-- **Smith's determinant** (1875): if `f m = ∑ d ∣ m, g d` for every `m ≥ 1`, then the
determinant of the GCD matrix of `f` is `g 1 * g 2 * ⋯ * g n`. -/
theorem det_gcdMatrix (n : ℕ) (f g : ℕ → R) (hfg : ∀ m, 0 < m → f m = ∑ d ∈ m.divisors, g d) :
    (gcdMatrix n f).det = ∏ i : Fin n, g ((i : ℕ) + 1) := by
  rw [gcdMatrix_eq_transpose_mul_mul n f g hfg, det_mul, det_transpose, det_mul,
    det_zetaMatrix_map_intCast, det_diagonal, one_mul, mul_one]

/-- The classical case of Smith's determinant: `det [gcd (i, j)] = φ 1 * φ 2 * ⋯ * φ n`. -/
theorem det_gcdMatrix_id (n : ℕ) :
    (gcdMatrix n (fun m ↦ (m : R))).det = ∏ i : Fin n, (Nat.totient ((i : ℕ) + 1) : R) :=
  det_gcdMatrix n (fun m ↦ (m : R)) (fun m ↦ (Nat.totient m : R)) fun m _ ↦ by
    rw [← Nat.cast_sum, Nat.sum_totient]

end Matrix
