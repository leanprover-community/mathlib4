/-
Copyright (c) 2025 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.BigOperators
import Mathlib.RingTheory.PowerSeries.Basic

/-!

# Some results on the coefficients of multiplication of two power series

## Main results

- `PowerSeries.coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal`,
  `PowerSeries.coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal'`:
  if for all `i ≤ n` (resp. for all `i`), the `i`-th coefficients of power series `f` and `g` are
  in ideals `I` and `J`, respectively, then for all `i ≤ n` (resp. for all `i`), the `i`-th
  coefficients of `f * g` are in `I * J`.

- `PowerSeries.coeff_mul_mem_ideal_of_coeff_right_mem_ideal`,
  `PowerSeries.coeff_mul_mem_ideal_of_coeff_right_mem_ideal'`:
  if for all `i ≤ n` (resp. for all `i`), the `i`-th coefficients of power series `g` are
  in ideal `I`, then for all `i ≤ n` (resp. for all `i`), the `i`-th coefficients of `f * g` are
  in `I`.

- `PowerSeries.coeff_mul_mem_ideal_of_coeff_left_mem_ideal`,
  `PowerSeries.coeff_mul_mem_ideal_of_coeff_left_mem_ideal'`:
  if for all `i ≤ n` (resp. for all `i`), the `i`-th coefficients of power series `f` are
  in ideal `I`, then for all `i ≤ n` (resp. for all `i`), the `i`-th coefficients of `f * g` are
  in `I`.

-/

namespace PowerSeries

variable {A : Type*} [Semiring A] {I J : Ideal A} {f g : A⟦X⟧} (n : ℕ)

theorem coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal (hf : ∀ i ≤ n, coeff i f ∈ I)
    (hg : ∀ i ≤ n, coeff i g ∈ J) : ∀ i ≤ n, coeff i (f * g) ∈ I * J := fun i hi ↦ by
  rw [coeff_mul]
  exact Ideal.sum_mem _ fun p hp ↦ Ideal.mul_mem_mul
    (hf _ ((Finset.antidiagonal.fst_le hp).trans hi))
    (hg _ ((Finset.antidiagonal.snd_le hp).trans hi))

theorem coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal' (hf : ∀ i, coeff i f ∈ I)
    (hg : ∀ i, coeff i g ∈ J) : ∀ i, coeff i (f * g) ∈ I * J :=
  fun i ↦ coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal i
    (fun i _ ↦ hf i) (fun i _ ↦ hg i) i le_rfl

theorem coeff_mul_mem_ideal_of_coeff_right_mem_ideal
    (hg : ∀ i ≤ n, coeff i g ∈ I) : ∀ i ≤ n, coeff i (f * g) ∈ I := by
  simpa using coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal (I := ⊤) (f := f) n (by simp) hg

theorem coeff_mul_mem_ideal_of_coeff_right_mem_ideal'
    (hg : ∀ i, coeff i g ∈ I) : ∀ i, coeff i (f * g) ∈ I := by
  simpa using coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal' (I := ⊤) (f := f) (by simp) hg

variable [I.IsTwoSided]

theorem coeff_mul_mem_ideal_of_coeff_left_mem_ideal
    (hf : ∀ i ≤ n, coeff i f ∈ I) : ∀ i ≤ n, coeff i (f * g) ∈ I := by
  simpa only [Ideal.IsTwoSided.mul_one] using
    coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal (J := 1) (g := g) n hf (by simp)

theorem coeff_mul_mem_ideal_of_coeff_left_mem_ideal'
    (hf : ∀ i, coeff i f ∈ I) : ∀ i, coeff i (f * g) ∈ I := by
  simpa only [Ideal.IsTwoSided.mul_one] using
    coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal' (J := 1) (g := g) hf (by simp)

end PowerSeries
