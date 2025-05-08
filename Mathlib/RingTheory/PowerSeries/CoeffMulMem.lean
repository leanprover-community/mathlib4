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

-/

namespace PowerSeries

variable {A : Type*} [Semiring A] {I J : Ideal A}

theorem coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal
    (f g : A⟦X⟧) (n : ℕ) (hf : ∀ i ≤ n, coeff A i f ∈ I)
    (hg : ∀ i ≤ n, coeff A i g ∈ J) : ∀ i ≤ n, coeff A i (f * g) ∈ I * J := fun i hi ↦ by
  rw [coeff_mul]
  exact Ideal.sum_mem _ fun p hp ↦ Ideal.mul_mem_mul
    (hf _ ((Finset.antidiagonal.fst_le hp).trans hi))
    (hg _ ((Finset.antidiagonal.snd_le hp).trans hi))

theorem coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal'
    (f g : A⟦X⟧) (hf : ∀ i, coeff A i f ∈ I)
    (hg : ∀ i, coeff A i g ∈ J) : ∀ i, coeff A i (f * g) ∈ I * J :=
  fun i ↦ f.coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal g i
    (fun i _ ↦ hf i) (fun i _ ↦ hg i) i le_rfl

theorem coeff_mul_mem_ideal_of_coeff_right_mem_ideal
    (f g : A⟦X⟧) (n : ℕ) (hg : ∀ i ≤ n, coeff A i g ∈ I) : ∀ i ≤ n, coeff A i (f * g) ∈ I := by
  simpa using f.coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal (I := ⊤) g n (by simp) hg

theorem coeff_mul_mem_ideal_of_coeff_right_mem_ideal'
    (f g : A⟦X⟧) (hg : ∀ i, coeff A i g ∈ I) : ∀ i, coeff A i (f * g) ∈ I := by
  simpa using f.coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal' (I := ⊤) g (by simp) hg

variable [I.IsTwoSided]

theorem coeff_mul_mem_ideal_of_coeff_left_mem_ideal
    (f g : A⟦X⟧) (n : ℕ) (hf : ∀ i ≤ n, coeff A i f ∈ I) : ∀ i ≤ n, coeff A i (f * g) ∈ I := by
  simpa only [Ideal.IsTwoSided.mul_one] using
    f.coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal (J := 1) g n hf (by simp)

theorem coeff_mul_mem_ideal_of_coeff_left_mem_ideal'
    (f g : A⟦X⟧) (hf : ∀ i, coeff A i f ∈ I) : ∀ i, coeff A i (f * g) ∈ I := by
  simpa only [Ideal.IsTwoSided.mul_one] using
    f.coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal' (J := 1) g hf (by simp)

end PowerSeries
