/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Scott Carnahan
-/
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Data.Finsupp.PointwiseSMul
import Mathlib.RingTheory.HahnSeries.Multiplication

-- Merge the relevant results into multiplication.

/-!
# Finitely supported Hahn series
We describe Hahn series with finitely many nonzero coefficients.

## Main Definitions
 * `HahnSeries.ofFinsupp` is a Hahn series whose coefficients are those of a finitely supported
   function `Γ →₀ R`.

## Main results
 *

## TODO

-/

open Finset Function Pointwise

noncomputable section

variable {Γ Γ' Γ₁ Γ₂ F R S U V : Type*}

namespace HahnSeries

section ring

variable [PartialOrder Γ]

@[simp]
theorem ofFinsupp_single [Zero R] (g : Γ) (r : R) :
    ofFinsupp (Finsupp.single g r) = HahnSeries.single g r := by
  ext g'
  by_cases h : g = g'
  · simp [h]
  · simp [h, coeff_single_of_ne fun a ↦ h a.symm]

@[simp]
theorem ofFinsupp_add [AddCommMonoid R] (x y : Γ →₀ R) :
    ofFinsupp (x + y) = ofFinsupp x + ofFinsupp y := by
  ext
  simp

@[simp]
theorem ofFinsupp_smul [Zero V] [SMulZeroClass R V] (r : R) (x : Γ →₀ V) :
    r • ofFinsupp (x) = ofFinsupp (r • x) := by
  ext
  simp

@[simp]
theorem ofFinsupp_neg [AddGroup R] (x : Γ →₀ R) :
    ofFinsupp (Neg.neg x) = -ofFinsupp x := by
  ext
  simp

@[simp]
theorem ofFinsupp_sub [AddGroup R] (x y : Γ →₀ R) :
    ofFinsupp (x - y) = ofFinsupp x - ofFinsupp y := by
  ext
  simp

@[simp]
theorem ofFinsupp_zero [Zero R] :
    ofFinsupp (0 : Γ →₀ R) = 0 := by
  rfl

@[simp]
theorem ofFinsupp_one [Semiring R] [Zero Γ] :
    ofFinsupp (1 : AddMonoidAlgebra R Γ) = 1 := by
  ext g
  by_cases h : g = 0
  · simp [h, AddMonoidAlgebra.one_def]
  · simpa [MonoidAlgebra.one_def, h] using Finsupp.single_eq_of_ne fun a ↦ h a.symm

theorem ofFinsupp_mul [Semiring R] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ]
    (x y : AddMonoidAlgebra R Γ) :
    ofFinsupp (x * y) = ofFinsupp x * ofFinsupp y := by
  ext g
  rw [coeff_mul, AddMonoidAlgebra.mul_def]
  simp only [Finsupp.sum, coeff_ofFinsupp]
  rw [sum_sigma', sum_apply']
  refine (Finset.sum_of_injOn
    (fun i ↦ ⟨i.1, i.2⟩) ?_ ?_ ?_ ?_).symm
  · intro i hi ij h1 h2
    exact Prod.ext_iff.mpr (by simp_all)
  · intro i hi
    simp only [coe_sigma, Set.mem_sigma_iff, mem_coe, Finsupp.mem_support_iff]
    simp only [mem_coe, mem_addAntidiagonal, mem_support, coeff_ofFinsupp] at hi
    exact ⟨hi.1,hi.2.1⟩
  · intro i hi hin
    simp only [Set.mem_image, mem_coe, mem_addAntidiagonal, mem_support, coeff_ofFinsupp, ne_eq,
      Prod.exists, not_exists, not_and, and_imp] at hin
    rw [Finsupp.single_apply_eq_zero]
    intro hg
    simp only [mem_sigma, Finsupp.mem_support_iff, ne_eq] at hi
    have := hin i.1 i.2
    simp only [Sigma.eta, not_true_eq_false, imp_false] at this
    exact ((this hi.1 hi.2) hg.symm).elim
  · intro i hi
    rw [← AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.mul_def]
    simp only [mul_zero, Finsupp.single_zero, Finsupp.sum_single_index, zero_mul]
    rw [mem_addAntidiagonal] at hi
    rw [hi.2.2, Finsupp.single_eq_same]

theorem ofFinsupp_pow [Semiring R] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ]
    (x : AddMonoidAlgebra R Γ) (n : ℕ) :
    ofFinsupp (x ^ n) = ofFinsupp x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [ofFinsupp_mul, pow_add, ih]

end ring

end HahnSeries

namespace HahnModule

open Finsupp in
theorem ofFinsupp_smul_coeff [PartialOrder Γ] [PartialOrder Γ'] [VAdd Γ Γ'] [DecidableEq Γ']
    [IsOrderedCancelVAdd Γ Γ'] [Zero R] [AddCommMonoid V] [SMulWithZero R V] (f : Γ →₀ R)
    (x : HahnModule Γ' R V) :
    ((of R).symm ((HahnSeries.ofFinsupp f) • x)).coeff = f • ((of R).symm x).coeff := by
  ext g
  rw [coeff_smul,  Finsupp.smul_eq]
  simp only [HahnSeries.coeff_ofFinsupp]
  refine (Finset.sum_of_injOn (M := V) id (Set.injOn_id _) ?_ ?_ ?_).symm
  · intro gh h
    simpa [mem_coe, mem_vaddAntidiagonal_iff] using h
  · intro gh h hn
    simp only [mem_vaddAntidiagonal] at h
    simp only [id_eq, Set.image_id', mem_coe, mem_vaddAntidiagonal_iff, h.2.2, and_true] at hn
    aesop
  · intro gh h
    simp

end HahnModule
