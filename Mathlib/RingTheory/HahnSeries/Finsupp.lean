/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Scott Carnahan
-/
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
import Mathlib.RingTheory.HahnSeries.Multiplication


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

/-- Makes a Hahn series out of a finitely supported function. -/
@[simps]
def ofFinsupp [Zero R] (x : (Multiplicative Γ) →₀ R) : HahnSeries Γ R where
  coeff g := x (Multiplicative.ofAdd g)
  isPWO_support' := (Finsupp.finite_support x).isPWO

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
  simp only [ofFinsupp_coeff, Finsupp.coe_neg, Pi.neg_apply, coeff_neg']

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
    ofFinsupp (1 : MonoidAlgebra R (Multiplicative Γ)) = 1 := by
  ext g
  by_cases h : g = 0
  · simp [h, MonoidAlgebra.one_def]
  · simpa [MonoidAlgebra.one_def, h] using Finsupp.single_eq_of_ne fun a ↦ h a.symm

theorem ofFinsupp_mul [Semiring R] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ]
    (x y : MonoidAlgebra R (Multiplicative Γ)) :
    ofFinsupp (x * y) = ofFinsupp x * ofFinsupp y := by
  ext g
  rw [coeff_mul, MonoidAlgebra.mul_def]
  simp only [Finsupp.sum, ofFinsupp_coeff]
  rw [sum_sigma', sum_apply']
  refine (Finset.sum_of_injOn
    (fun i ↦ ⟨Multiplicative.ofAdd i.1, Multiplicative.ofAdd i.2⟩) ?_ ?_ ?_ ?_).symm
  · intro i hi ij h1 h2
    exact Prod.ext_iff.mpr (by simp_all)
  · intro i hi
    simp only [coe_sigma, Set.mem_sigma_iff, mem_coe, Finsupp.mem_support_iff]
    simp only [mem_coe, mem_addAntidiagonal, mem_support, ofFinsupp_coeff] at hi
    exact ⟨hi.1,hi.2.1⟩
  · intro i hi hin
    simp only [Set.mem_image, mem_coe, mem_addAntidiagonal, mem_support, ofFinsupp_coeff, ne_eq,
      Prod.exists, not_exists, not_and, and_imp] at hin
    rw [Finsupp.single_apply_eq_zero]
    intro hg
    simp only [mem_sigma, Finsupp.mem_support_iff, ne_eq] at hi
    have := hin (Multiplicative.toAdd i.1) (Multiplicative.toAdd i.2)
    simp only [ofAdd_toAdd, Sigma.eta, not_true_eq_false, imp_false] at this
    have := this hi.1 hi.2
    rw [Multiplicative.ext_iff,toAdd_ofAdd, toAdd_mul] at hg
    exact (this hg.symm).elim
  · intro i hi
    rw [← MonoidAlgebra.single_mul_single, MonoidAlgebra.mul_def]
    simp only [mul_zero, Finsupp.single_zero, Finsupp.sum_single_index, zero_mul]
    rw [mem_addAntidiagonal] at hi
    rw [← ofAdd_add, Finsupp.single_apply_left (f := Multiplicative.ofAdd) fun _ _ a ↦ a, hi.2.2,
      Finsupp.single_eq_same]

theorem ofFinsupp_pow [Semiring R] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ]
    (x : MonoidAlgebra R (Multiplicative Γ)) (n : ℕ) :
    ofFinsupp (x ^ n) = ofFinsupp x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [ofFinsupp_mul, pow_add, ih]

end ring

end HahnSeries

namespace Finsupp

open Classical in
/-- The scalar multiplication of finitely supported functions on arbitrary functions. -/
def SMul [VAdd Γ Γ'] [Zero R] [Zero V] [SMulZeroClass R V]
    [AddCommMonoid V] :
    (Γ →₀ R) → (Γ' → V) → (Γ' → V) :=
  fun f g x ↦ ∑ i ∈ f.support, if h : ∃ y, i +ᵥ y = x then (f i) • (g h.choose) else 0

open Classical in
theorem SMul_apply [VAdd Γ Γ'] [Zero R] [Zero V] [SMulZeroClass R V]
    [AddCommMonoid V] (f : Γ →₀ R) (g : Γ' → V) (x : Γ') :
    SMul f g x =
      ∑ i ∈ f.support, if h : ∃ y, i +ᵥ y = x then (f i) • (g h.choose) else 0 := by
  rfl
-- action of Finsupps on formal functions for `vAdd Γ Γ'`. Need [IsCancelVAdd Γ Γ'] to prove
-- nice properties

end Finsupp
