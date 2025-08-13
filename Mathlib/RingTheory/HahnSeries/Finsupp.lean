/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Scott Carnahan
-/
import Mathlib.Algebra.MonoidAlgebra.Defs
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
def ofFinsupp [Zero R] (x : Γ →₀ R) : HahnSeries Γ R where
  coeff g := x g
  isPWO_support' := (Finsupp.finite_support x).isPWO

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
  simp only [Finsupp.sum, ofFinsupp_coeff]
  rw [sum_sigma', sum_apply']
  refine (Finset.sum_of_injOn
    (fun i ↦ ⟨i.1, i.2⟩) ?_ ?_ ?_ ?_).symm
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

namespace Finsupp

open Classical in
/-- A scalar multiplication of finitely supported functions on arbitrary functions. This is only
sensible with a `IsCancelVAdd Γ Γ'` typeclass assumption. -/
instance [VAdd Γ Γ'] [Zero R] [Zero V] [SMulZeroClass R V]
    [AddCommMonoid V] :
    SMul (Γ →₀ R) (Γ' → V) where
  smul f g x := ∑ i ∈ f.support, if h : ∃ y, i +ᵥ y = x then (f i) • (g h.choose) else 0

open Classical in
theorem smul_apply_conv [VAdd Γ Γ'] [Zero R] [Zero V] [SMulZeroClass R V]
    [AddCommMonoid V] (f : Γ →₀ R) (g : Γ' → V) (x : Γ') :
    (f • g) x =
      ∑ i ∈ f.support, if h : ∃ y, i +ᵥ y = x then (f i) • (g h.choose) else 0 := by
  rfl

theorem smul_apply_group [AddGroup Γ] [AddAction Γ Γ'] [Zero R] [Zero V]
    [SMulZeroClass R V] [AddCommMonoid V] (f : Γ →₀ R) (g : Γ' → V) (x : Γ') :
    (f • g) x = ∑ i ∈ f.support, (f i) • g (-i +ᵥ x) := by
  rw [smul_apply_conv]
  classical
  refine Finset.sum_congr rfl fun i hi ↦ dite_eq_iff.mpr <| Or.inl ?_
  have h : ∃ y, i +ᵥ y = x := Exists.intro (-i +ᵥ x) (vadd_neg_vadd i x)
  use h
  rw [eq_neg_vadd_iff.mpr h.choose_spec]

end Finsupp

namespace HahnModule

theorem ofFinsupp_smul_coeff [PartialOrder Γ] [PartialOrder Γ'] [VAdd Γ Γ']
    [IsOrderedCancelVAdd Γ Γ'] [Zero R] [AddCommMonoid V] [SMulZeroClass R V] (f : Γ →₀ R)
    (x : HahnModule Γ' R V) :
    ((of R).symm ((HahnSeries.ofFinsupp f) • x)).coeff = f • ((of R).symm x).coeff := by
  ext g
  rw [coeff_smul, Finsupp.smul_apply_conv]
  simp only [VAddAntidiagonal, HahnSeries.ofFinsupp_coeff]
  classical
  rw [sum_dite, sum_const_zero, add_zero]
  rw [@sum_eq_sum_extend]
  refine (sum_of_injOn Prod.fst (fun ⦃x₁⦄ ↦ ?_) ?_ ?_ ?_)
  · intro h₁ x₂ h₂ h₁₂
    simp only [Set.Finite.coe_toFinset, Set.mem_vaddAntidiagonal, HahnSeries.mem_support,
      HahnSeries.ofFinsupp_coeff, ne_eq] at h₁ h₂ h₁₂
    refine Prod.ext h₁₂ ?_
    have := h₁.2.2
    rw [h₁₂, ← h₂.2.2] at this
    exact IsCancelVAdd.left_cancel x₂.1 x₁.2 x₂.2 this
  · intro x₁ h₁
    simp only [Set.Finite.coe_toFinset, Set.mem_vaddAntidiagonal, HahnSeries.mem_support,
      HahnSeries.ofFinsupp_coeff, ne_eq] at h₁
    simp only [coe_filter, Finsupp.mem_support_iff, ne_eq, Set.mem_setOf_eq]
    exact ⟨h₁.1, x₁.2, h₁.2.2⟩
  · intro i hi hn
    rw [extend_def]
    have hei : ∃ a : { x // x ∈ {x ∈ f.support | ∃ y, x +ᵥ y = g} }, ↑a = i := by use ⟨i, hi⟩
    simp only [hei, ↓reduceDIte]
    have hej := (mem_filter.mp (hei.choose).2).2
    have hij : i +ᵥ hej.choose = g := by
      convert hej.choose_spec
      exact hei.choose_spec.symm
    have main : f i • ((of R).symm x).coeff hej.choose = 0 := by
      simp only [mem_filter, Finsupp.mem_support_iff] at hi
      simp only [Set.Finite.coe_toFinset, Set.mem_image, Set.mem_vaddAntidiagonal,
        HahnSeries.mem_support, HahnSeries.ofFinsupp_coeff, Prod.exists, exists_and_right,
        exists_and_left, exists_eq_right, not_and, not_exists] at hn
      have := hn hi.1 hej.choose
      refine smul_eq_zero_of_right (f i) ?_
      contrapose! this
      exact ⟨this, hij⟩
    convert main
    exact hei.choose_spec
  · intro ij hij
    simp only [Set.Finite.mem_toFinset, Set.mem_vaddAntidiagonal, HahnSeries.mem_support,
      HahnSeries.ofFinsupp_coeff, ne_eq] at hij
    rw [extend_def]
    have he : ∃ (a : { x // x ∈ {x ∈ f.support | ∃ y, x +ᵥ y = g} }), a = ij.1 := by
      simp only [Subtype.exists, mem_filter, Finsupp.mem_support_iff, exists_prop, exists_eq_right]
      exact ⟨hij.1, Exists.intro ij.2 hij.2.2⟩
    simp only [he, ↓reduceDIte]
    let y2 := (mem_filter.mp he.choose.2).2
    have : y2.choose = ij.2 := by
      apply IsCancelVAdd.left_cancel ij.1
      convert y2.choose_spec
      · exact he.choose_spec.symm
      · exact hij.2.2
    simp_rw [this, he.choose_spec]

end HahnModule
