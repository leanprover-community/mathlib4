/-
Copyright (c) 2025 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia, Andrew Yang
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Finsupp
public import Mathlib.Algebra.Order.Group.Pointwise.Interval
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.Order.BourbakiWitt
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Ideals of `MvPolynomial` defined by `restrictSupport`

This file contains basic results about `MvPolynomial.restrictSupport` and ideals of `MvPolynomial`.

## Main definitions

* `restrictSupportIdeal R s`: The ideal defined by `restrictSupport R s` when `s` is an upper set.
* `idealOfVars σ R`: The ideal spanned by all variables.

## Main results

* `MvPolynomial.pow_idealOfVars_eq_span`
* `MvPolynomial.mem_pow_idealOfVars_iff`

-/

@[expose] public section


variable {σ R : Type*}

namespace MvPolynomial

variable [CommSemiring R]

open Finset Finsupp

lemma restrictSupport_eq_span (s : Set (σ →₀ ℕ)) :
    restrictSupport R s = .span _ ((monomial · 1) '' s) := Finsupp.supported_eq_span_single ..

lemma mem_restrictSupport_iff {s : Set (σ →₀ ℕ)} {r : MvPolynomial σ R} :
    r ∈ restrictSupport R s ↔ ↑r.support ⊆ s := .rfl

@[simp]
lemma monomial_mem_restrictSupport {s : Set (σ →₀ ℕ)} {m} {r : R} :
    monomial m r ∈ restrictSupport R s ↔ m ∈ s ∨ r = 0 := by
  classical
  by_cases r = 0 <;> simp [mem_restrictSupport_iff, support_monomial, *]

open Pointwise in
lemma restrictSupport_add (s t : Set (σ →₀ ℕ)) :
    restrictSupport R (s + t) = restrictSupport R s * restrictSupport R t := by
  apply le_antisymm
  · rw [restrictSupport_eq_span, Submodule.span_le, Set.image_subset_iff, Set.add_subset_iff]
    intro x hx y hy
    simp [show monomial (x + y) (1 : R) = monomial x 1 * monomial y 1 by simp, -monomial_mul,
      *, Submodule.mul_mem_mul]
  · rw [restrictSupport_eq_span, restrictSupport_eq_span, Submodule.span_mul_span,
      Submodule.span_le, Set.mul_subset_iff]
    simp +contextual [Set.add_mem_add]

open Pointwise in
@[simp] lemma restrictSupport_zero : restrictSupport R (0 : Set (σ →₀ ℕ)) = 1 := by
  classical
  apply le_antisymm
  · rw [restrictSupport_eq_span, Submodule.span_le, Set.image_subset_iff]
    simpa using ⟨1, by simp⟩
  · rintro _ ⟨x, rfl⟩
    simp [mem_restrictSupport_iff, Set.subset_def, coeff_one]

@[simp]
lemma restrictSupport_univ : restrictSupport R (.univ : Set (σ →₀ ℕ)) = ⊤ := by
  ext; simp [mem_restrictSupport_iff]

open Pointwise in
lemma restrictSupport_nsmul (n : ℕ) (s : Set (σ →₀ ℕ)) :
    restrictSupport R (n • s) = restrictSupport R s ^ n := by
  induction n <;> simp [add_smul, restrictSupport_add, *, pow_succ]

/-- The ideal defined by `restrictSupport R s` when `s` is an upper set. -/
def restrictSupportIdeal (s : Set (σ →₀ ℕ)) (hs : IsUpperSet s) :
    Ideal (MvPolynomial σ R) where
  __ := restrictSupport R s
  smul_mem' x y hy m (hm : m ∈ (x * y).support) := by
    classical
    simp only [mem_support_iff, coeff_mul, ne_eq] at hm
    obtain ⟨⟨i, j⟩, hij, e⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
    refine hs (by simp_all [eq_comm]) (hy (show j ∈ y.support by aesop))

@[simp]
lemma restrictScalars_restrictSupportIdeal (s : Set (σ →₀ ℕ)) (hs) :
  (restrictSupportIdeal (R := R) s hs).restrictScalars R = restrictSupport R s := by rfl

variable (σ R) in
/-- The ideal spanned by all variables. -/
def idealOfVars : Ideal (MvPolynomial σ R) := .span (Set.range X)

lemma idealOfVars_eq_restrictSupportIdeal :
    idealOfVars σ R = restrictSupportIdeal _ ((isUpperSet_Ici 1).preimage degree_mono) := by
  apply le_antisymm
  · simp [idealOfVars, Ideal.span_le, Set.range_subset_iff, restrictSupportIdeal, X]
  · change restrictSupport _ _ ≤ (idealOfVars σ R).restrictScalars R
    rw [restrictSupport_eq_span, Submodule.span_le, Set.image_subset_iff]
    intro x hx
    obtain ⟨i, hi⟩ : x.support.Nonempty := by aesop
    obtain ⟨c, rfl⟩ := le_iff_exists_add'.mp (show single i 1 ≤ x by simp_all; lia)
    simpa [monomial_add_single] using Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))

open Pointwise in
lemma pow_idealOfVars (n : ℕ) :
    idealOfVars σ R ^ n = restrictSupportIdeal _ ((isUpperSet_Ici n).preimage degree_mono) := by
  rw [idealOfVars_eq_restrictSupportIdeal]
  apply Submodule.restrictScalars_injective R
  by_cases hn : n = 0
  · simp [hn, show Set.Ici 0 = Set.univ by ext; simp, Ideal.one_eq_top]
  rw [Submodule.restrictScalars_pow hn]
  refine (restrictSupport_nsmul ..).symm.trans (congr_arg (restrictSupport R) ?_)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' (Nat.one_le_cast_iff_ne_zero.mpr hn)
  clear hn; induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul, ih]
    refine Set.Subset.antisymm (Set.Subset.trans (Set.preimage_add_preimage_subset _)
      (Set.preimage_mono (Set.Ici_add_Ici_subset ..))) ?_
    simp only [Set.subset_def, Set.mem_preimage, Set.mem_Ici, Set.mem_add]
    intro x x_deg
    obtain ⟨i, i_in⟩ := support_nonempty_iff (f := x).mpr (by grind only [= map_zero])
    have : single i 1 ≤ x := by
      classical
      rw [le_def]; intro j
      rw [single_apply]; split_ifs with h
      · rwa [← h, Nat.one_le_iff_ne_zero, ← Finsupp.mem_support_iff]
      simp
    obtain ⟨z, hz⟩ := exists_add_of_le this
    rw [add_comm, hz, map_add, degree_single, Nat.add_le_add_iff_left] at x_deg
    exact ⟨z, x_deg, ⟨single i 1, by simp, by rw [hz, add_comm]⟩⟩

/-- The `n`th power of `idealOfVars` is spanned by all monomials of total degree `n`. -/
theorem pow_idealOfVars_eq_span (n) : idealOfVars σ R ^ n =
    .span ((fun x ↦ monomial x 1) '' {x | x.sum (fun _ => id) = n}) := by
  rw [idealOfVars, Ideal.span, Submodule.span_pow, ← Set.image_univ,
    Set.image_pow_eq_image_finsupp_prod]
  simp [monomial_eq]

theorem mem_pow_idealOfVars_iff (n : ℕ) (p : MvPolynomial σ R) :
    p ∈ idealOfVars σ R ^ n ↔ ∀ x ∈ p.support, n ≤ x.sum (fun _ => id) := by
  rw [pow_idealOfVars]
  simp [restrictSupportIdeal, mem_restrictSupport_iff, Set.subset_def, sum, degree]

theorem mem_pow_idealOfVars_iff' (n : ℕ) (p : MvPolynomial σ R) :
    p ∈ idealOfVars σ R ^ n ↔ ∀ x, x.sum (fun _ => id) < n → p.coeff x = 0 := by
  grind only [mem_pow_idealOfVars_iff, mem_support_iff]

theorem monomial_mem_pow_idealOfVars_iff (n : ℕ) (x : σ →₀ ℕ) {r : R} (h : r ≠ 0) :
    monomial x r ∈ idealOfVars σ R ^ n ↔ n ≤ x.sum fun _ => id := by
  classical
  grind only [mem_pow_idealOfVars_iff, mem_support_iff, coeff_monomial]

theorem C_mem_pow_idealOfVars_iff (n r) : C r ∈ idealOfVars σ R ^ n ↔ r = 0 ∨ n = 0 := by
  by_cases h : r = 0
  · simp [h]
  simpa [h] using monomial_mem_pow_idealOfVars_iff (σ := σ) n 0 h

end MvPolynomial
