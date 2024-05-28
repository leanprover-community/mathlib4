/-
Copyright (c) 2024 Alessandro Iraci. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, Alessandro Iraci
-/

import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.RingTheory.MvPowerSeries.Symmetric.Basic

/-!
# Symmetric Functions

This file defines the elementary, complete homogeneous, and power sums symmetric `MvPowerSeries`s.

## Main declarations

* `MvPowerSeries.esymm`

* `MvPowerSeries.hsymm`

* `MvPowerSeries.psum`

## Notation

+ `esymm σ R n` is the `n`th elementary symmetric polynomial in `MvPolynomial σ R`.

+ `hsymm σ R n` is the `n`th complete homogeneous symmetric polynomial in `MvPolynomial σ R`.

+ `psum σ R n` is the degree-`n` power sum in `MvPolynomial σ R`, i.e. the sum of monomials
  `(X i)^n` over `i ∈ σ`.

As in other similar files, we typically use the notation:

+ `σ τ : Type*` (indexing the variables)

+ `R S : Type*` `[CommSemiring R]` `[CommSemiring S]` (the coefficients)

+ `r : R` elements of the coefficient ring

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

-/

open BigOperators Classical Equiv Perm

noncomputable section

variable {σ R : Type*} [CommSemiring R] [DecidableEq σ]
variable {τ S : Type*} [CommSemiring S] [DecidableEq τ]

namespace MvPowerSeries

variable (n : ℕ)
variable (σ R)

section ElementarySymmetric

/-- The `n`th elementary symmetric `MvPowerSeries σ R`. -/
def esymm : MvPowerSeries σ R :=
  fun (s : σ →₀ ℕ) ↦ if s.sum (fun _ ↦ id) = n ∧ ∀ i : σ, s i ≤ 1 then 1 else 0

@[simp]
lemma esymm_def (s : σ →₀ ℕ) :
  esymm σ R n s = if s.sum (fun _ ↦ id) = n ∧ ∀ i : σ, s i ≤ 1 then 1 else 0 := rfl

@[simp]
lemma coeff_esymm (s : σ →₀ ℕ) :
  coeff R s (esymm σ R n) = if s.sum (fun _ ↦ id) = n ∧ ∀ i : σ, s i ≤ 1 then 1 else 0 := rfl

theorem map_esymm (f : R →+* S) : map _ f (esymm σ R n) = esymm σ S n := by
  ext s
  simp

theorem rename_esymm (e : σ ≃ τ) : rename e (esymm σ R n) = esymm τ R n := by
  ext s
  simp only [rename, AlgEquiv.coe_mk, coeff_equiv, coeff_esymm, Finsupp.mapDomain_equiv_apply,
    Equiv.symm_symm]
  simp_rw [← Finsupp.equivMapDomain_eq_mapDomain]
  simp_rw [Finsupp.sum_equivMapDomain e.symm s (fun _ ↦ id)]
  by_cases h : s.sum (fun _ ↦ id) = n ∧ ∀ i : τ, s i ≤ 1
  · simp only [h, reduceIte, implies_true, and_true]
  · simp only [h, ↓reduceIte, ite_eq_right_iff]
    intro h'; exfalso; apply h
    simp only [h', true_and]
    intro i
    rw [← (Equiv.apply_symm_apply e i)]
    exact h'.2 (e.symm i)

instance : HasBoundedDegree (esymm σ R n) := by
  use n; intro s h
  simp only [coeff_esymm, ne_eq, ite_eq_right_iff, and_imp, not_forall, exists_prop,
    exists_and_left] at h
  simp [h.1]

instance : IsSymmetric (esymm σ R n) := by
  intro e
  exact rename_esymm _ _ n e

end ElementarySymmetric

section CompleteHomogeneousSymmetric

/-- The `n`th complete homogeneous symmetric `MvPowerSeries σ R`. -/
def hsymm : MvPowerSeries σ R :=
  fun (s : σ →₀ ℕ) ↦ if s.sum (fun _ ↦ id) = n then 1 else 0

@[simp]
lemma hsymm_def (s : σ →₀ ℕ) :
  hsymm σ R n s = if s.sum (fun _ ↦ id) = n then 1 else 0 := rfl

@[simp]
lemma coeff_hsymm (s : σ →₀ ℕ) :
  coeff R s (hsymm σ R n) = if s.sum (fun _ ↦ id) = n then 1 else 0 := rfl

theorem map_hsymm (f : R →+* S) : map _ f (hsymm σ R n) = hsymm σ S n := by
  ext s
  simp

theorem rename_hsymm (e : σ ≃ τ) : rename e (hsymm σ R n) = hsymm τ R n := by
  ext s
  simp only [rename, AlgEquiv.coe_mk, coeff_equiv, coeff_hsymm, Finsupp.mapDomain_equiv_apply,
    Equiv.symm_symm]
  simp_rw [← Finsupp.equivMapDomain_eq_mapDomain]
  simp_rw [Finsupp.sum_equivMapDomain e.symm s (fun _ ↦ id)]

instance : HasBoundedDegree (hsymm σ R n) := by
  use n; intro s h
  simp only [coeff_hsymm, ne_eq, ite_eq_right_iff, not_forall, exists_prop] at h
  simp [h.1]

instance : IsSymmetric (hsymm σ R n) := by
  intro e
  exact rename_hsymm _ _ n e

end CompleteHomogeneousSymmetric

section PowerSums

/-- The `n`th power sum symmetric `MvPowerSeries σ R`. -/
def psum : MvPowerSeries σ R :=
  fun (s : σ →₀ ℕ) ↦ if s.sum (fun _ ↦ id) = n ∧ s.support.card = 1 then 1 else 0

@[simp]
lemma psum_def (s : σ →₀ ℕ) :
  psum σ R n s = if s.sum (fun _ ↦ id) = n ∧ s.support.card = 1 then 1 else 0 := rfl

@[simp]
lemma coeff_psum (s : σ →₀ ℕ) :
  coeff R s (psum σ R n) = if s.sum (fun _ ↦ id) = n ∧ s.support.card = 1 then 1 else 0 := rfl

theorem map_psum (f : R →+* S) : map _ f (psum σ R n) = psum σ S n := by
  ext s
  simp

private def supportEquiv (s : σ →₀ ℕ) (e : σ ≃ τ) : { x // x ∈ s.support }
   ≃ { x // x ∈ (Finsupp.equivMapDomain e s).support } where
  toFun := fun ⟨x, hx⟩ ↦ ⟨e x, by simp [Finsupp.mem_support_iff.mp hx]⟩
  invFun := fun ⟨x, hx⟩ ↦ ⟨e.symm x, by
    rw [Finsupp.mem_support_iff, Finsupp.equivMapDomain_apply] at hx
    simp [hx]⟩
  left_inv := by intro i; simp
  right_inv := by intro i; simp

theorem rename_psum (e : σ ≃ τ) : rename e (psum σ R n) = psum τ R n := by
  ext s
  simp only [rename, AlgEquiv.coe_mk, coeff_equiv, coeff_psum]
  simp_rw [← Finsupp.equivMapDomain_eq_mapDomain, Finsupp.sum_equivMapDomain e.symm s (fun _ ↦ id)]
  rw [Finset.card_eq_of_equiv (supportEquiv _ _ e.symm)]

instance : HasBoundedDegree (psum σ R n) := by
  use n; intro s h
  simp only [coeff_psum, ne_eq, ite_eq_right_iff, and_imp, not_forall, exists_prop,
    exists_and_left] at h
  simp [h.1]

instance : IsSymmetric (psum σ R n) := by
  intro e
  exact rename_psum _ _ n e

end PowerSums

end MvPowerSeries

end
