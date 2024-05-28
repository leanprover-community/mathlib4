import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.RingTheory.MvPowerSeries.Symmetric.Basic


open Equiv (Perm)

open BigOperators

noncomputable section

variable {σ R : Type*} [CommSemiring R] [DecidableEq σ]

section ElementarySymmetric

open Classical

namespace MvPowerSeries

variable (σ R)

/-- The `n`th elementary symmetric `MvPowerSeries σ R`. -/
def esymm (n : ℕ) : MvPowerSeries σ R :=
  fun (s : σ →₀ ℕ) ↦ if s.sum (fun _ ↦ id) = n ∧ ∀ i : σ, s i ≤ 1 then 1 else 0

@[simp]
lemma esymm_def (n : ℕ) (s : σ →₀ ℕ) :
  esymm σ R n s = if s.sum (fun _ ↦ id) = n ∧ ∀ i : σ, s i ≤ 1 then 1 else 0 := rfl

@[simp]
lemma coeff_esymm (n : ℕ) (s : σ →₀ ℕ) :
  coeff R s (esymm σ R n) = if s.sum (fun _ ↦ id) = n ∧ ∀ i : σ, s i ≤ 1 then 1 else 0 := rfl

/-- The `n`th complete homogeneous symmetric `MvPowerSeries σ R`. -/
def hsymm (n : ℕ) : MvPowerSeries σ R :=
  fun (s : σ →₀ ℕ) ↦ if s.sum (fun _ ↦ id) = n then 1 else 0

@[simp]
lemma hsymm_def (n : ℕ) (s : σ →₀ ℕ) :
  hsymm σ R n s = if s.sum (fun _ ↦ id) = n then 1 else 0 := rfl

@[simp]
lemma coeff_hsymm (n : ℕ) (s : σ →₀ ℕ) :
  coeff R s (hsymm σ R n) = if s.sum (fun _ ↦ id) = n then 1 else 0 := rfl

/-- The `n`th power sum symmetric `MvPowerSeries σ R`. -/
def psum (n : ℕ) : MvPowerSeries σ R :=
  fun (s : σ →₀ ℕ) ↦ if s.sum (fun _ ↦ id) = n ∧ s.support.card = 1 then 1 else 0

@[simp]
lemma psum_def (n : ℕ) (s : σ →₀ ℕ) :
  psum σ R n s = if s.sum (fun _ ↦ id) = n ∧ s.support.card = 1 then 1 else 0 := rfl

@[simp]
lemma coeff_psum (n : ℕ) (s : σ →₀ ℕ) :
  coeff R s (psum σ R n) = if s.sum (fun _ ↦ id) = n ∧ s.support.card = 1 then 1 else 0 := rfl


variable {τ S : Type*} [CommSemiring S] [DecidableEq τ]

theorem map_esymm (n : ℕ) (f : R →+* S) : map _ f (esymm σ R n) = esymm σ S n := by
  ext s
  simp

theorem rename_esymm (n : ℕ) (e : σ ≃ τ) : rename e (esymm σ R n) = esymm τ R n := by
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

theorem map_hsymm (n : ℕ) (f : R →+* S) : map _ f (hsymm σ R n) = hsymm σ S n := by
  ext s
  simp

theorem rename_hsymm (n : ℕ) (e : σ ≃ τ) : rename e (hsymm σ R n) = hsymm τ R n := by
  ext s
  simp only [rename, AlgEquiv.coe_mk, coeff_equiv, coeff_hsymm, Finsupp.mapDomain_equiv_apply,
    Equiv.symm_symm]
  simp_rw [← Finsupp.equivMapDomain_eq_mapDomain]
  simp_rw [Finsupp.sum_equivMapDomain e.symm s (fun _ ↦ id)]

theorem map_psum (n : ℕ) (f : R →+* S) : map _ f (psum σ R n) = psum σ S n := by
  ext s
  simp

theorem rename_psum (n : ℕ) (e : σ ≃ τ) : rename e (psum σ R n) = psum τ R n := by
  ext s
  simp only [rename, AlgEquiv.coe_mk, coeff_equiv, coeff_psum, Finsupp.mapDomain_equiv_apply,
    Equiv.symm_symm]
  simp_rw [← Finsupp.equivMapDomain_eq_mapDomain]
  simp_rw [Finsupp.sum_equivMapDomain e.symm s (fun _ ↦ id)]
  sorry
