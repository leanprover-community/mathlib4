/-
Copyright (c) 2024 Alessandro Iraci. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, Alessandro Iraci
-/
import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# Degree on MvPowerSeries

This file defines a degree on MvPowerSeries, with values in WithTop WithBot ℕ.

## Main declarations

* `MvPowerSeries.degree`

-/

open Classical

section Degree

namespace MvPowerSeries


variable {σ R S : Type*} [CommSemiring R] [DecidableEq (MvPowerSeries σ R)]
variable {φ ψ : MvPowerSeries σ R}

/-- A `MvPowerSeries φ` has degree bound n if its monomials are uniformly bounded by n-/
def HasDegreeBound (n : WithTop ℕ) : MvPowerSeries σ R → Prop :=
  fun φ ↦ (∀ s : σ →₀ ℕ, coeff R s φ ≠ 0 → s.sum (fun _ ↦ id) ≤ n)

@[simp]
theorem HasDegreeBound_def {n : WithTop ℕ} : HasDegreeBound n φ ↔
  ∀ s : σ →₀ ℕ, coeff R s φ ≠ 0 → s.sum (fun _ ↦ id) ≤ n := by rfl

/-- A `MvPowerSeries φ` has bounded degree if its monomials are uniformly bounded -/
def HasBoundedDegree (φ : MvPowerSeries σ R) : Prop :=
  ∃ n : ℕ, HasDegreeBound n φ

@[simp]
theorem HasBoundedDegree_def : HasBoundedDegree φ ↔ ∃ n : ℕ, HasDegreeBound n φ := by rfl

noncomputable def totalDegree := fun (φ : MvPowerSeries σ R) ↦ sInf { n | HasDegreeBound n φ }

theorem totalDegree_def : φ.totalDegree = sInf { n | HasDegreeBound n φ } := rfl

@[simp]
theorem hasDegreeBound_degree : HasDegreeBound φ.totalDegree φ := by
  simp only [totalDegree_def, HasDegreeBound_def, Nat.cast_finsupp_sum, id_eq, le_sInf_iff,
    Set.mem_setOf_eq]
  intro s hs b hb
  exact_mod_cast hb s hs

@[simp]
lemma hasDegreeBound_of_le {n : WithTop ℕ} (hn : HasDegreeBound n φ) (m : WithTop ℕ) (h : n ≤ m) :
    HasDegreeBound m φ := by
  simp only [HasDegreeBound_def, Nat.cast_finsupp_sum, id_eq]
  simp only [HasDegreeBound_def, Nat.cast_finsupp_sum, id_eq] at hn
  intro s hs
  exact le_trans (hn s hs) h

@[simp]
theorem totalDegree_le_DegreeBound {n : WithTop ℕ} (h : HasDegreeBound n φ) :
    φ.totalDegree ≤ n := by
  simp only [totalDegree_def, le_sInf_iff, Set.mem_setOf_eq]
  exact sInf_le h

@[simp]
theorem totalDegree_le_DegreeBound_iff {n : WithTop ℕ} :
    HasDegreeBound n φ ↔ φ.totalDegree ≤ n := by
  constructor
  · exact totalDegree_le_DegreeBound
  · intro h
    apply hasDegreeBound_of_le
    · exact hasDegreeBound_degree
    · exact h

theorem le_totalDegree {s : σ →₀ ℕ} (h : φ s ≠ 0) : (s.sum fun _ ↦ id) ≤ totalDegree φ := by
  simp only [Nat.cast_finsupp_sum, id_eq, totalDegree, le_sInf_iff, Set.mem_setOf_eq]
  intro b hb
  simp only [HasDegreeBound, ne_eq, Nat.cast_finsupp_sum, id_eq] at hb
  apply hb
  exact h

theorem totalDegree_le_of_support_subset (h : ∀ s, φ s ≠ 0 → ψ s ≠ 0) :
    totalDegree φ ≤ totalDegree ψ := by
  simp only [totalDegree, le_sInf_iff, Set.mem_setOf_eq]
  intro d hd
  apply sInf_le
  intro s hs
  apply h at hs
  apply hd
  exact hs

@[simp]
theorem totalDegree_zero : (0 : MvPowerSeries σ R).totalDegree = 0 := by
  simp only [totalDegree, HasDegreeBound, map_zero, ne_eq, not_true_eq_false, Nat.cast_finsupp_sum,
    id_eq, IsEmpty.forall_iff, forall_const, Set.setOf_true, sInf_univ, bot_eq_zero']

@[simp]
theorem totalDegree_C (r : R) : (C σ R r : MvPowerSeries σ R).totalDegree = 0 := by
  rw [totalDegree_def]
  apply le_antisymm
  · apply sInf_le
    simp only [HasDegreeBound, ne_eq, Nat.cast_finsupp_sum, id_eq, Set.mem_setOf_eq]
    intro s hs
    simp only [coeff_C, ite_eq_right_iff, not_forall, exists_prop] at hs
    rw [hs.1]
    simp only [Finsupp.sum_zero_index, Nat.cast_zero, le_refl]
  · simp only [HasDegreeBound_def, ne_eq, Nat.cast_finsupp_sum, id_eq, le_sInf_iff,
    Set.mem_setOf_eq, zero_le, implies_true, forall_const]

@[simp]
theorem totalDegree_one : (1 : MvPowerSeries σ R).totalDegree = 0 := by
  apply totalDegree_C (1 : R)

@[simp]
theorem totalDegree_X [Nontrivial R] (i : σ) : (X i : MvPowerSeries σ R).totalDegree = 1 := by
  rw [totalDegree, X_def]
  simp_rw [HasDegreeBound_def, coeff_monomial]
  simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not, Nat.cast_finsupp_sum, id_eq,
    forall_eq, Nat.cast_zero, Finsupp.sum_single_index, Nat.cast_one]
  apply le_antisymm
  · apply sInf_le
    simp only [Set.mem_setOf_eq, le_refl]
  · apply le_sInf
    simp only [Set.mem_setOf_eq, imp_self, forall_const]

lemma totalDegreeBound_le : φ.totalDegree ≤ ψ.totalDegree ↔
    ∀ n, (HasDegreeBound n ψ → HasDegreeBound n φ) := by
  constructor
  · intro h n hn
    apply hasDegreeBound_of_le
    · exact hasDegreeBound_degree
    · exact le_trans h (totalDegree_le_DegreeBound hn)
  · intro h
    rw [← totalDegree_le_DegreeBound_iff]
    apply h
    exact hasDegreeBound_degree

lemma totalDegree_bound_add {a b : WithTop ℕ} (ha : HasDegreeBound a φ)
    (hb: HasDegreeBound b ψ) : HasDegreeBound (max a b) (φ + ψ) := by
  intro s hs
  have : coeff R s φ ≠ 0 ∨ coeff R s ψ ≠ 0 := by
    contrapose! hs
    simp only [map_add, hs, add_zero]
  rcases this with h | h
  · apply le_trans (ha s h) (le_max_left a b)
  · apply le_trans (hb s h) (le_max_right a b)

theorem totalDegree_add : (φ + ψ).totalDegree ≤ max φ.totalDegree ψ.totalDegree := by
  have : HasDegreeBound (max φ.totalDegree ψ.totalDegree) (φ + ψ) := by
    apply totalDegree_bound_add
    · exact hasDegreeBound_degree
    · exact hasDegreeBound_degree
  exact totalDegree_le_DegreeBound this

theorem totalDegree_mul : (φ * ψ).totalDegree ≤ φ.totalDegree + ψ.totalDegree := by
  rw [← totalDegree_le_DegreeBound_iff]
  intro s hs
  rw [coeff_mul] at hs
  have hf : HasDegreeBound φ.totalDegree φ := hasDegreeBound_degree
  have hg : HasDegreeBound ψ.totalDegree ψ := hasDegreeBound_degree
  simp only [HasDegreeBound_def, Nat.cast_finsupp_sum, id_eq] at hf
  simp only [HasDegreeBound_def, Nat.cast_finsupp_sum, id_eq] at hg
  have ⟨a, ⟨has, ha⟩⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
  have ha1 : (coeff R a.1 φ ≠ 0) := by
    contrapose! ha
    simp only [ha, zero_mul]
  have ha2 : (coeff R a.2 ψ ≠ 0) := by
    contrapose! ha
    simp only [ha, mul_zero]
  simp only [Finset.mem_antidiagonal] at has
  rw [← has, Finsupp.sum_add_index]
  · simp only [Nat.cast_add, Nat.cast_finsupp_sum, id_eq, ge_iff_le]
    gcongr
    · exact hf a.1 ha1
    · exact hg a.2 ha2
  · simp
  · simp
theorem totalDegree_smul_le (r : R) :
    (r • φ).totalDegree ≤ φ.totalDegree := by
  rw [totalDegreeBound_le]
  intro n hn
  simp only [HasDegreeBound_def, LinearMapClass.map_smul, smul_eq_mul, ne_eq, Nat.cast_finsupp_sum,
    id_eq]
  intro s hs
  simp only [HasDegreeBound_def, ne_eq, Nat.cast_finsupp_sum, id_eq] at hn
  apply hn s
  by_contra h
  simp only [h, mul_zero, not_true_eq_false] at hs

theorem totalDegree_pow (n : ℕ) : (φ ^ n).totalDegree ≤ n * φ.totalDegree := by
  induction' n with n ih
  · simp
  · apply le_trans totalDegree_mul
    simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, add_mul]
    gcongr
    · exact ih
    · simp

@[simp]
theorem totalDegree_monomial (s : σ →₀ ℕ) {r : R} (hr : r ≠ 0) :
    (monomial _ s r : MvPowerSeries σ R).totalDegree = s.sum fun _ ↦ id := by
  apply le_antisymm
  · rw [← totalDegree_le_DegreeBound_iff]
    intro t ht
    simp only [coeff_monomial, ne_eq, ite_eq_right_iff, hr, imp_false, not_not] at ht
    rw [ht]
  · apply le_totalDegree
    show coeff R s (monomial _ s r) ≠ 0
    simp [coeff_monomial, hr]

theorem totalDegree_monomial_le (s : σ →₀ ℕ) (r : R) :
    (monomial _ s r).totalDegree ≤ s.sum fun _ ↦ id := by
  by_cases hr : r = 0
  · simp [hr]
  · rw [totalDegree_monomial s hr]

@[simp]
theorem totalDegree_X_pow [Nontrivial R] (i : σ) (n : ℕ) :
    (X i ^ n : MvPowerSeries σ R).totalDegree = n := by
  rw [X_pow_eq, totalDegree_monomial]
  · simp
  · exact one_ne_zero

theorem totalDegree_add_eq_left_of_totalDegree_lt (h : ψ.totalDegree < φ.totalDegree) :
    (φ + ψ).totalDegree = φ.totalDegree := by
    have hmax : (φ + ψ).totalDegree ≤ max φ.totalDegree ψ.totalDegree := totalDegree_add
    have hmaxphi : max φ.totalDegree ψ.totalDegree = φ.totalDegree := by
      simp only [max_eq_left_iff]
      exact le_of_lt h
    rw [hmaxphi] at hmax
    apply le_antisymm hmax
    rw [totalDegreeBound_le]
    intro n hn s hs
    by_cases hs0 : (coeff R s) ψ = 0
    · apply hn s
      simp [hs, hs0]
    · have : ¬ HasDegreeBound ψ.totalDegree φ := by
        by_contra hphi
        apply totalDegree_le_DegreeBound at hphi
        exact lt_irrefl _ (lt_of_le_of_lt hphi h)
      simp only [HasDegreeBound_def, ne_eq, id_eq, not_forall, not_le,
        exists_prop] at this
      obtain ⟨t, hφ, hψ⟩ := this
      have coeff_ne_zero : coeff R t (φ + ψ) ≠ 0 := by
        have : coeff R t ψ = 0 := by
          by_contra h0
          apply le_totalDegree at h0
          exact lt_irrefl _ (lt_of_le_of_lt h0 hψ)
        simp [hφ, this]
      apply le_of_lt
      exact lt_of_lt_of_le (lt_of_le_of_lt (hasDegreeBound_degree s hs0) hψ) (hn t coeff_ne_zero)

theorem totalDegree_add_eq_right_of_totalDegree_lt (h : ψ.totalDegree < φ.totalDegree):
    (ψ + φ).totalDegree = φ.totalDegree := by
  rw [add_comm, totalDegree_add_eq_left_of_totalDegree_lt h]

end MvPowerSeries

end Degree
