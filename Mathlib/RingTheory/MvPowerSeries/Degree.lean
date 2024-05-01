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
  ∃ n, HasDegreeBound n φ

@[simp]
theorem HasBoundedDegree_def : HasBoundedDegree φ ↔ ∃ n, HasDegreeBound n φ := by rfl

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

lemma totalDegreeBound_le : φ.totalDegree ≤ ψ.totalDegree ↔ ∀ n, (HasDegreeBound n ψ → HasDegreeBound n φ) := by
  constructor
  · intro h n hn
    apply hasDegreeBound_of_le
    · exact hasDegreeBound_degree
    · exact le_trans h (totalDegree_le_DegreeBound hn)
  · intro h
    rw [← totalDegree_le_DegreeBound_iff]
    apply h
    exact hasDegreeBound_degree

theorem totalDegree_bound_add {a b : WithTop ℕ} (ha : HasDegreeBound a φ)
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
  simp only [Finset.mem_antidiagonal] at has
  rw [← has]
  sorry

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
  -- rw [Finset.pow_eq_prod_const, ← Nat.nsmul_eq_mul, Finset.nsmul_eq_sum_const]
  -- refine supDegree_prod_le rfl (fun _ _ => ?_)
  -- exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)
  sorry

@[simp]
theorem totalDegree_monomial (s : σ →₀ ℕ) {r : R} (hr : r ≠ 0) :
    (monomial _ s r : MvPowerSeries σ R).totalDegree = s.sum fun _ ↦ id := by
  --simp [degree, support_monomial, if_neg hr]
  sorry

theorem totalDegree_monomial_le (s : σ →₀ ℕ) (r : R) :
    (monomial _ s r).totalDegree ≤ s.sum fun _ ↦ id := by
  sorry
  -- if hr : r = 0 then
  --   simp only [hr, map_zero, degree_zero]
  -- else
  --   rw [degree_monomial _ hr]
  --   exact le_rfl

@[simp]
theorem totalDegree_X_pow [Nontrivial R] (i : σ) (n : ℕ) :
    (X i ^ n : MvPowerSeries σ R).totalDegree = n := by sorry --simp [X_pow_eq_monomial, one_ne_zero]

theorem totalDegree_add_eq_left_of_totalDegree_lt [CommRing R] (h : ψ.totalDegree < φ.totalDegree) :
    (φ + ψ).totalDegree = φ.totalDegree := by
  have h1 : φ = (φ + ψ) + (-ψ) := by simp only [add_neg_cancel_right]
    --nth_rw 1 [h1]
  have h2 : φ.totalDegree ≤ max (φ + ψ).totalDegree ψ.totalDegree := by sorry
  have h3 : max (φ + ψ).totalDegree ψ.totalDegree ≤ φ.totalDegree := by sorry
  have h4 : φ.totalDegree = max (φ + ψ).totalDegree ψ.totalDegree := by
    exact le_antisymm h2 h3
  have h5 : (φ + ψ).totalDegree = max (φ + ψ).totalDegree ψ.totalDegree := by
    by_cases hmax : max (φ + ψ).totalDegree ψ.totalDegree = ψ.totalDegree
    · rw [← h4] at hmax
      rw [hmax] at h
      exfalso
      apply lt_irrefl ψ.totalDegree
      exact h
    · simp at hmax
      rw [max_eq_left_of_lt hmax]
  rw [← h5] at h4
  symm
  exact h4

theorem totalDegree_add_eq_right_of_totalDegree_lt (h : ψ.totalDegree < φ.totalDegree) [CommRing R] :
    (ψ + φ).totalDegree = φ.totalDegree := by
  rw [add_comm, totalDegree_add_eq_left_of_totalDegree_lt h]

end MvPowerSeries

end Degree
