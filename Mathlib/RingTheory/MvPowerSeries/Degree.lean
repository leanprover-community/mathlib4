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

/-- A `MvPowerSeries φ` has bounded degree if its monomials are uniformly bounded -/
def HasDegreeBound (n : WithBot (WithTop ℕ)) : MvPowerSeries σ R → Prop :=
  fun φ ↦ (∀ s : σ →₀ ℕ, coeff R s φ ≠ 0 → s.sum (fun _ ↦ id) ≤ n)

/-- A `MvPowerSeries φ` has bounded degree if its monomials are uniformly bounded -/
def HasBoundedDegree (φ : MvPowerSeries σ R) : Prop :=
  ∃ n, HasDegreeBound n φ

noncomputable def degree (φ : MvPowerSeries σ R) : WithBot (WithTop ℕ) :=
  sInf { n | HasDegreeBound n φ }

theorem le_degree {s : σ →₀ ℕ} (h : φ s ≠ 0) : (s.sum fun _ ↦ id) ≤ degree φ := by
  sorry

theorem totalDegree_le_of_support_subset (h : ∀ s, φ s ≠ 0 → ψ s ≠ 0) :
    degree φ ≤ degree ψ :=
  sorry

@[simp]
theorem degree_zero : (0 : MvPowerSeries σ R).degree = ⊥ := by sorry

@[simp]
theorem degree_C (r : R) : (C σ R r : MvPowerSeries σ R).degree = 0 := by sorry

@[simp]
theorem degree_one : (1 : MvPowerSeries σ R).degree = 0 :=
  degree_C (1 : R)

@[simp]
theorem degree_X [Nontrivial R] (s : σ) : (X s : MvPowerSeries σ R).degree = 1 := by
  -- rw [degree, support_X]
  -- simp only [Finset.sup, Finsupp.sum_single_index, Finset.fold_singleton, sup_bot_eq]
  sorry

theorem degree_add : (φ + ψ).degree ≤ max φ.degree ψ.degree := by
  sorry

theorem degree_add_eq_left_of_degree_lt (h : ψ.degree < φ.degree) :
    (φ + ψ).degree = φ.degree := by
  -- classical
  --   apply le_antisymm
  --   · rw [← max_eq_left_of_lt h]
  --     exact totalDegree_add p q
  --   by_cases hp : p = 0
  --   · simp [hp]
  --   obtain ⟨b, hb₁, hb₂⟩ :=
  --     p.support.exists_mem_eq_sup (Finsupp.support_nonempty_iff.mpr hp) fun m : σ →₀ ℕ =>
  --       Multiset.card (toMultiset m)
  --   have hb : ¬b ∈ q.support := by
  --     contrapose! h
  --     rw [totalDegree_eq p, hb₂, totalDegree_eq]
  --     apply Finset.le_sup h
  --   have hbb : b ∈ (p + q).support := by
  --     apply support_sdiff_support_subset_support_add
  --     rw [Finset.mem_sdiff]
  --     exact ⟨hb₁, hb⟩
  --   rw [totalDegree_eq, hb₂, totalDegree_eq]
  --   exact Finset.le_sup (f := fun m => Multiset.card (Finsupp.toMultiset m)) hbb
  sorry

theorem degree_add_eq_right_of_degree_lt (h : ψ.degree < φ.degree) :
    (ψ + φ).degree = φ.degree := by
  rw [add_comm, degree_add_eq_left_of_degree_lt h]

theorem degree_mul : (φ * ψ).degree ≤ φ.degree + ψ.degree := by
  sorry


theorem degree_smul_le [CommSemiring S] [DistribMulAction R S] (r : R) :
    (r • φ).degree ≤ φ.degree := sorry

theorem degree_pow (n : ℕ) : (φ ^ n).degree ≤ n * φ.degree := by
  -- rw [Finset.pow_eq_prod_const, ← Nat.nsmul_eq_mul, Finset.nsmul_eq_sum_const]
  -- refine supDegree_prod_le rfl (fun _ _ => ?_)
  -- exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)
  sorry

@[simp]
theorem degree_monomial (s : σ →₀ ℕ) {r : R} (hr : r ≠ 0) :
    (monomial _ s r : MvPowerSeries σ R).degree = s.sum fun _ ↦ id := by
  --simp [degree, support_monomial, if_neg hr]
  sorry

theorem degree_monomial_le (s : σ →₀ ℕ) (r : R) :
    (monomial s r).degree ≤ s.sum fun _ ↦ id := by
  if hr : r = 0 then
    simp only [hr, map_zero, degree_zero]
  else
    rw [degree_monomial _ hr]
    exact le_rfl
  sorry

@[simp]
theorem degree_X_pow [Nontrivial R] (i : σ) (n : ℕ) :
    (X i ^ n : MvPowerSeries σ R).degree = n := by simp [X_pow_eq_monomial, one_ne_zero]

end MvPowerSeries

end Degree
