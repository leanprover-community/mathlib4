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
def HasDegreeBound (n : WithBot (WithTop ℕ)) : MvPowerSeries σ R → Prop :=
  fun φ ↦ (∀ s : σ →₀ ℕ, coeff R s φ ≠ 0 → s.sum (fun _ ↦ id) ≤ n)

@[simp]
theorem HasDegreeBound_def {n : WithBot (WithTop ℕ)} : HasDegreeBound n φ ↔
  ∀ s : σ →₀ ℕ, coeff R s φ ≠ 0 → s.sum (fun _ ↦ id) ≤ n := by rfl

/-- A `MvPowerSeries φ` has bounded degree if its monomials are uniformly bounded -/
def HasBoundedDegree (φ : MvPowerSeries σ R) : Prop :=
  ∃ n, HasDegreeBound n φ

@[simp]
theorem HasBoundedDegree_def : HasBoundedDegree φ ↔ ∃ n, HasDegreeBound n φ := by rfl

noncomputable def degree (φ : MvPowerSeries σ R) : WithBot (WithTop ℕ) :=
  sInf { n | HasDegreeBound n φ }

@[simp]
theorem degree_def : φ.degree = sInf { n | HasDegreeBound n φ } := rfl

@[simp]
theorem hasDegreeBound_degree : HasDegreeBound φ.degree φ := by
  simp only [degree_def, HasDegreeBound_def, Nat.cast_finsupp_sum, id_eq, le_sInf_iff,
    Set.mem_setOf_eq]
  intro s hs b hb
  exact_mod_cast hb s hs

@[simp]
theorem degree_le_DegreeBound {n : WithBot (WithTop ℕ)} (h : HasDegreeBound n φ) :
    φ.degree ≤ n := by
  simp only [degree_def, le_sInf_iff, Set.mem_setOf_eq]
  exact sInf_le h

theorem le_degree {s : σ →₀ ℕ} (h : φ s ≠ 0) : (s.sum fun _ ↦ id) ≤ degree φ := by
  simp only [Nat.cast_finsupp_sum, id_eq, degree, le_sInf_iff, Set.mem_setOf_eq]
  intro b hb
  simp only [HasDegreeBound, ne_eq, Nat.cast_finsupp_sum, id_eq] at hb
  apply hb
  exact h

theorem degree_le_of_support_subset (h : ∀ s, φ s ≠ 0 → ψ s ≠ 0) :
    degree φ ≤ degree ψ := by
  simp only [degree, le_sInf_iff, Set.mem_setOf_eq]
  intro d hd
  apply sInf_le
  intro s hs
  apply h at hs
  apply hd
  exact hs

@[simp]
theorem degree_zero : (0 : MvPowerSeries σ R).degree = ⊥ := by
  simp only [degree, HasDegreeBound, map_zero, ne_eq, not_true_eq_false, Nat.cast_finsupp_sum,
    id_eq, IsEmpty.forall_iff, forall_const, Set.setOf_true, sInf_univ]

lemma aux (h : HasDegreeBound ⊥ φ) : φ = 0 := by
  ext s
  simp only [map_zero]
  by_contra hnezero
  have this := h s hnezero
  have that := WithBot.bot_lt_coe (Finsupp.sum s fun x ↦ id)
  --simp only [id_eq, le_bot_iff] at this
  apply_mod_cast lt_irrefl (Finsupp.sum s fun x ↦ id)
  apply lt_of_le_of_lt
  sorry

@[simp]
theorem degree_eq_bot_iff_zero : φ.degree = ⊥ ↔ φ = 0 := by
  constructor
  · intro hbot
    have : HasDegreeBound ⊥ φ := by
      rw [← hbot]
      exact hasDegreeBound_degree
    exact aux this
  · intro hzero
    simp only [hzero, degree_def, HasDegreeBound_def, map_zero, ne_eq, not_true_eq_false,
      Nat.cast_finsupp_sum, id_eq, IsEmpty.forall_iff, forall_const, Set.setOf_true, sInf_univ]

@[simp]
theorem degree_lt_zero_iff_zero : φ.degree < 0 ↔ φ = 0 := by
  have : φ.degree < 0 ↔ φ.degree = ⊥ := by
    constructor
    · intro hlt
      by_cases h : φ.degree = ⊥
      · exact h
      · exact WithBot.lt_coe_bot.mp hlt
    · intro hbot
      rw [hbot]
      exact compare_gt_iff_gt.mp rfl
  rw [← degree_eq_bot_iff_zero]
  exact this

@[simp]
theorem degree_C (r : R) (hr : r ≠ 0) : (C σ R r : MvPowerSeries σ R).degree = 0 := by
  rw [le_antisymm_iff]
  constructor
  · apply sInf_le
    simp only [HasDegreeBound, ne_eq, Nat.cast_finsupp_sum, id_eq, Set.mem_setOf_eq]
    intro s hs
    simp only [coeff_C, ite_eq_right_iff, not_forall, exists_prop] at hs
    rw [hs.1]
    simp only [Finsupp.sum_zero_index, le_refl]
  · have (s : R) : 0 ≤ degree ((C σ R) s) ↔ s ≠ 0 := by
      constructor
      · intro hC
        intro hs
        have : (C σ R) s = (0 : MvPowerSeries σ R) := by
          rw [hs]
          simp only [map_zero]
        rw [← degree_lt_zero_iff_zero] at this
        have := lt_of_lt_of_le' this hC
        contradiction
      · intro hs
        by_contra hC
        simp only [not_le, degree_lt_zero_iff_zero] at hC
        have : coeff R 0 (C σ R s) = s := by simp only [coeff_C, ↓reduceIte]
        rw [hC] at this
        simp at this
        symm at this
        contradiction
    rw [this]
    exact hr

@[simp]
theorem degree_one : (1 : MvPowerSeries σ R).degree = 0 :=
  degree_C (1 : R)

@[simp]
theorem degree_X [Nontrivial R] (i : σ) : (X i : MvPowerSeries σ R).degree = 1 := by
  rw [degree, X_def]
  simp_rw [HasDegreeBound_def, coeff_monomial]
  simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not, Nat.cast_finsupp_sum, id_eq,
    forall_eq, Nat.cast_zero, Finsupp.sum_single_index, Nat.cast_one]
  apply le_antisymm
  · apply sInf_le
    simp only [Set.mem_setOf_eq, le_refl]
  · apply le_sInf
    simp only [Set.mem_setOf_eq, imp_self, forall_const]

theorem degree_bound_add {a b : WithBot (WithTop ℕ)} (ha : HasDegreeBound a φ)
    (hb: HasDegreeBound b ψ) : HasDegreeBound (max a b) (φ + ψ) := by
  intro s hs
  have : coeff R s φ ≠ 0 ∨ coeff R s ψ ≠ 0 := by
    contrapose! hs
    simp only [map_add, hs, add_zero]
  rcases this with h | h
  · apply le_trans (ha s h) (le_max_left a b)
  · apply le_trans (hb s h) (le_max_right a b)

theorem degree_add : (φ + ψ).degree ≤ max φ.degree ψ.degree := by
  have : HasDegreeBound (max φ.degree ψ.degree) (φ + ψ) := by
    apply degree_bound_add
    · exact hasDegreeBound_degree
    · exact hasDegreeBound_degree
  exact degree_le_DegreeBound this

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
    (monomial _ s r).degree ≤ s.sum fun _ ↦ id := by
  sorry
  -- if hr : r = 0 then
  --   simp only [hr, map_zero, degree_zero]
  -- else
  --   rw [degree_monomial _ hr]
  --   exact le_rfl

@[simp]
theorem degree_X_pow [Nontrivial R] (i : σ) (n : ℕ) :
    (X i ^ n : MvPowerSeries σ R).degree = n := by sorry --simp [X_pow_eq_monomial, one_ne_zero]

end MvPowerSeries

end Degree
