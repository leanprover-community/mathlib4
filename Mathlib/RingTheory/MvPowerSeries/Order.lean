/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.RingTheory.MvPowerSeries.Basic

/-! Valuation on rings of formal power series -/

noncomputable section

namespace MvPowerSeries

variable {σ R : Type*} [Semiring R]

theorem exists_coeff_ne_zero_iff_ne_zero (φ : MvPowerSeries σ R):
    (∃ n : ℕ, ∃ d, coeff R d φ ≠ 0 ∧ n = d.sum (fun _ s ↦ s)) ↔ φ ≠ 0 := by
  refine not_iff_not.mp ?_
  push_neg
  simp only [ne_eq, ext_iff, map_zero, not_imp_not]
  constructor
  · exact fun h d ↦ h (d.sum fun _ i ↦ i) d rfl
  · exact fun h n d _ ↦ h d

section Order

example (p q : σ → Prop) (h : ∀ s, p s ↔ q s) : (∀ s, p s) ↔ (∀ s, q s) := by
  exact forall_congr' h

/-- The order of a formal power series `φ` is the greatest `n : PartENat`
such that `monomial d 1` divides `φ`, for some `d : σ →₀ ℕ` with total sum `n`.
  The order is `⊤` if and only if `φ = 0`. -/
def order (φ : MvPowerSeries σ R) : PartENat := by
  classical
  exact if h : φ = 0 then ⊤ else Nat.find (φ.exists_coeff_ne_zero_iff_ne_zero.mpr h)

open Classical in
theorem order_def (φ : MvPowerSeries σ R) :
    order φ  = if h : φ = 0 then (⊤ : PartENat)
    else Nat.find (φ.exists_coeff_ne_zero_iff_ne_zero.mpr h) := by
  unfold order
  by_cases h : φ = 0
  · simp only [dif_pos h]
  · simp only [dif_neg h]

theorem order_zero : order (0 : MvPowerSeries σ R) = ⊤ := by
  rw [order_def, dif_pos rfl]

theorem order_eq_top_iff (φ : MvPowerSeries σ R) :
    order φ = ⊤ ↔ φ = 0 := by
  classical
  simp only [order_def, ne_eq, dite_eq_left_iff, PartENat.natCast_ne_top,
    imp_false, Decidable.not_not]

theorem order_finite_iff_ne_zero (φ : MvPowerSeries σ R) :
    (order φ).Dom ↔ φ ≠ 0 := by
  simp only [ne_eq, ← order_eq_top_iff, PartENat.ne_top_iff_dom]

theorem nat_lt_order_iff {φ : MvPowerSeries σ R} {n : ℕ} :
    n < order φ ↔ ∀ d, (d.sum fun _ i ↦ i) ≤ n → coeff R d φ = 0 := by
  classical
  by_cases h : φ = 0
  · simp [h, order_zero]
  simp only [order_def, ne_eq, dif_neg h, Nat.cast_lt, Nat.lt_find_iff, not_exists, not_and, not_imp_not]
  constructor
  · exact fun hn d hd ↦ hn (d.sum fun _ s ↦ s) hd d (by rfl)
  · exact fun h m hm d h' ↦ h d (Eq.symm (Eq.symm h') ▸ hm)

theorem coeff_eq_zero_of_lt_order {φ : MvPowerSeries σ R} {d : σ →₀ ℕ}
    (hd : d.sum (fun _ i ↦ i) < order φ) : coeff R d φ = 0 := by
  rw [nat_lt_order_iff] at hd
  exact hd d (le_refl _)

theorem order_le_nat_iff {φ : MvPowerSeries σ R} {n : ℕ} :
    φ.order ≤ n ↔ ∃ d, (d.sum fun _ i ↦ i) ≤ n ∧ coeff R d φ ≠ 0 := by
  simp only [← not_lt, not_iff_comm, nat_lt_order_iff, ne_eq, not_exists, not_and, not_not]

theorem nat_le_order_iff {φ : MvPowerSeries σ R} {n : ℕ} :
    n ≤ order φ ↔ ∀ d, (d.sum fun _ i ↦ i) < n → coeff R d φ = 0 := by
  classical
  by_cases h : φ = 0
  · simp [h, order_zero]
  simp only [order_def, ne_eq, dif_neg h, Nat.cast_le, Nat.le_find_iff, not_exists, not_and,
    not_imp_not]
  constructor
  · exact fun hn d hd ↦ hn _ hd d (by rfl)
  · exact fun h m hm d h' ↦ h d (Eq.symm (Eq.symm h') ▸ hm)

theorem le_order_iff {φ : MvPowerSeries σ R} {n : PartENat} :
    n ≤ order φ ↔ ∀ d, (d.sum fun _ i ↦ i : ℕ) < n → coeff R d φ = 0 := by
  classical
  induction' n using PartENat.casesOn with n
  · simp [order_eq_top_iff]
    rw [ext_iff]
    apply forall_congr'
    simp only [map_zero, implies_true]
  · simp only [nat_le_order_iff, Nat.cast_lt]

theorem order_lt_nat_iff {φ : MvPowerSeries σ R} {n : ℕ} :
    φ.order < n ↔ ∃ d, (d.sum fun _ i ↦ i) < n ∧ coeff R d φ ≠ 0 := by
  rw [← not_le, not_iff_comm, nat_le_order_iff]
  simp only [ne_eq, not_exists, not_and, not_not]

theorem order_lt_iff {φ : MvPowerSeries σ R} {n : PartENat} :
    φ.order < n ↔ ∃ d, (d.sum fun _ i ↦ i) < n ∧ coeff R d φ ≠ 0 := by
  rw [← not_le, not_iff_comm, le_order_iff]
  simp only [ne_eq, not_exists, not_and, not_not, Finsupp.sum, Nat.cast_sum]

theorem order_le_nat {φ : MvPowerSeries σ R} {n : ℕ} {d : σ →₀ ℕ}
    (hn : n = d.sum fun _ i ↦ i) (h : coeff R d φ ≠ 0) :
    order φ ≤ n := by
  rw [← not_lt, nat_lt_order_iff, hn]
  exact fun h' ↦ h (h' d (le_refl _))

theorem order_monomial [DecidableEq R] (d : σ →₀ ℕ) (a : R) :
    order (monomial R d a) = if a = 0 then (⊤ : PartENat) else d.sum (fun _ i ↦ i) := by
  by_cases h : a = 0
  · rw [if_pos h, h, map_zero, order_zero]
  · rw [if_neg h]
    apply le_antisymm
    · simp only [Finsupp.sum, ← Nat.cast_sum]
      rw [order_le_nat_iff]
      use d
      simp only [coeff_monomial_same, ne_eq, h, not_false_eq_true, and_true, Finsupp.sum, le_refl]
    · simp only [le_order_iff]
      intro e he
      rw [coeff_monomial_ne]
      intro he'
      apply ne_of_lt he
      simp only [Finsupp.sum, he', Nat.cast_sum]

theorem le_order_add (φ ψ : MvPowerSeries σ R) :
    min (order φ) (order ψ) ≤ order (φ + ψ) := by
  by_cases h : (φ + ψ) = 0
  · simp only [h, order_zero, le_top]
  simp only [← order_finite_iff_ne_zero, ne_eq] at h
  set n := (φ + ψ).order.get h
  have hn : n = (φ + ψ).order := PartENat.natCast_get h
  rw [← hn, min_le_iff]
  obtain ⟨d, hd, h⟩ := order_le_nat_iff.mp (le_of_eq hn.symm)
  rw [or_iff_not_imp_left, not_le, nat_lt_order_iff]
  intro h'
  rw [order_le_nat_iff]
  use d, hd
  simpa only [map_add, h' d hd, ne_eq, zero_add] using h

theorem order_add_of_order_lt_eq_left {φ ψ : MvPowerSeries σ R} (h : order φ < order ψ) :
    order (φ + ψ) = order φ := by
  have : (order φ).Dom := PartENat.dom_of_lt h
  let n := (order φ).get this
  have hn : φ.order = n := ((order φ).natCast_get this).symm
  rw [hn]
  obtain ⟨d, hd, hd'⟩ := order_le_nat_iff.mp (le_of_eq hn)
  apply le_antisymm
  · rw [order_le_nat_iff]
    use d, hd
    suffices coeff R d ψ = 0 by
      rw [map_add, this, add_zero]
      exact hd'
    apply coeff_eq_zero_of_lt_order
    apply lt_of_le_of_lt _ h
    simp only [hn, Nat.cast_le, hd]
  simp only [nat_le_order_iff]
  intro e he
  simp only [map_add]
  suffices e.sum (fun _ i ↦ i) < φ.order by
    convert add_zero _
    · apply coeff_eq_zero_of_lt_order (lt_trans this h)
    · rw [eq_comm]
      apply coeff_eq_zero_of_lt_order this
  simp only [hn, Nat.cast_lt, he]

theorem order_add_of_order_lt_eq_right {φ ψ : MvPowerSeries σ R} (h : order ψ < order φ) :
    order (φ + ψ) = order ψ := by
  rw [add_comm]
  exact order_add_of_order_lt_eq_left h

/-- The order of the sum of two formal power series
 is the minimum of their orders if their orders differ. -/
theorem order_add_of_order_eq (φ ψ : MvPowerSeries σ R) (h : order φ ≠ order ψ) :
    order (φ + ψ) = order φ ⊓ order ψ := by
  refine le_antisymm ?_ (le_order_add _ _)
  by_cases H₁ : order φ < order ψ
  · rw [order_add_of_order_lt_eq_left H₁]
    apply le_of_eq
    simp only [left_eq_inf, le_of_lt H₁]
  by_cases H₂ : order ψ < order φ
  · rw [order_add_of_order_lt_eq_right H₂]
    apply le_of_eq
    simp only [right_eq_inf, le_of_lt H₂]
  exfalso; exact h (le_antisymm (not_lt.1 H₂) (not_lt.1 H₁))

/-- The order of the product of two formal power series
 is at least the sum of their orders. -/
theorem order_mul_ge (φ ψ : MvPowerSeries σ R) :
    order φ + order ψ ≤ order (φ * ψ) := by
  classical
  rw [le_order_iff]
  intro d hd
  rw [coeff_mul, Finset.sum_eq_zero]
  rintro ⟨p, q⟩ hpq
  simp only
  by_cases hp : p.sum (fun _ i ↦ i) < order φ
  · rw [coeff_eq_zero_of_lt_order hp, zero_mul]
  by_cases hq : q.sum (fun _ i ↦ i) < order ψ
  · rw [coeff_eq_zero_of_lt_order hq, mul_zero]
  exfalso
  rw [not_lt] at hp hq
  apply not_le.mpr hd
  simp only [Finset.mem_antidiagonal] at hpq
  rw [← hpq, Finsupp.sum_add_index, Nat.cast_add]
  exact add_le_add hp hq
  exact fun _ _ ↦ rfl
  exact fun _ _ _ _ ↦ rfl

end Order

section natOrder

/-- The natOrder of a nonzero formal power series `φ` is the greatest `n : ℕ`
such that `monomial d 1` divides `φ`, for some `d : σ →₀ ℕ` with total sum `n`.
  The order is `0` is `0`. -/
def natOrder (φ : MvPowerSeries σ R) : Nat := by
  classical
  exact if h : φ = 0 then 0 else Nat.find (φ.exists_coeff_ne_zero_iff_ne_zero.mpr h)


end natOrder
