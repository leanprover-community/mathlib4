/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Data.Finsupp.WellFounded

/-! LexOrder of multivariate power series

Given an ordering of `σ` such that `WellOrderGT σ`,
the lexicographic order on `σ →₀ ℕ` is a well ordering,
which can be used to define a natural valuation `lexOrder` on the ring `MvPowerSeries σ R`:
the smallest exponent in the support.

-/

namespace MvPowerSeries

variable {σ R : Type*}
variable [Semiring R]

section LexOrder

open Finsupp
variable [LinearOrder σ] [WellFoundedGT σ]

/-- The lex order on multivariate power series. -/
noncomputable def lexOrder (φ : MvPowerSeries σ R) : (WithTop (Lex (σ →₀ ℕ))) := by
  classical
  exact if h : φ = 0 then ⊤ else by
    have ne : Set.Nonempty (toLex '' φ.support) := by
      simp only [Set.image_nonempty, Function.support_nonempty_iff, ne_eq, h, not_false_eq_true]
    apply WithTop.some
    apply WellFounded.min _ (toLex '' φ.support) ne
    · exact Finsupp.instLTLex.lt
    · exact wellFounded_lt

theorem lexOrder_def_of_ne_zero {φ : MvPowerSeries σ R} (hφ : φ ≠ 0) :
    ∃ (ne : Set.Nonempty (toLex '' φ.support)),
      lexOrder φ = WithTop.some ((@wellFounded_lt (Lex (σ →₀ ℕ))
        (instLTLex) (Lex.wellFoundedLT)).min (toLex '' φ.support) ne) := by
  suffices ne : Set.Nonempty (toLex '' φ.support) by
    use ne
    unfold lexOrder
    simp only [dif_neg hφ]
  simp only [Set.image_nonempty, Function.support_nonempty_iff, ne_eq, hφ, not_false_eq_true]

@[simp]
theorem lexOrder_eq_top_iff_eq_zero (φ : MvPowerSeries σ R) :
    lexOrder φ = ⊤ ↔ φ = 0 := by
  unfold lexOrder
  split_ifs with h
  · simp only [h]
  · simp only [h, WithTop.coe_ne_top]

theorem lexOrder_zero : lexOrder (0 : MvPowerSeries σ R) = ⊤ := by
  unfold lexOrder
  rw [dif_pos rfl]

theorem exists_finsupp_eq_lexOrder_of_ne_zero {φ : MvPowerSeries σ R} (hφ : φ ≠ 0) :
    ∃ (d : σ →₀ ℕ), lexOrder φ = toLex d := by
  simp only [ne_eq, ← lexOrder_eq_top_iff_eq_zero, WithTop.ne_top_iff_exists] at hφ
  obtain ⟨p, hp⟩ := hφ
  exact ⟨ofLex p, by simp only [toLex_ofLex, hp]⟩

theorem coeff_ne_zero_of_lexOrder {φ : MvPowerSeries σ R} {d : σ →₀ ℕ}
    (h : toLex d = lexOrder φ) : coeff R d φ ≠ 0 := by
  have hφ : φ ≠ 0 := by
    simp only [ne_eq, ← lexOrder_eq_top_iff_eq_zero, ← h, WithTop.coe_ne_top, not_false_eq_true]
  have hφ' := lexOrder_def_of_ne_zero hφ
  rcases hφ' with ⟨ne, hφ'⟩
  simp only [← h, WithTop.coe_eq_coe] at hφ'
  suffices toLex d ∈ toLex '' φ.support by
    simp only [Set.mem_image_equiv, toLex_symm_eq, ofLex_toLex, Function.mem_support, ne_eq] at this
    apply this
  rw [hφ']
  apply WellFounded.min_mem

theorem coeff_eq_zero_of_lt_lexOrder {φ : MvPowerSeries σ R} {d : σ →₀ ℕ}
    (h : toLex d < lexOrder φ) : coeff R d φ = 0 := by
  by_cases hφ : φ = 0
  · simp only [hφ, map_zero]
  · rcases lexOrder_def_of_ne_zero hφ with ⟨ne, hφ'⟩
    rw [hφ', WithTop.coe_lt_coe] at h
    by_contra h'
    exact WellFounded.not_lt_min _ (toLex '' φ.support) ne (Set.mem_image_equiv.mpr h') h

theorem lexOrder_le_of_coeff_ne_zero {φ : MvPowerSeries σ R} {d : σ →₀ ℕ}
    (h : coeff R d φ ≠ 0) : lexOrder φ ≤ toLex d := by
  rw [← not_lt]
  intro h'
  exact h (coeff_eq_zero_of_lt_lexOrder h')

theorem le_lexOrder_iff {φ : MvPowerSeries σ R} {w : WithTop (Lex (σ →₀ ℕ))} :
    w ≤ lexOrder φ ↔ (∀ (d : σ →₀ ℕ) (_ : toLex d < w), coeff R d φ = 0) := by
  constructor
  · intro h d hd
    apply coeff_eq_zero_of_lt_lexOrder
    exact lt_of_lt_of_le hd h
  · intro h
    rw [← not_lt]
    intro h'
    have hφ : φ ≠ 0 := by
      rw [ne_eq, ← lexOrder_eq_top_iff_eq_zero]
      exact ne_top_of_lt h'
    obtain ⟨d, hd⟩ := exists_finsupp_eq_lexOrder_of_ne_zero hφ
    refine coeff_ne_zero_of_lexOrder hd.symm (h d ?_)
    rwa [← hd]

theorem min_lexOrder_le {φ ψ : MvPowerSeries σ R} :
    min (lexOrder φ) (lexOrder ψ) ≤ lexOrder (φ + ψ)  := by
  rw [le_lexOrder_iff]
  intro d hd
  simp only [lt_min_iff] at hd
  rw [map_add, coeff_eq_zero_of_lt_lexOrder hd.1, coeff_eq_zero_of_lt_lexOrder hd.2, add_zero]

theorem coeff_mul_of_add_lexOrder {φ ψ : MvPowerSeries σ R}
    {p q : σ →₀ ℕ} (hp : lexOrder φ = toLex p) (hq : lexOrder ψ = toLex q) :
    coeff R (p + q) (φ * ψ) = coeff R p φ * coeff R q ψ := by
  rw [coeff_mul, Finset.sum_eq_single_of_mem ⟨p, q⟩ (by simp)]
  rintro ⟨u, v⟩ h h'
  simp only [Finset.mem_antidiagonal] at h
  rcases trichotomy_of_add_eq_add (congrArg toLex h) with h'' | h'' | h''
  · exact False.elim (h' (by simp [Prod.ext_iff, h''.1, h''.2]))
  · rw [coeff_eq_zero_of_lt_lexOrder (d := u), zero_mul]
    rw [hp]
    norm_cast
  · rw [coeff_eq_zero_of_lt_lexOrder (d := v), mul_zero]
    rw [hq]
    norm_cast

theorem le_lexOrder_mul (φ ψ : MvPowerSeries σ R) :
    lexOrder φ + lexOrder ψ ≤ lexOrder (φ * ψ) := by
  rw [le_lexOrder_iff]
  intro d hd
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨u, v⟩ h
  simp only [Finset.mem_antidiagonal] at h
  simp only
  suffices toLex u < lexOrder φ ∨ toLex v < lexOrder ψ by
    rcases this with (hu | hv)
    · rw [coeff_eq_zero_of_lt_lexOrder hu, zero_mul]
    · rw [coeff_eq_zero_of_lt_lexOrder hv, mul_zero]
  rw [or_iff_not_imp_left, not_lt, ← not_le]
  intro hu hv
  rw [← not_le] at hd
  apply hd
  simp only [← h, toLex_add, WithTop.coe_add, add_le_add hu hv]

alias lexOrder_mul_ge := le_lexOrder_mul

theorem lexOrder_mul [NoZeroDivisors R] (φ ψ : MvPowerSeries σ R) :
    lexOrder (φ * ψ) = lexOrder φ + lexOrder ψ := by
  by_cases hφ : φ = 0
  · simp only [hφ, zero_mul, lexOrder_zero, top_add]
  by_cases hψ : ψ = 0
  · simp only [hψ, mul_zero, lexOrder_zero, add_top]
  rcases exists_finsupp_eq_lexOrder_of_ne_zero hφ with ⟨p, hp⟩
  rcases exists_finsupp_eq_lexOrder_of_ne_zero hψ with ⟨q, hq⟩
  apply le_antisymm _ (lexOrder_mul_ge φ ψ)
  rw [hp, hq]
  apply lexOrder_le_of_coeff_ne_zero (d := p + q)
  rw [coeff_mul_of_add_lexOrder hp hq, mul_ne_zero_iff]
  exact ⟨coeff_ne_zero_of_lexOrder hp.symm, coeff_ne_zero_of_lexOrder hq.symm⟩

end LexOrder

end MvPowerSeries
