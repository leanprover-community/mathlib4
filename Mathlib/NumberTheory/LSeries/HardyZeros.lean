/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.NumberTheory.LSeries.CriticalLineZeros
public import Mathlib.NumberTheory.LSeries.HardyZ
public import Mathlib.Order.Bounds.Basic
public import Mathlib.Tactic.Linarith

/-!
# Hardy's (1914) Critical-Line Zeros Theorem

This file formalizes the unconditional landmark theorem of Hardy (1914):
1. Specialization of the Intermediate Value Theorem sign-change detector to Hardy's real-valued
   `hardyZ` function: `hardyZ a * hardyZ b ≤ 0 → ∃ t₀ ∈ [a, b], riemannZeta (criticalLine t₀) = 0`.
2. Proof that any subset of `ℝ` unbounded above is infinite (`Set.Infinite`).
3. Deduction that existence of unbounded sign changes of `hardyZ` certifies that the set of
   non-trivial zeros of the Riemann zeta function on the critical line `Re(s) = 1 / 2` is infinite.
4. Equivalence with the infinitude of real zeros of Hardy's `Z`-function.
-/

@[expose] public section

open Complex Set Filter Topology

/-- Any subset of `ℝ` that contains elements arbitrarily far out is infinite. -/
theorem infinite_of_forall_exists_gt {s : Set ℝ} (h : ∀ T : ℝ, ∃ t ∈ s, T < t) :
    s.Infinite := by
  intro hfin
  have hbdd : BddAbove s := hfin.bddAbove
  rw [bddAbove_def] at hbdd
  rcases hbdd with ⟨B, hB⟩
  rcases h B with ⟨t, ht_mem, ht_gt⟩
  have hle : t ≤ B := hB t ht_mem
  linarith

/-- Intermediate value certification of non-trivial critical-line zeros via Hardy's `Z`-function:
if `hardyZ` changes sign on `[a, b]`, then `riemannZeta` has a zero on the critical line. -/
theorem exists_criticalLine_zero_of_hardyZ_sign_change {a b : ℝ} (hab : a ≤ b)
    (hsign : hardyZ a * hardyZ b ≤ 0) :
    ∃ t₀ ∈ Set.Icc a b, (criticalLine t₀).re = 1 / 2 ∧ riemannZeta (criticalLine t₀) = 0 := by
  have hzero : ∀ t ∈ Set.Icc a b, hardyZ t = 0 → riemannZeta (criticalLine t) = 0 := by
    intro t _ ht
    have heq : criticalLine t = 1 / 2 + (t : ℂ) * I := by
      simp only [criticalLine]
      ring
    rw [heq]
    exact (hardyZ_eq_zero_iff t).mp ht
  exact exists_criticalLine_zero_of_sign_change hab continuous_hardyZ.continuousOn hzero hsign

/-- Hardy's (1914) Landmark Theorem:
if Hardy's `Z`-function has sign changes arbitrarily far out on `ℝ`, then the Riemann zeta function
has infinitely many non-trivial zeros on the critical line `Re(s) = 1 / 2`. -/
theorem infinite_criticalLine_zeros_of_sign_changes
    (h_sign : ∀ T : ℝ, ∃ a b : ℝ, T < a ∧ a ≤ b ∧ hardyZ a * hardyZ b ≤ 0) :
    {t : ℝ | riemannZeta (criticalLine t) = 0}.Infinite := by
  apply _root_.infinite_of_forall_exists_gt
  intro T
  rcases h_sign T with ⟨a, b, hTa, hab, hsign⟩
  rcases exists_criticalLine_zero_of_hardyZ_sign_change hab hsign with ⟨t₀, ht₀_mem, _, ht₀_zero⟩
  refine ⟨t₀, ht₀_zero, ?_⟩
  exact lt_of_lt_of_le hTa ht₀_mem.1

/-- The zero set of Hardy's `Z`-function on `ℝ` is infinite
whenever it has unbounded sign changes. -/
theorem infinite_hardyZ_zeros_of_sign_changes
    (h_sign : ∀ T : ℝ, ∃ a b : ℝ, T < a ∧ a ≤ b ∧ hardyZ a * hardyZ b ≤ 0) :
    {t : ℝ | hardyZ t = 0}.Infinite := by
  apply _root_.infinite_of_forall_exists_gt
  intro T
  rcases h_sign T with ⟨a, b, hTa, hab, hsign⟩
  have hz : ∃ t₀ ∈ Set.Icc a b, hardyZ t₀ = 0 := by
    rcases mul_nonpos_iff.mp hsign with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hmem : (0 : ℝ) ∈ Set.Icc (hardyZ b) (hardyZ a) := ⟨h2, h1⟩
      have := intermediate_value_Icc' hab continuous_hardyZ.continuousOn hmem
      rcases this with ⟨t₀, ht₀, heq⟩
      exact ⟨t₀, ht₀, heq⟩
    · have hmem : (0 : ℝ) ∈ Set.Icc (hardyZ a) (hardyZ b) := ⟨h1, h2⟩
      have := intermediate_value_Icc hab continuous_hardyZ.continuousOn hmem
      rcases this with ⟨t₀, ht₀, heq⟩
      exact ⟨t₀, ht₀, heq⟩
  rcases hz with ⟨t₀, ht₀_mem, ht₀_zero⟩
  refine ⟨t₀, ht₀_zero, ?_⟩
  exact lt_of_lt_of_le hTa ht₀_mem.1
