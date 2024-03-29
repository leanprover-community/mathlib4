/-
Copyright (c) 2024 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Anne Baanen
-/
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # A lemma from the classification of wallpaper groups -/

open Lean.Parser.Tactic in
/-- The tactic `cancel_nat_inv` cancels inverses and simplifies casts. -/
macro "cancel_nat_inv" loc:(location)? : tactic =>
  `(tactic|
  ( simp (disch := positivity) only [inv_inj, inv_le_inv, inv_lt_inv] $[$loc]?
    norm_cast0 $[$loc]? ))

/-- The tactic call `exact_mod_inv h` succeeds if the hypothesis `h` and the goal are the same,
up to cancelling inverses and making the possible simplifications by considering as inequalities of
natural numbers. -/
macro "exact_mod_inv" h:term : tactic => `(tactic| (cancel_nat_inv at $h:term ⊢; exact $h))

theorem Nat.le_antisymm' {n m : ℕ} (h1 : n + 1 ≤ m + 1) (h2 : m ≤ n ) : n = m :=
  Nat.le_antisymm (Nat.le_of_succ_le_succ h1) h2

macro "inv_bounds" h1:term "," h2:term : tactic =>
  `(tactic| (cancel_nat_inv at $h1:term $h2:term ⊢; exact Nat.le_antisymm' $h1 $h2))

/-- Classification of triples `(p, q, r)` of natural numbers, such that `p⁻¹ + q⁻¹ + r⁻¹ = 1`.
Method 1: following a textbook. -/
example {p q r : ℕ} (hp : 2 ≤ p) (hpq : p ≤ q) (hqr : q ≤ r) (h : (p:ℚ)⁻¹ + (q:ℚ)⁻¹ + (r:ℚ)⁻¹ = 1) :
    (p, q, r) = (3, 3, 3) ∨ (p, q, r) = (2, 4, 4) ∨ (p, q, r) = (2, 3, 6) := by
  have : 0 < q := by linarith only [hp, hpq]
  have : 0 < r := by linarith only [hp, hpq, hqr]
  have h₁ : 0 < (r:ℚ)⁻¹ := by positivity
  have h₂ : (q:ℚ)⁻¹ ≤ (p:ℚ)⁻¹ := by gcongr
  have h₃ : (r:ℚ)⁻¹ ≤ (q:ℚ)⁻¹ := by gcongr
  have H₁ : 3⁻¹ ≤ (p:ℚ)⁻¹ := by linarith only [h, h₂, h₃]
  have H₂ : (q:ℚ)⁻¹ < 2⁻¹ := by linarith only [h, h₁, h₂]
  -- ** Real work starts here
  obtain hp₂ | hp := (eq_or_gt_of_le H₁).symm
  have hp : (p:ℚ)⁻¹ = 2⁻¹ := by inv_bounds hp₂, hp
  have H₃ : 4⁻¹ ≤ (q:ℚ)⁻¹ := by linarith only [h, hp, h₃]
  obtain hq₂ | hq := (eq_or_gt_of_le H₃).symm
  have hq : (q:ℚ)⁻¹ = 3⁻¹ := by inv_bounds hq₂, H₂
  all_goals
    sorry
    -- linear_solve hq : (q:ℚ)⁻¹
    -- linear_solve hr : (r:ℚ)⁻¹
    -- cancel_nat_inv at hp hq hr
    -- simp [hp, hq, hr]

/-- Classification of triples `(p, q, r)` of natural numbers, such that `p⁻¹ + q⁻¹ + r⁻¹ = 1`.
Method 2: hybrid. -/
example {p q r : ℕ} (hp : 2 ≤ p) (hpq : p ≤ q) (hqr : q ≤ r) (h : (p:ℚ)⁻¹ + (q:ℚ)⁻¹ + (r:ℚ)⁻¹ = 1) :
    (p, q, r) = (3, 3, 3) ∨ (p, q, r) = (2, 4, 4) ∨ (p, q, r) = (2, 3, 6) := by
  have : 0 < q := by linarith only [hp, hpq]
  have : 0 < r := by linarith only [hp, hpq, hqr]
  have h₁ : 0 < (r:ℚ)⁻¹ := by positivity
  have h₂ : (q:ℚ)⁻¹ ≤ (p:ℚ)⁻¹ := by gcongr
  have h₃ : (r:ℚ)⁻¹ ≤ (q:ℚ)⁻¹ := by gcongr
  have H₁ : 3⁻¹ ≤ (p:ℚ)⁻¹ := by linarith only [h, h₂, h₃]
  have H₂ : (q:ℚ)⁻¹ < 2⁻¹ := by linarith only [h, h₁, h₂]
  -- ** Real work starts here
  have h₄ : (p:ℚ)⁻¹ ≤ (2:ℚ)⁻¹ := by exact_mod_inv hp
  have H₃ : 4⁻¹ ≤ (q:ℚ)⁻¹ := by linarith only [h, h₃, h₄]
  cancel_nat_inv at H₁ H₂ H₃
  rw [← eq_sub_iff_add_eq', inv_eq_iff_eq_inv] at h -- `isolate r at h`
  interval_cases p <;> interval_cases q <;>
  · norm_num1 at h
    cancel_denoms at h
    norm_cast0 at h
    simp
    omega

/-- Classification of triples `(p, q, r)` of natural numbers, such that `p⁻¹ + q⁻¹ + r⁻¹ = 1`.
Method 3: maximally exploit computerized case-checking. -/
example {p q r : ℕ} (hp : 2 ≤ p) (hpq : p ≤ q) (hqr : q ≤ r) (h : (p:ℚ)⁻¹ + (q:ℚ)⁻¹ + (r:ℚ)⁻¹ = 1) :
    (p, q, r) = (3, 3, 3) ∨ (p, q, r) = (2, 4, 4) ∨ (p, q, r) = (2, 3, 6) := by
  have : 0 < q := by linarith only [hp, hpq]
  have : 0 < r := by linarith only [hp, hpq, hqr]
  have h₁ : 0 < (r:ℚ)⁻¹ := by positivity
  have h₂ : (q:ℚ)⁻¹ ≤ (p:ℚ)⁻¹ := by gcongr
  have h₃ : (r:ℚ)⁻¹ ≤ (q:ℚ)⁻¹ := by gcongr
  have H₁ : 3⁻¹ ≤ (p:ℚ)⁻¹ := by linarith only [h, h₂, h₃]
  have H₂ : (q:ℚ)⁻¹ < 2⁻¹ := by linarith only [h, h₁, h₂]
  -- ** Real work starts here
  have h₄ : (p:ℚ)⁻¹ ≤ (2:ℚ)⁻¹ := by exact_mod_inv hp
  have H₃ : 4⁻¹ ≤ (q:ℚ)⁻¹ := by linarith only [h, h₃, h₄]
  have H₄ : (q:ℚ)⁻¹ ≤ 3⁻¹ := by exact_mod_inv H₂
  have H₅ : 6⁻¹ ≤ (r:ℚ)⁻¹ := by linarith only [h, h₄, H₄]
  cancel_nat_inv at H₁ H₂ H₃ H₅
  interval_cases p <;> interval_cases q <;> interval_cases r <;> norm_num1 at h <;> simp
