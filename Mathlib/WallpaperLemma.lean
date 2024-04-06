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
import Mathlib.Tactic.Qify

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

open Lean.Parser.Tactic in
/-- The tactic `cleanup_nat_inv` normalizes numerically, then cancels inverses and simplifies casts.
-/
macro "cleanup_nat_inv" loc:(location)? : tactic =>
  `(tactic|
  ( norm_num1 $[$loc]?
    try rw [← inv_eq_one_div] $[$loc]?
    cancel_nat_inv $[$loc]? ))

/-- Classification of triples `(p, q, r)` of natural numbers, such that `p⁻¹ + q⁻¹ + r⁻¹ = 1`.
Method 1: following a textbook. -/
example {p q r : ℕ} (hp : 2 ≤ p) (hpq : p ≤ q) (hqr : q ≤ r) (h : (p:ℚ)⁻¹ + (q:ℚ)⁻¹ + (r:ℚ)⁻¹ = 1) :
    (p, q, r) = (3, 3, 3) ∨ (p, q, r) = (2, 4, 4) ∨ (p, q, r) = (2, 3, 6) := by
  have : 0 < q := by linarith only [hp, hpq]
  have : 0 < r := by linarith only [hp, hpq, hqr]
  have h₁ : 0 < (r:ℚ)⁻¹ := by positivity
  have h₂ : (q:ℚ)⁻¹ ≤ (p:ℚ)⁻¹ := by gcongr
  have h₃ : (r:ℚ)⁻¹ ≤ (q:ℚ)⁻¹ := by gcongr
  have Hp_lower : 3⁻¹ ≤ (p:ℚ)⁻¹ := by linarith only [h, h₂, h₃]
  have Hq_upper : (q:ℚ)⁻¹ < 2⁻¹ := by linarith only [h, h₁, h₂]
  -- ** Real work starts here
  have Hq_lower : (1 - (p:ℚ)⁻¹) / 2 ≤ (q:ℚ)⁻¹ := by linarith only [h, h₃]
  have Hr : (r:ℚ)⁻¹ = 1 - (p:ℚ)⁻¹ - (q:ℚ)⁻¹ := by linarith only [h]
  cleanup_nat_inv at Hp_lower
  interval_cases p <;>
  · cleanup_nat_inv at Hq_upper Hq_lower
    interval_cases q <;>
    · cleanup_nat_inv at Hr
      tauto

/-- Classification of triples `(p, q, r)` of natural numbers, such that `p⁻¹ + q⁻¹ + r⁻¹ = 1`.
Method 3: maximally exploit computerized case-checking. -/
example {p q r : ℕ} (hp : 2 ≤ p) (hpq : p ≤ q) (hqr : q ≤ r) (h : (p:ℚ)⁻¹ + (q:ℚ)⁻¹ + (r:ℚ)⁻¹ = 1) :
    (p, q, r) = (3, 3, 3) ∨ (p, q, r) = (2, 4, 4) ∨ (p, q, r) = (2, 3, 6) := by
  have : 0 < q := by linarith only [hp, hpq]
  have : 0 < r := by linarith only [hp, hpq, hqr]
  have h₁ : 0 < (r:ℚ)⁻¹ := by positivity
  have h₂ : (q:ℚ)⁻¹ ≤ (p:ℚ)⁻¹ := by gcongr
  have h₃ : (r:ℚ)⁻¹ ≤ (q:ℚ)⁻¹ := by gcongr
  have Hp_lower : 3⁻¹ ≤ (p:ℚ)⁻¹ := by linarith only [h, h₂, h₃]
  have Hq_upper : (q:ℚ)⁻¹ < 2⁻¹ := by linarith only [h, h₁, h₂]
  -- ** Real work starts here
  have h₄ : (p:ℚ)⁻¹ ≤ (2:ℚ)⁻¹ := by exact_mod_inv hp
  have H₃ : 4⁻¹ ≤ (q:ℚ)⁻¹ := by linarith only [h, h₃, h₄]
  have H₄ : (q:ℚ)⁻¹ ≤ 3⁻¹ := by exact_mod_inv Hq_upper
  have H₅ : 6⁻¹ ≤ (r:ℚ)⁻¹ := by linarith only [h, h₄, H₄]
  cancel_nat_inv at Hp_lower Hq_upper H₃ H₅
  interval_cases p <;>
  · interval_cases q <;>
    · interval_cases r <;>
      · norm_num1 at h <;>
        · simp
