/-
Copyright (c) 2026 E. S. Markov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: E. S. Markov
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Rational Barrier Potentials and Clamped Clearance Regularizers

This file formalizes the monotonicity, boundary vanishing, and uniform bounds of rational
internal-pressure functions `P_in(ρ) = κ * (Λ - ρ) / (ρ + 1)` and clamped clearance
regularizers `max 0 (L₀ * (1 - (P_ext - P_in) / (P_in + ε)))` on `[0, Λ]`.

## Main definitions

* `rationalPressure κ Λ ρ`: the rational internal potential `κ * (Λ - ρ) / (ρ + 1)`.
* `clampedClearance L₀ ε P_in P_ext`: the non-negative clamped regularizer
  `max 0 (L₀ * (1 - (P_ext - P_in) / (P_in + ε)))`.

## Main results

* `rationalPressure_nonneg` & `rationalPressure_limit`: non-negativity on `[0, Λ]` and vanishing
  at the saturation boundary `ρ = Λ`.
* `rationalPressure_strictAnti` & `rationalPressure_le_max`: strict antitone decay on `[0, Λ]`
  with maximum `κ * Λ` at `ρ = 0`.
* `clampedClearance_bounds`, `clampedClearance_balanced`, & `clampedClearance_collapse`: uniform
  two-sided bounds `[0, L₀]` under external compression, equilibrium value `L₀`, and vanishing
  above the critical threshold `2 * P_in + ε`.
-/

@[expose] public section

noncomputable section

section RationalClearance

/-- Rational internal barrier potential `κ * (Λ - ρ) / (ρ + 1)` with capacity bound `Λ`. -/
def rationalPressure (κ Λ ρ : ℝ) : ℝ :=
  κ * (Λ - ρ) / (ρ + 1)

/-- Clamped non-negative clearance regularizer `max 0 (L₀ * (1 - (P_ext - P_in) / (P_in + ε)))`. -/
def clampedClearance (L₀ ε P_in P_ext : ℝ) : ℝ :=
  max 0 (L₀ * (1 - (P_ext - P_in) / (P_in + ε)))

/-- At zero density (`ρ = 0`), the rational pressure equals `κ * Λ`. -/
theorem rationalPressure_zero (κ Λ : ℝ) :
    rationalPressure κ Λ 0 = κ * Λ := by
  dsimp [rationalPressure]
  ring

/-- At the saturation boundary (`ρ = Λ`), the rational pressure vanishes identically. -/
theorem rationalPressure_limit (κ Λ : ℝ) :
    rationalPressure κ Λ Λ = 0 := by
  dsimp [rationalPressure]
  ring

/-- **Non-negativity on `[0, Λ]`:** for `κ ≥ 0` and `0 ≤ ρ ≤ Λ`, `rationalPressure κ Λ ρ ≥ 0`. -/
theorem rationalPressure_nonneg {κ Λ ρ : ℝ} (hκ : 0 ≤ κ) (hρ0 : 0 ≤ ρ) (hρΛ : ρ ≤ Λ) :
    0 ≤ rationalPressure κ Λ ρ := by
  dsimp [rationalPressure]
  have h_num : 0 ≤ κ * (Λ - ρ) := mul_nonneg hκ (by linarith)
  have h_den : 0 < ρ + 1 := by linarith
  exact div_nonneg h_num h_den.le

/-- **Strict antitone decay on `[0, Λ]`:** for `κ > 0`, `Λ > 0`, and `0 ≤ ρ₁ < ρ₂`,
the rational pressure strictly decreases (`rationalPressure κ Λ ρ₂ < rationalPressure κ Λ ρ₁`). -/
theorem rationalPressure_strictAnti {κ Λ ρ₁ ρ₂ : ℝ}
    (hκ : 0 < κ) (hΛ : 0 < Λ) (hρ₁ : 0 ≤ ρ₁) (hlt : ρ₁ < ρ₂) :
    rationalPressure κ Λ ρ₂ < rationalPressure κ Λ ρ₁ := by
  dsimp [rationalPressure]
  have hd₁ : 0 < ρ₁ + 1 := by linarith
  have hd₂ : 0 < ρ₂ + 1 := by linarith
  rw [div_lt_div_iff₀ hd₂ hd₁]
  have h_diff : κ * (Λ - ρ₁) * (ρ₂ + 1) - κ * (Λ - ρ₂) * (ρ₁ + 1) =
      κ * (Λ + 1) * (ρ₂ - ρ₁) := by ring
  have h_pos : 0 < κ * (Λ + 1) * (ρ₂ - ρ₁) := by
    have hΛ1 : 0 < Λ + 1 := by linarith
    have hρ12 : 0 < ρ₂ - ρ₁ := by linarith
    positivity
  linarith

/-- **Upper bound on `[0, Λ]`:** for `κ > 0`, `Λ > 0`, and `0 ≤ ρ ≤ Λ`,
`rationalPressure κ Λ ρ ≤ κ * Λ`. -/
theorem rationalPressure_le_max {κ Λ ρ : ℝ}
    (hκ : 0 < κ) (hΛ : 0 < Λ) (hρ0 : 0 ≤ ρ) (hρΛ : ρ ≤ Λ) :
    rationalPressure κ Λ ρ ≤ κ * Λ := by
  rcases eq_or_lt_of_le hρ0 with rfl | hpos
  · rw [rationalPressure_zero]
  · exact (rationalPressure_strictAnti hκ hΛ le_rfl hpos).le.trans (by rw [rationalPressure_zero])

/-- **Two-sided uniform bounds under external compression (`P_in ≤ P_ext`):**
for `L₀ > 0`, `ε > 0`, and `0 ≤ P_in ≤ P_ext`, the clamped clearance lies strictly in `[0, L₀]`
without division-by-zero singularities. -/
theorem clampedClearance_bounds {L₀ ε P_in P_ext : ℝ}
    (hL : 0 < L₀) (hε : 0 < ε) (hPin : 0 ≤ P_in) (hcomp : P_in ≤ P_ext) :
    0 ≤ clampedClearance L₀ ε P_in P_ext ∧ clampedClearance L₀ ε P_in P_ext ≤ L₀ := by
  dsimp [clampedClearance]
  refine ⟨le_max_left _ _, max_le hL.le ?_⟩
  have h_den : 0 < P_in + ε := by linarith
  have h_ratio : 0 ≤ (P_ext - P_in) / (P_in + ε) := div_nonneg (by linarith) h_den.le
  have h_le1 : 1 - (P_ext - P_in) / (P_in + ε) ≤ 1 := by linarith
  calc L₀ * (1 - (P_ext - P_in) / (P_in + ε))
    _ ≤ L₀ * 1 := mul_le_mul_of_nonneg_left h_le1 hL.le
    _ = L₀ := mul_one L₀

/-- **Balanced pressure equilibrium (`P_ext = P_in`):** when external and internal pressures
match, the clamped clearance equals its baseline value `L₀`. -/
theorem clampedClearance_balanced {L₀ ε P : ℝ} (hL : 0 < L₀) :
    clampedClearance L₀ ε P P = L₀ := by
  dsimp [clampedClearance]
  have h_eq : L₀ * (1 - (P - P) / (P + ε)) = L₀ := by ring
  rw [h_eq]
  exact max_eq_right hL.le

/-- **Collapse under critical overpressure (`P_ext ≥ 2 * P_in + ε`):** once external compression
exceeds `2 * P_in + ε`, the clamped clearance vanishes identically (`clampedClearance = 0`). -/
theorem clampedClearance_collapse {L₀ ε P_in P_ext : ℝ}
    (hL : 0 < L₀) (hε : 0 < ε) (hPin : 0 ≤ P_in) (hover : 2 * P_in + ε ≤ P_ext) :
    clampedClearance L₀ ε P_in P_ext = 0 := by
  dsimp [clampedClearance]
  have h_den : 0 < P_in + ε := by linarith
  have h_ge1 : 1 ≤ (P_ext - P_in) / (P_in + ε) := by
    rw [le_div_iff₀ h_den]
    linarith
  have h_nonpos : L₀ * (1 - (P_ext - P_in) / (P_in + ε)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hL.le (by linarith)
  exact max_eq_left h_nonpos

end RationalClearance
