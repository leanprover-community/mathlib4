/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Analysis.Normed.ValuativeRel
import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# p-adic numbers with a valuative relation

## Tags

p-adic, p adic, padic, norm, valuation, cauchy, completion, p-adic completion
-/

variable {p : ℕ} [hp : Fact p.Prime]

open ValuativeRel

instance : ValuativeRel ℚ_[p] := .ofValuation NormedField.valuation'

@[simp] lemma valuation_le_iff {x y : ℚ_[p]} :
    valuation ℚ_[p] x ≤ valuation _ y ↔ ‖x‖ ≤ ‖y‖ := by
  rw [← NormedField.rel_iff_le, ← Valuation.Compatible.rel_iff_le]

@[simp] lemma valuation_eq_iff {x y : ℚ_[p]} :
    valuation ℚ_[p] x = valuation _ y ↔ ‖x‖ = ‖y‖ := by
  simp [le_antisymm_iff]

@[simp] lemma valuation_lt_iff {x y : ℚ_[p]} :
    valuation ℚ_[p] x < valuation _ y ↔ ‖x‖ < ‖y‖ := by
  rw [lt_iff_le_not_ge]
  simpa using le_of_lt

lemma valuation_p_ne_zero : valuation ℚ_[p] p ≠ 0 := by simp [hp.out.ne_zero]

@[simp]
lemma valuation_p_lt_one :
    valuation ℚ_[p] p < 1 := by
  simp only [← map_one (valuation _), valuation_lt_iff, padicNormE.norm_p, norm_one]
  rw [inv_lt_one₀]
  · simp [hp.out.one_lt]
  · simp [hp.out.pos]

instance : IsRankLeOne ℚ_[p] := inferInstance

instance : IsNontrivial ℚ_[p] where
  condition := ⟨valuation _ p, valuation_p_ne_zero, valuation_p_lt_one.ne⟩

instance : IsDiscrete ℚ_[p] := by
  refine ⟨valuation _ p, valuation_p_lt_one, fun x hx ↦ ?_⟩
  induction x using ValueGroupWithZero.ind with | mk r s
  simp only [← ValueGroupWithZero.mk_one_one, ValueGroupWithZero.mk_lt_mk, OneMemClass.coe_one,
    mul_one, one_mul, NormedField.rel_iff_le, not_le] at hx
  simp [valuation, NormedField.rel_iff_le]
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · have hs : (s : ℚ_[p]) ≠ 0 := by simp
    obtain ⟨n, hn⟩ := padicNormE.image hr
    obtain ⟨m, hm⟩ := padicNormE.image hs
    rw [hm, hn] at hx ⊢
    have : m < n := by
      rw [← neg_lt_neg_iff,
        ← (zpow_right_strictMono₀ (a := (p : ℚ)) (by exact_mod_cast hp.out.one_lt)).lt_iff_lt]
      exact_mod_cast hx.right
    push_cast
    rw [mul_comm, ← zpow_sub_one₀ (by exact_mod_cast hp.out.ne_zero),
      zpow_le_zpow_iff_right₀]
    · linarith
    · exact_mod_cast hp.out.one_lt
