/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone, Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Data.Real.EReal
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Extended Nonnegative Real Logarithm

We define `log` as an extension of the logarithm of a positive real
to the extended nonnegative reals `ℝ≥0∞`. The function takes values
in the extended reals `EReal`, with `log 0 = ⊥` and `log ⊤ = ⊤`.

## Main Definitions
- `ENNReal.log`: The extension of the real logarithm to `ℝ≥0∞`.

## Main Results
- `ENNReal.log_strictMono`: `log` is increasing;
- `ENNReal.log_injective`, `ENNReal.log_surjective`, `ENNReal.log_bijective`: `log` is
  injective, surjective, and bijective;
- `ENNReal.log_mul_add`, `ENNReal.log_pow`, `ENNReal.log_rpow`: `log` satisfies
the identities `log (x * y) = log x + log y` and `log (x ^ y) = y * log x`
(with either `y ∈ ℕ` or `y ∈ ℝ`).

## Tags
ENNReal, EReal, logarithm
-/
namespace ENNReal

open scoped NNReal

/-! ### Definition -/
section Definition

/-- The logarithm function defined on the extended nonnegative reals `ℝ≥0∞`
to the extended reals `EReal`. Coincides with the usual logarithm function
and with `Real.log` on positive reals, and takes values `log 0 = ⊥` and `log ⊤ = ⊤`.
Conventions about multiplication in `ℝ≥0∞` and addition in `EReal` make the identity
`log (x * y) = log x + log y` unconditional. -/
noncomputable def log (x : ℝ≥0∞) : EReal :=
  if x = 0 then ⊥
    else if x = ⊤ then ⊤
    else Real.log x.toReal

@[simp] lemma log_zero : log 0 = ⊥ := if_pos rfl
@[simp] lemma log_one : log 1 = 0 := by simp [log]
@[simp] lemma log_top : log ⊤ = ⊤ := rfl

@[simp]
lemma log_ofReal (x : ℝ) : log (ENNReal.ofReal x) = if x ≤ 0 then ⊥ else ↑(Real.log x) := by
  simp only [log, ENNReal.none_eq_top, ENNReal.ofReal_ne_top, IsEmpty.forall_iff,
    ENNReal.ofReal_eq_zero, EReal.coe_ennreal_ofReal]
  split_ifs with h_nonpos
  · rfl
  · trivial
  · rw [ENNReal.toReal_ofReal]
    exact (not_le.mp h_nonpos).le

lemma log_ofReal_of_pos {x : ℝ} (hx : 0 < x) : log (ENNReal.ofReal x) = Real.log x := by
  rw [log_ofReal, if_neg]
  exact not_le.mpr hx

theorem log_pos_real {x : ℝ≥0∞} (h : x ≠ 0) (h' : x ≠ ⊤) :
    log x = Real.log (ENNReal.toReal x) := by simp [log, h, h']

theorem log_pos_real' {x : ℝ≥0∞} (h : 0 < x.toReal) :
    log x = Real.log (ENNReal.toReal x) := by
  simp [log, Ne.symm (ne_of_lt (ENNReal.toReal_pos_iff.1 h).1),
    ne_of_lt (ENNReal.toReal_pos_iff.1 h).2]

theorem log_of_nnreal {x : ℝ≥0} (h : x ≠ 0) :
    log (x : ℝ≥0∞) = Real.log x := by simp [log, h]

end Definition

/-! ### Monotonicity -/
section Monotonicity

theorem log_strictMono : StrictMono log := by
  intro x y h
  unfold log
  rcases ENNReal.trichotomy x with (rfl | rfl | x_real)
  · rcases ENNReal.trichotomy y with (rfl | rfl | y_real)
    · exfalso; exact lt_irrefl 0 h
    · simp
    · simp [Ne.symm (ne_of_lt (ENNReal.toReal_pos_iff.1 y_real).1),
      ne_of_lt (ENNReal.toReal_pos_iff.1 y_real).2, EReal.bot_lt_coe]
  · exfalso; exact (ne_top_of_lt h) (Eq.refl ⊤)
  · simp only [Ne.symm (ne_of_lt (ENNReal.toReal_pos_iff.1 x_real).1),
      ne_of_lt (ENNReal.toReal_pos_iff.1 x_real).2]
    rcases ENNReal.trichotomy y with (rfl | rfl | y_real)
    · exfalso; rw [← ENNReal.bot_eq_zero] at h; exact not_lt_bot h
    · simp
    · simp only [Ne.symm (ne_of_lt (ENNReal.toReal_pos_iff.1 y_real).1), ↓reduceIte,
        ne_of_lt (ENNReal.toReal_pos_iff.1 y_real).2, EReal.coe_lt_coe_iff]
      apply Real.log_lt_log x_real
      exact (ENNReal.toReal_lt_toReal (ne_of_lt (ENNReal.toReal_pos_iff.1 x_real).2)
        (ne_of_lt (ENNReal.toReal_pos_iff.1 y_real).2)).2 h

theorem log_monotone : Monotone log := log_strictMono.monotone

theorem log_injective : Function.Injective log := log_strictMono.injective

theorem log_surjective : Function.Surjective log := by
  intro y
  cases' eq_bot_or_bot_lt y with y_bot y_nbot
  · exact y_bot ▸ ⟨⊥, log_zero⟩
  cases' eq_top_or_lt_top y with y_top y_ntop
  · exact y_top ▸ ⟨⊤, log_top⟩
  use ENNReal.ofReal (Real.exp y.toReal)
  have exp_y_pos := not_le_of_lt (Real.exp_pos y.toReal)
  simp only [log, ofReal_eq_zero, exp_y_pos, ↓reduceIte, ofReal_ne_top,
    ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos y.toReal)), Real.log_exp y.toReal]
  exact EReal.coe_toReal (ne_of_lt y_ntop) (Ne.symm (ne_of_lt y_nbot))

theorem log_bijective : Function.Bijective log := ⟨log_injective, log_surjective⟩

@[simp]
theorem log_eq_iff {x y : ℝ≥0∞} : log x = log y ↔ x = y :=
  Iff.intro (@log_injective x y) (fun h ↦ by rw [h])

@[simp] theorem log_eq_bot_iff {x : ℝ≥0∞} : log x = ⊥ ↔ x = 0 := log_zero ▸ @log_eq_iff x 0

@[simp] theorem log_eq_one_iff {x : ℝ≥0∞} : log x = 0 ↔ x = 1 := log_one ▸ @log_eq_iff x 1

@[simp] theorem log_eq_top_iff {x : ℝ≥0∞} : log x = ⊤ ↔ x = ⊤ := log_top ▸ @log_eq_iff x ⊤

@[simp] lemma log_lt_log_iff {x y : ℝ≥0∞} : log x < log y ↔ x < y := log_strictMono.lt_iff_lt

@[simp] lemma bot_lt_log_iff {x : ℝ≥0∞} : ⊥ < log x ↔ 0 < x := log_zero ▸ @log_lt_log_iff 0 x

@[simp] lemma log_lt_top_iff {x : ℝ≥0∞} : log x < ⊤ ↔ x < ⊤ := log_top ▸ @log_lt_log_iff x ⊤

@[simp] lemma log_lt_zero_iff {x : ℝ≥0∞} : log x < 0 ↔ x < 1 := log_one ▸ @log_lt_log_iff x 1

@[simp] lemma zero_lt_log_iff {x : ℝ≥0∞} : 0 < log x ↔ 1 < x := log_one ▸ @log_lt_log_iff 1 x

@[simp] lemma log_le_log_iff {x y : ℝ≥0∞} : log x ≤ log y ↔ x ≤ y := log_strictMono.le_iff_le

@[simp] lemma log_le_zero_iff {x : ℝ≥0∞} : log x ≤ 0 ↔ x ≤ 1 := log_one ▸ @log_le_log_iff x 1

@[simp] lemma zero_le_log_iff {x : ℝ≥0∞} : 0 ≤ log x ↔ 1 ≤ x := log_one ▸ @log_le_log_iff 1 x

end Monotonicity

/-! ### Algebraic properties -/

section Morphism

theorem log_mul_add {x y : ℝ≥0∞} : log (x * y) = log x + log y := by
  rcases ENNReal.trichotomy x with (rfl | rfl | x_real)
  · simp
  · rw [log_top]
    rcases ENNReal.trichotomy y with (rfl | rfl | y_real)
    · rw [mul_zero, log_zero, EReal.add_bot]
    · simp
    · rw [log_pos_real' y_real, ENNReal.top_mul', EReal.top_add_coe, log_eq_top_iff]
      simp only [ite_eq_right_iff, zero_ne_top, imp_false]
      exact Ne.symm (ne_of_lt (ENNReal.toReal_pos_iff.1 y_real).1)
  · rw [log_pos_real' x_real]
    rcases ENNReal.trichotomy y with (rfl | rfl | y_real)
    · simp
    · simp [Ne.symm (ne_of_lt (ENNReal.toReal_pos_iff.1 x_real).1)]
    · have xy_real := Real.mul_pos x_real y_real
      rw [← ENNReal.toReal_mul] at xy_real
      rw_mod_cast [log_pos_real' xy_real, log_pos_real' y_real, ENNReal.toReal_mul]
      exact Real.log_mul (Ne.symm (ne_of_lt x_real)) (Ne.symm (ne_of_lt y_real))

theorem log_pow {x : ℝ≥0∞} {n : ℕ} : log (x ^ n) = n * log x := by
  cases' Nat.eq_zero_or_pos n with n_zero n_pos
  · simp [n_zero, pow_zero x]
  rcases ENNReal.trichotomy x with (rfl | rfl | x_real)
  · rw [zero_pow (Ne.symm (ne_of_lt n_pos)), log_zero, EReal.mul_bot_of_pos (Nat.cast_pos'.2 n_pos)]
  · rw [ENNReal.top_pow n_pos, log_top, EReal.mul_top_of_pos (Nat.cast_pos'.2 n_pos)]
  · replace x_real := ENNReal.toReal_pos_iff.1 x_real
    have x_ne_zero := Ne.symm (LT.lt.ne x_real.1)
    have x_ne_top := LT.lt.ne x_real.2
    simp only [log, pow_eq_zero_iff', x_ne_zero, false_and, ↓reduceIte, pow_eq_top_iff, x_ne_top,
      toReal_pow, Real.log_pow, EReal.coe_mul]
    rfl

theorem log_rpow {x : ℝ≥0∞} {y : ℝ} : log (x ^ y) = y * log x := by
  rcases lt_trichotomy y 0 with (y_neg | rfl | y_pos)
  · rcases ENNReal.trichotomy x with (rfl | rfl | x_real)
    · simp only [ENNReal.zero_rpow_def y, not_lt_of_lt y_neg, ne_of_lt y_neg, log_top, log_zero]
      exact Eq.symm (EReal.coe_mul_bot_of_neg y_neg)
    · rw [ENNReal.top_rpow_of_neg y_neg, log_zero, log_top]
      exact Eq.symm (EReal.coe_mul_top_of_neg y_neg)
    · have x_ne_zero := Ne.symm (LT.lt.ne (ENNReal.toReal_pos_iff.1 x_real).1)
      have x_ne_top := LT.lt.ne (ENNReal.toReal_pos_iff.1 x_real).2
      simp only [log, rpow_eq_zero_iff, x_ne_zero, false_and, x_ne_top, or_self, ↓reduceIte,
        rpow_eq_top_iff]
      norm_cast
      exact ENNReal.toReal_rpow x y ▸ Real.log_rpow x_real y
  · simp
  · rcases ENNReal.trichotomy x with (rfl | rfl | x_real)
    · rw [ENNReal.zero_rpow_of_pos y_pos, log_zero, EReal.mul_bot_of_pos]; norm_cast
    · rw [ENNReal.top_rpow_of_pos y_pos, log_top, EReal.mul_top_of_pos]; norm_cast
    · have x_ne_zero := Ne.symm (LT.lt.ne (ENNReal.toReal_pos_iff.1 x_real).1)
      have x_ne_top := LT.lt.ne (ENNReal.toReal_pos_iff.1 x_real).2
      simp only [log, rpow_eq_zero_iff, x_ne_zero, false_and, x_ne_top, or_self, ↓reduceIte,
        rpow_eq_top_iff]
      norm_cast
      exact ENNReal.toReal_rpow x y ▸ Real.log_rpow x_real y

lemma log_inv {x : ℝ≥0∞} : log x⁻¹ = - log x := by
  simp [← rpow_neg_one, log_rpow]

end Morphism

end ENNReal
