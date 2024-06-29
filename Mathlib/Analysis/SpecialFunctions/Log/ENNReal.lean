/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Topology.Instances.EReal

/-!
# Extended nonnegative real logarithm

We define `log` as an extension of the logarithm of a positive real
to the extended nonnegative reals `ℝ≥0∞`. The function takes values
in the extended reals `EReal`, with `log 0 = ⊥` and `log ⊤ = ⊤`.

## Main definitions
- `ENNReal.log`: The extension of the real logarithm to `ℝ≥0∞`.
- `ENNReal.log_orderIso`, `ENNReal.log_equiv`: `log` seen respectively
as an order isomorphism and an homeomorphism.

## Main Results
- `ENNReal.log_strictMono`: `log` is increasing;
- `ENNReal.log_injective`, `ENNReal.log_surjective`, `ENNReal.log_bijective`: `log` is
  injective, surjective, and bijective;
- `ENNReal.log_mul_add`, `ENNReal.log_pow`, `ENNReal.log_rpow`: `log` satisfy
the identities `log (x * y) = log x + log y` and `log (x ^ y) = y * log x`
(with either `y ∈ ℕ` or `y ∈ ℝ`).

## TODO
- Define `exp` on `EReal` and prove its basic properties.

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
    else Real.log (ENNReal.toReal x)

@[simp]
theorem log_zero : log 0 = ⊥ := by simp [log]

@[simp]
theorem log_one : log 1 = 0 := by simp [log]

@[simp]
theorem log_top : log ⊤ = ⊤ := by simp [log]

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

theorem log_monotone : Monotone log := StrictMono.monotone log_strictMono

theorem log_injective : Function.Injective log := StrictMono.injective log_strictMono

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

/-- `log` as an order isomorphism. -/
noncomputable def log_orderIso : ℝ≥0∞ ≃o EReal :=
  StrictMono.orderIsoOfSurjective log log_strictMono log_surjective

@[simp] lemma log_orderIso_apply (x : ℝ≥0∞) : log_orderIso x = log x := rfl

@[simp]
theorem log_eq_iff {x y : ℝ≥0∞} : log x = log y ↔ x = y :=
  Iff.intro (@log_injective x y) (fun h ↦ by rw [h])

@[simp]
theorem log_eq_bot_iff {x : ℝ≥0∞} : log x = ⊥ ↔ x = 0 := log_zero ▸ @log_eq_iff x 0

@[simp]
theorem log_eq_one_iff {x : ℝ≥0∞} : log x = 0 ↔ x = 1 := log_one ▸ @log_eq_iff x 1

@[simp]
theorem log_eq_top_iff {x : ℝ≥0∞} : log x = ⊤ ↔ x = ⊤ := log_top ▸ @log_eq_iff x ⊤

@[simp]
theorem log_lt_iff_lt {x y : ℝ≥0∞} : log x < log y ↔ x < y := OrderIso.lt_iff_lt log_orderIso

@[simp]
theorem log_bot_lt_iff {x : ℝ≥0∞} : ⊥ < log x ↔ 0 < x := log_zero ▸ @log_lt_iff_lt 0 x

@[simp]
theorem log_lt_top_iff {x : ℝ≥0∞} : log x < ⊤ ↔ x < ⊤ := log_top ▸ @log_lt_iff_lt x ⊤

@[simp]
theorem log_lt_one_iff {x : ℝ≥0∞} : log x < 0 ↔ x < 1 := log_one ▸ @log_lt_iff_lt x 1

@[simp]
theorem log_one_lt_iff {x : ℝ≥0∞} : 0 < log x ↔ 1 < x := log_one ▸ @log_lt_iff_lt 1 x

@[simp]
theorem log_le_iff_le {x y : ℝ≥0∞} : log x ≤ log y ↔ x ≤ y := OrderIso.le_iff_le log_orderIso

@[simp]
theorem log_le_one_iff (x : ℝ≥0∞) : log x ≤ 0 ↔ x ≤ 1 := log_one ▸ @log_le_iff_le x 1

@[simp]
theorem log_one_le_iff {x : ℝ≥0∞} : 0 ≤ log x ↔ 1 ≤ x := log_one ▸ @log_le_iff_le 1 x

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

theorem log_pow {x : ℝ≥0∞} {n : ℕ} : log (x ^ n) = (n : ℝ≥0∞) * log x := by
  cases' Nat.eq_zero_or_pos n with n_zero n_pos
  · simp [n_zero, pow_zero x]
  rcases ENNReal.trichotomy x with (rfl | rfl | x_real)
  · rw [zero_pow (Ne.symm (ne_of_lt n_pos)), log_zero, EReal.mul_bot_of_pos]; norm_cast
  · rw [ENNReal.top_pow n_pos, log_top, EReal.mul_top_of_pos]; norm_cast
  · replace x_real := ENNReal.toReal_pos_iff.1 x_real
    have x_ne_zero := Ne.symm (LT.lt.ne x_real.1)
    have x_ne_top := LT.lt.ne x_real.2
    simp only [log, pow_eq_zero_iff', x_ne_zero, ne_eq, false_and, ↓reduceIte, pow_eq_top_iff,
      x_ne_top, toReal_pow, Real.log_pow, EReal.coe_mul]
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

end Morphism

/-! ### Topological properties -/

section Continuity

/-- `log` as a homeomorphism. -/
noncomputable def log_homeomorph : ℝ≥0∞ ≃ₜ EReal := OrderIso.toHomeomorph log_orderIso

@[simp] theorem log_homeomorph_apply (x : ℝ≥0∞) : log_homeomorph x = log x := rfl

@[continuity, fun_prop]
theorem log_continuous : Continuous log := Homeomorph.continuous log_homeomorph

end Continuity

end ENNReal
