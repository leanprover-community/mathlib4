/-
Copyright (c) 2023 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Real.EReal
import Mathlib.Logic.Equiv.Basic
import Mathlib.Topology.Instances.ENNReal
import Mathlib.Topology.Instances.EReal

/-!
# Extended nonnegative real logarithm
We define `log` as an extension of the logarithm of a positive real 
to the extended nonnegative reals `ENNReal`. The function takes values in the extended reals `EReal`, 
with `log 0 = ⊥` and `log ⊤ = ⊤`.

## Main definitions
- `log`: The extension of the real logarithm to `ENNReal`.
- `log_OrderIso`, `log_equiv`: `log` seen respectively 
as an order isomorphism and an homeomorphism.

## Main Results
- `log_strictMono`: `log` is increasing;
- `log_injective`, `log_surjective`, `log_bijective`: `log` is
  injective, surjective, and bijective;
- `log_mul_add`, `log_pow`, `log_pow`: `log` satisfy 
the identities `log (x * y) = log x + log y` and `log (x * y) = y * log x` (with either `y ∈ ℕ` or `y ∈ ℝ`).

## Tags
ENNReal, EReal, logarithm
-/


namespace ENNReal

/-! ### Definition -/


section Definition

/--
The logarithm function defined on the extended nonnegative reals `ENNReal` to the extended reals `EReal`. 
Coincides with the usual logarithm function and with `Real.log` on positive reals, and takes 
values `log 0 = ⊥` and `log ⊤ = ⊤`. Conventions about multiplication in `ENNReal` 
and addition in `EReal` make the identity `log (x * y) = log x + log y` unconditionnal. --/
noncomputable def log (x : ENNReal) : EReal :=
  if x = 0 then ⊥ 
    else if x = ⊤ then ⊤
    else Real.log (ENNReal.toReal x)

@[simp]
theorem log_zero :
  log 0 = ⊥ :=
by simp [log]

@[simp]
theorem log_one :
  log 1 = 0 :=
by simp [log]

@[simp]
theorem log_top :
  log ⊤ = ⊤ :=
by simp [log]

theorem log_pos_real {x : ENNReal} (h : x ≠ 0) (h' : x ≠ ⊤) :
  log x = Real.log (ENNReal.toReal x) :=
by simp [log, h, h']

theorem log_pos_real' {x : ENNReal} (h : 0 < x.toReal) :
  log x = Real.log (ENNReal.toReal x) := 
by simp [log, Ne.symm (ne_of_lt (ENNReal.toReal_pos_iff.1 h).1), 
  ne_of_lt (ENNReal.toReal_pos_iff.1 h).2]

theorem log_of_nNReal {x : NNReal} (h : x ≠ 0) :
  log (ENNReal.ofReal x) = Real.log x :=
by simp [log, h]

end Definition

/-! ### Monotonicity -/


section Monotonicity

theorem log_strictMono :
  StrictMono log :=
by
  intro x y h
  unfold log
  rcases ENNReal.trichotomy x with (x_zero | x_top | x_real)
  . rcases ENNReal.trichotomy y with (y_zero | y_top | y_real)
    . exfalso
      rw [x_zero, y_zero] at h
      exact lt_irrefl 0 h
    . simp [x_zero, y_top]
    . simp [x_zero, Ne.symm (ne_of_lt (ENNReal.toReal_pos_iff.1 y_real).1), 
        ne_of_lt (ENNReal.toReal_pos_iff.1 y_real).2]
  . exfalso
    exact (ne_top_of_lt h) x_top
  . simp [Ne.symm (ne_of_lt (ENNReal.toReal_pos_iff.1 x_real).1), 
      ne_of_lt (ENNReal.toReal_pos_iff.1 x_real).2]
    rcases ENNReal.trichotomy y with (y_zero | y_top | y_real)
    . exfalso 
      rw [y_zero, ← ENNReal.bot_eq_zero] at h
      exact not_lt_bot h
    . simp [y_top]
    . simp [Ne.symm (ne_of_lt (ENNReal.toReal_pos_iff.1 y_real).1), 
        ne_of_lt (ENNReal.toReal_pos_iff.1 y_real).2]
      apply Real.log_lt_log x_real
      apply (ENNReal.toReal_lt_toReal (ne_of_lt (ENNReal.toReal_pos_iff.1 x_real).2) 
        (ne_of_lt (ENNReal.toReal_pos_iff.1 y_real).2)).2 h

theorem log_monotone :
  Monotone log :=
StrictMono.monotone log_strictMono

theorem log_injective :
  Function.Injective log :=
StrictMono.injective log_strictMono

theorem log_surjective :
  Function.Surjective log :=
by
  intro y
  cases' eq_bot_or_bot_lt y with y_bot y_nbot
  · rw [y_bot]
    use ⊥
    exact log_zero
  cases' eq_top_or_lt_top y with y_top y_ntop
  · rw [y_top]
    use ⊤
    exact log_top
  use ENNReal.ofReal (Real.exp y.toReal)
  have exp_y_pos := not_le_of_lt (Real.exp_pos y.toReal)
  simp [log, exp_y_pos, ENNReal.ofReal_ne_top]
  rw [ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos y.toReal)), Real.log_exp y.toReal]
  exact EReal.coe_toReal (ne_of_lt y_ntop) (Ne.symm (ne_of_lt y_nbot))

theorem log_bijective :
  Function.Bijective log :=
⟨log_injective, log_surjective⟩

/-- `log` as an order isomorphism. --/
@[simps!]
noncomputable def log_OrderIso :
  ENNReal ≃o EReal :=
StrictMono.orderIsoOfSurjective log log_strictMono log_surjective

theorem log_eq_iff {x y : ENNReal} :
  x = y ↔ log x = log y :=
by
  apply Iff.intro
  · intro h
    rw [h]
  · exact @log_injective x y

theorem log_eq_bot_iff {x : ENNReal} :
  x = 0 ↔ log x = ⊥ :=
by
  rw [← log_zero]
  exact @log_eq_iff x 0

theorem log_eq_one_iff {x : ENNReal} :
  x = 1 ↔ log x = 0 :=
by
  rw [← log_one]
  exact @log_eq_iff x 1

theorem log_eq_top_iff {x : ENNReal} :
  x = ⊤ ↔ log x = ⊤ :=
by
  rw [← log_top]
  exact @log_eq_iff x ⊤

theorem log_lt_iff_lt {x y : ENNReal} :
  x < y ↔ log x < log y :=
Iff.symm (OrderIso.lt_iff_lt log_OrderIso)

theorem log_bot_lt_iff {x : ENNReal} :
  0 < x ↔ ⊥ < log x :=
by
  rw [← log_zero]
  exact @log_lt_iff_lt 0 x

theorem log_lt_top_iff {x : ENNReal} :
  x < ⊤ ↔ log x < ⊤ :=
by
  rw [← log_top]
  exact @log_lt_iff_lt x ⊤

theorem log_lt_one_iff {x : ENNReal} :
  x < 1 ↔ log x < 0 :=
by
  rw [← log_one]
  exact @log_lt_iff_lt x 1

theorem log_one_lt_iff {x : ENNReal} :
  1 < x ↔ 0 < log x :=
by
  rw [← log_one]
  exact @log_lt_iff_lt 1 x

theorem log_le_iff_le {x y : ENNReal} :
  x ≤ y ↔ log x ≤ log y :=
Iff.symm (OrderIso.le_iff_le log_OrderIso)

theorem log_le_one_iff (x : ENNReal) :
  x ≤ 1 ↔ log x ≤ 0 :=
by
  rw [← log_one]
  exact @log_le_iff_le x 1

theorem log_one_le_iff {x : ENNReal} :
  1 ≤ x ↔ 0 ≤ log x :=
by
  rw [← log_one]
  exact @log_le_iff_le 1 x

end Monotonicity

/-! ### Algebraic properties -/


section Morphism

theorem log_mul_add {x y : ENNReal} :
  log (x * y) = log x + log y :=
by
  rcases ENNReal.trichotomy x with (x_zero | x_top | x_real)
  · simp [x_zero]
  · simp [x_top]
    rcases ENNReal.trichotomy y with (y_zero | y_top | y_real)
    · simp [y_zero]
    · simp [y_top]
    · rw [log_pos_real' y_real, ENNReal.top_mul']
      simp
      rw [← log_eq_top_iff]
      simp
      exact Ne.symm (ne_of_lt (ENNReal.toReal_pos_iff.1 y_real).1)
  · rw [log_pos_real' x_real]
    rcases ENNReal.trichotomy y with (y_zero | y_top | y_real)
    · simp [y_zero]
    · simp [y_top, ENNReal.mul_top']
      rw [← log_eq_top_iff]
      simp
      exact Ne.symm (ne_of_lt (ENNReal.toReal_pos_iff.1 x_real).1)
    · have xy_real := Real.mul_pos x_real y_real
      rw [← ENNReal.toReal_mul] at xy_real 
      rw [log_pos_real' xy_real, log_pos_real' y_real, ENNReal.toReal_mul]
      norm_cast
      exact Real.log_mul (Ne.symm (ne_of_lt x_real)) (Ne.symm (ne_of_lt y_real))

theorem log_pow {x : ENNReal} {n : ℕ} :
    log (x ^ n) = (n : ENNReal) * log x :=
by
  by_cases h_n_pos : n = 0
  · rw [h_n_pos, pow_zero x]
    simp
  replace h_n_pos := Nat.pos_of_ne_zero h_n_pos
  rcases ENNReal.trichotomy x with (x_zero | x_top | x_real)
  · rw [x_zero, zero_pow h_n_pos, log_zero, EReal.mul_bot_of_pos]
    norm_cast
  · rw [x_top, ENNReal.top_pow h_n_pos, log_top, EReal.mul_top_of_pos]
    norm_cast
  · replace x_real := ENNReal.toReal_pos_iff.1 x_real
    have x_ne_zero := Ne.symm (LT.lt.ne x_real.1)
    have x_ne_top := LT.lt.ne x_real.2
    have xn_ne_zero := pow_ne_zero n x_ne_zero
    simp [log, x_ne_zero, x_ne_top, xn_ne_zero]
    rfl

theorem log_rpow {x : ENNReal} {y : ℝ} : log (x ^ y) = y * log x :=
  by
  rcases lt_trichotomy y 0 with (y_neg | y_zero | y_pos)
  · rcases ENNReal.trichotomy x with (x_zero | x_top | x_real)
    · rw [x_zero, ENNReal.zero_rpow_def y]
      simp [not_lt_of_lt y_neg, ne_of_lt y_neg]
      exact Eq.symm (EReal.coe_mul_bot_of_neg y_neg)
    · rw [x_top, ENNReal.top_rpow_of_neg y_neg]
      simp
      exact Eq.symm (EReal.coe_mul_top_of_neg y_neg)
    · have x_ne_zero := Ne.symm (LT.lt.ne (ENNReal.toReal_pos_iff.1 x_real).1)
      have x_ne_top := LT.lt.ne (ENNReal.toReal_pos_iff.1 x_real).2
      simp [log, x_ne_zero, x_ne_top]
      norm_cast
      rw [← ENNReal.toReal_rpow x y]
      apply Real.log_rpow x_real y
  · rw [y_zero, @ENNReal.rpow_zero x]
    simp
  · rcases ENNReal.trichotomy x with (x_zero | x_top | x_real)
    · rw [x_zero, ENNReal.zero_rpow_of_pos y_pos, log_zero, EReal.mul_bot_of_pos]
      norm_cast
    · rw [x_top, ENNReal.top_rpow_of_pos y_pos, log_top, EReal.mul_top_of_pos]
      norm_cast
    · have x_ne_zero := Ne.symm (LT.lt.ne (ENNReal.toReal_pos_iff.1 x_real).1)
      have x_ne_top := LT.lt.ne (ENNReal.toReal_pos_iff.1 x_real).2
      simp [log, x_ne_zero, x_ne_top]
      norm_cast
      rw [← ENNReal.toReal_rpow x y]
      apply Real.log_rpow x_real y

end Morphism


/-! ### Topological properties -/

section Continuity

/-- `log` as an homeomorphism. --/
@[simps!]
noncomputable def log_Homeomorph :
  ENNReal ≃ₜ EReal :=
OrderIso.toHomeomorph log_OrderIso

@[continuity]
theorem log_Continuous :
  Continuous log :=
Homeomorph.continuous log_Homeomorph

end Continuity

#lint

end ENNReal