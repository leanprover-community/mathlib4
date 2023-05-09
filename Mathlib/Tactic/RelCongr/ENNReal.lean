import Mathlib.Data.Real.ENNReal
import Mathlib.Tactic.RelCongr.Basic

/-!

Note: apparent omissions in this file are often due to generic `CovariantClass` lemmas being
applicable.

-/


attribute [rel_congr]
  ENNReal.add_lt_add -- tt + tt
  ENNReal.add_lt_add_left -- ff + tt
  ENNReal.add_lt_add_right -- tt + ff

/-! # <, * -/

theorem ENNReal.mul_lt_mul_left' {a b c : ENNReal} (h0 : a ≠ 0) (hinf : a ≠ ⊤) (bc : b < c) :
    a * b < a * c :=
  ENNReal.mul_left_strictMono h0 hinf bc

theorem ENNReal.mul_lt_mul_right' {a b c : ENNReal} (h0 : a ≠ 0) (hinf : a ≠ ⊤) (bc : b < c) :
    b * a < c * a :=
  mul_comm b a ▸ mul_comm c a ▸ ENNReal.mul_left_strictMono h0 hinf bc

attribute [rel_congr]
  ENNReal.mul_lt_mul -- tt * tt
  ENNReal.mul_lt_mul_left' -- ff * tt
  ENNReal.mul_lt_mul_right' -- tt * ff

/-! # ≤, / -/

attribute [rel_congr]
  ENNReal.div_le_div -- tt / tt
  ENNReal.div_le_div_left -- ff / tt
  ENNReal.div_le_div_right -- tt / ff

/-! # ≤, ⁻¹ -/

theorem ENNReal.inv_le_inv' {a b : ENNReal} (h : a ≤ b) : b⁻¹ ≤ a⁻¹ :=
  ENNReal.inv_strictAnti.antitone h

theorem ENNReal.inv_lt_inv' {a b : ENNReal} (h : a < b) : b⁻¹ < a⁻¹ := ENNReal.inv_strictAnti h

attribute [rel_congr]
  ENNReal.inv_le_inv' -- tt
  ENNReal.inv_lt_inv' -- tt

/-! # ≤, ^ -/

attribute [rel_congr]
  ENNReal.zpow_le_of_le -- ff ^ tt

/-! # <, ^ -/

theorem ENNReal.pow_lt_pow_of_lt_left {x y : ENNReal} (h : x < y) {n : ℕ} (hn : n ≠ 0) :
    x ^ n < y ^ n :=
  ENNReal.pow_strictMono hn h

attribute [rel_congr]
  ENNReal.pow_lt_pow_of_lt_left -- tt ^ ff
