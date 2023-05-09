import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.RelCongr.Basic

/-! # ≡ ZMOD, + -/

attribute [rel_congr]
  Int.ModEq.add -- tt + tt
  Int.ModEq.add_left -- ff + tt
  Int.ModEq.add_right -- tt + ff

/-! # ≡ ZMOD, - -/

attribute [rel_congr]
  Int.ModEq.sub -- tt - tt
  Int.ModEq.sub_left -- ff - tt
  Int.ModEq.sub_right -- tt - ff

/-! # ≡ ZMOD, * -/

attribute [rel_congr]
  Int.ModEq.mul -- tt * tt
  Int.ModEq.mul_left -- ff * tt
  Int.ModEq.mul_right -- tt * ff

/-! # ≡ ZMOD, ^ -/

attribute [rel_congr]
  Int.ModEq.pow -- tt * ff
