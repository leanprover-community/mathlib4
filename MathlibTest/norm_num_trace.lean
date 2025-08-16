import Mathlib.Tactic.NormNum.Basic

/-!
# Tests of `norm_num` trace nodes

These tests should be updated without much thought, unless a change specifically is targetting the
trace format. In those cases, it is best to temporarily uncomment `#guard_msgs` and check the trace
nodes behave correctly in the infoview. -/

set_option trace.Tactic.norm_num true
-- proofs would make this unstable (and hard to read)
set_option pp.proofs false
-- print shorter names
open Mathlib.Meta.NormNum

/--
trace:
[Tactic.norm_num] ✅️ evalMul
  [Tactic.norm_num] ✅️ evalOfNat
    [Tactic.norm_num] 2 ⇒ isNat 2 (⋯)
  [Tactic.norm_num] ✅️ evalAdd
    [Tactic.norm_num] ✅️ evalOfNat
      [Tactic.norm_num] 1 ⇒ isNat 1 (⋯)
    [Tactic.norm_num] ✅️ evalOfNat
      [Tactic.norm_num] 1 ⇒ isNat 1 (⋯)
    [Tactic.norm_num] 1 + 1 ⇒ isNat 2 (⋯)
  [Tactic.norm_num] 2 * (1 + 1) ⇒ isNat 4 (⋯)
[Tactic.norm_num] ✅️ evalTrue
  [Tactic.norm_num] True ⇒ isTrue (True.intro)
-/
#guard_msgs in
example : 2 * (1 + 1) = 4 := by
  norm_num

set_option linter.unusedTactic false in
/--
trace: [Tactic.norm_num] ❌️ evalMul
  [Tactic.norm_num] ✅️ evalOfNat
    [Tactic.norm_num] 2 ⇒ isNat 2 (⋯)
  [Tactic.norm_num] ❌️ evalAdd
    [Tactic.norm_num] ✅️ evalOfNat
      [Tactic.norm_num] 1 ⇒ isNat 1 (⋯)
    [Tactic.norm_num] 1 + x ⇒ x: no norm_nums apply
  [Tactic.norm_num] 2 * (1 + x) ⇒ 1 + x: no norm_nums apply
[Tactic.norm_num] ❌️ evalAdd
  [Tactic.norm_num] ✅️ evalOfNat
    [Tactic.norm_num] 1 ⇒ isNat 1 (⋯)
  [Tactic.norm_num] 1 + x ⇒ x: no norm_nums apply
[Tactic.norm_num] ❌️ evalAdd
  [Tactic.norm_num] ✅️ evalOfNat
    [Tactic.norm_num] 1 ⇒ isNat 1 (⋯)
  [Tactic.norm_num] 1 + x ⇒ x: no norm_nums apply
[Tactic.norm_num] ❌️ evalMul
  [Tactic.norm_num] ✅️ evalOfNat
    [Tactic.norm_num] 2 ⇒ isNat 2 (⋯)
  [Tactic.norm_num] ❌️ evalAdd
    [Tactic.norm_num] ✅️ evalOfNat
      [Tactic.norm_num] 1 ⇒ isNat 1 (⋯)
    [Tactic.norm_num] 1 + x ⇒ x: no norm_nums apply
  [Tactic.norm_num] 2 * (1 + x) ⇒ 1 + x: no norm_nums apply
[Tactic.norm_num] ❌️ evalAdd
  [Tactic.norm_num] ✅️ evalOfNat
    [Tactic.norm_num] 2 ⇒ isNat 2 (⋯)
  [Tactic.norm_num] ❌️ evalMul
    [Tactic.norm_num] ✅️ evalOfNat
      [Tactic.norm_num] 2 ⇒ isNat 2 (⋯)
    [Tactic.norm_num] 2 * x ⇒ x: no norm_nums apply
  [Tactic.norm_num] 2 + 2 * x ⇒ 2 * x: no norm_nums apply
[Tactic.norm_num] ❌️ evalMul
  [Tactic.norm_num] ✅️ evalOfNat
    [Tactic.norm_num] 2 ⇒ isNat 2 (⋯)
  [Tactic.norm_num] 2 * x ⇒ x: no norm_nums apply
[Tactic.norm_num] ❌️ evalMul
  [Tactic.norm_num] ✅️ evalOfNat
    [Tactic.norm_num] 2 ⇒ isNat 2 (⋯)
  [Tactic.norm_num] 2 * x ⇒ x: no norm_nums apply
[Tactic.norm_num] ❌️ evalAdd
  [Tactic.norm_num] ✅️ evalOfNat
    [Tactic.norm_num] 2 ⇒ isNat 2 (⋯)
  [Tactic.norm_num] ❌️ evalMul
    [Tactic.norm_num] ✅️ evalOfNat
      [Tactic.norm_num] 2 ⇒ isNat 2 (⋯)
    [Tactic.norm_num] 2 * x ⇒ x: no norm_nums apply
  [Tactic.norm_num] 2 + 2 * x ⇒ 2 * x: no norm_nums apply
-/
#guard_msgs in
example (x : ℕ) : 2 * (1 + x) = 2 + 2 * x := by
  norm_num
  rw [mul_add]
