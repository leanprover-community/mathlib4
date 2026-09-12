import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.Positivity

/-! Tests for the `Nat.fib` `norm_num` extension and its companion simproc. -/

-- via the `norm_num` extension
example : Nat.fib 12 = 144 := by norm_num
example : Nat.fib 0 = 0 := by norm_num
example : Nat.fib 1 = 1 := by norm_num
example : Nat.fib 70 = 190392490709135 := by norm_num

-- via the generated simproc: these need `simp`/`grind`, which could not do them before
example : Nat.fib 12 = 144 := by simp
example : Nat.fib 12 = 144 := by grind
example : Nat.fib (10 + 2) = 144 := by simp

/-- The extension must keep normalising its own operands, because `NormNum.derive` does no
traversal of its own. Consumers that call `derive` directly (`ring`, `positivity`, ...) rely
on this; a simproc-only implementation would silently fail here. -/
example : 0 < Nat.fib (Nat.sqrt 144) := by positivity
example : Nat.fib (Nat.sqrt 144) = 144 := by norm_num
example : Nat.fib 12 + 6 = 150 := by norm_num
