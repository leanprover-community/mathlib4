import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.Compare
import Mathlib.Tactic.Ring.RingNF

open Lean Elab Tactic

elab "ring_le" : tactic => do liftMetaFinishingTactic <| Mathlib.Tactic.Ring.proveLE
elab "ring_lt" : tactic => do liftMetaFinishingTactic <| Mathlib.Tactic.Ring.proveLT

section Nat
variable {x y : ℕ}

example : 3 ≤ (3:ℕ) := by ring_le
example : 1 ≤ (3:ℕ) := by ring_le
example : 0 ≤ (3:ℕ) + 1 := by ring_le
example : x ≤ x + 3 := by ring_le
example : x ≤ 1 + x := by ring_le
example : x + y + 1 ≤ y + x + 3 := by ring_le
example : x + y ≤ y + x + 3 := by ring_le
example : x + y + 1 ≤ y + 4 + x := by ring_le

example : 1 < (3:ℕ) := by ring_lt
example : 0 < (3:ℕ) + 1 := by ring_lt
example : x < x + 3 := by ring_lt
example : x < 1 + x := by ring_lt
example : x + y + 1 < y + x + 3 := by ring_lt
example : x + y < y + x + 3 := by ring_lt
example : x + y + 1 < y + 4 + x := by ring_lt

end Nat

section LinearOrderedField
variable {K : Type*} [LinearOrderedField K] {x y : K}

example : (0:K) ≤ 0 := by ring_le
example : 3 ≤ (3:K) := by ring_le
example : 1 ≤ (3:K) := by ring_le
example : -1 ≤ (3:K) := by ring_le
example : 1.5 ≤ (3:K) := by ring_le
example : 0 ≤ x + 3 - x := by ring_le
example : -1 ≤ x - x := by ring_le
example : x + y + 1 ≤ y + x + 3 := by ring_le
example : x + y + 1 ≤ y + x + 1 := by ring_le
example : x + y ≤ y + x + 3 := by ring_le
example : x + y - 3 ≤ y + x := by ring_le
example : x + y - x + 1 ≤ y + (4:K) := by ring_le

example : 1 < (3:K) := by ring_lt
example : -1 < (3:K) := by ring_lt
example : 1.5 < (3:K) := by ring_lt
example : 0 < x + 3 - x := by ring_lt
example : -1 < x - x := by ring_lt
example : x + y + 1 < y + x + 3 := by ring_lt
example : x + y < y + x + 3 := by ring_lt
example : x + y - 3 < y + x := by ring_lt
example : x + y - x + 1 < y + (4:K) := by ring_lt

/--
error: ring failed, ring expressions not equal up to a constant
K : Type u_1
inst✝ : LinearOrderedField K
x y : K
⊢ 1 + x + y ≤ 3 + y
-/
#guard_msgs in
example : x + y + 1 ≤ y + 3 := by ring_le

/--
error: comparison failed, LHS is larger
K : Type u_1
inst✝ : LinearOrderedField K
x y : K
⊢ 4 + x + y ≤ 3 + x + y
-/
#guard_msgs in
example : x + y + 4 ≤ y + x + 3 := by ring_le

/--
error: ring failed, ring expressions not equal up to a constant
K : Type u_1
inst✝ : LinearOrderedField K
x y : K
⊢ 1 + x + y < 3 + y
-/
#guard_msgs in
example : x + y + 1 < y + 3 := by ring_lt

/--
error: comparison failed, LHS is at least as large
K : Type u_1
inst✝ : LinearOrderedField K
x y : K
⊢ 4 + x + y < 4 + x + y
-/
#guard_msgs in
example : x + y + 4 < y + x + 4 := by ring_lt

end LinearOrderedField
