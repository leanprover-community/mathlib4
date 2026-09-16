import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.Compare
import Mathlib.Tactic.Ring.RingNF

open Lean Elab Tactic

elab "ring_le" : tactic => liftMetaFinishingTactic Mathlib.Tactic.Ring.proveLE
elab "ring_lt" : tactic => liftMetaFinishingTactic Mathlib.Tactic.Ring.proveLT

section Nat
variable {x y : ℕ}

example : 3 ≤ (3:ℕ) := by ring_le
example : 1 ≤ (3:ℕ) := by ring_le
example : 0 ≤ (3:ℕ) + 1 := by ring_le
example : x ≤ x := by ring_le
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
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {x y : K}

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

/- The speed of `Mathlib.Tactic.Ring.proveLE` is very sensitive to how much typeclass inference is
demanded by the lemmas it orchestrates.  This example took 1112 heartbeats (and 40 ms on a good
laptop) on an implementation with "minimal" typeclasses everywhere, e.g. lots of
`CovariantClass`/`ContravariantClass`, and takes 662 heartbeats (28 ms on a good laptop) on the
implementation at the time of joining Mathlib (October 2024). -/
set_option maxHeartbeats 750 in
example : x + y - x + 1 ≤ y + (4:K) := by ring_le

/- The speed of `Mathlib.Tactic.Ring.proveLT` is very sensitive to how much typeclass inference is
demanded by the lemmas it orchestrates.  This example took 1410 heartbeats (and 48 ms on a good
laptop) on an implementation with "minimal" typeclasses everywhere, e.g. lots of
`CovariantClass`/`ContravariantClass`, and takes 676 heartbeats (28 ms on a good laptop) on the
implementation at the time of joining Mathlib (October 2024). -/
set_option maxHeartbeats 750 in
example : x + y - x + 1 < y + (4:K) := by ring_lt

/--
error: ring failed, ring expressions not equal up to an additive constant
K : Type u_1
inst✝² : Field K
inst✝¹ : LinearOrder K
inst✝ : IsStrictOrderedRing K
x y : K
⊢ 1 + x + y ≤ 3 + y
-/
#guard_msgs in
example : x + y + 1 ≤ y + 3 := by ring_le

/--
error: comparison failed, LHS is larger
K : Type u_1
inst✝² : Field K
inst✝¹ : LinearOrder K
inst✝ : IsStrictOrderedRing K
x y : K
⊢ 4 + x + y ≤ 3 + x + y
-/
#guard_msgs in
example : x + y + 4 ≤ y + x + 3 := by ring_le

/--
error: ring failed, ring expressions not equal up to an additive constant
K : Type u_1
inst✝² : Field K
inst✝¹ : LinearOrder K
inst✝ : IsStrictOrderedRing K
x y : K
⊢ 1 + x + y < 3 + y
-/
#guard_msgs in
example : x + y + 1 < y + 3 := by ring_lt

/--
error: comparison failed, LHS is at least as large
K : Type u_1
inst✝² : Field K
inst✝¹ : LinearOrder K
inst✝ : IsStrictOrderedRing K
x y : K
⊢ 4 + x + y < 4 + x + y
-/
#guard_msgs in
example : x + y + 4 < y + x + 4 := by ring_lt

end LinearOrderedField
