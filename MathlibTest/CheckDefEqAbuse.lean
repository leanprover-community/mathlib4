import Mathlib.Data.Set.BooleanAlgebra
import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.Tactic.CheckDefEqAbuse

-- This test case relies on a known defeq abuse in the `Set` lattice instances
-- (going through `Pi` rather than `setOf`). It is fine to delete once that is fixed.
-- TODO: add a self-contained test case that doesn't depend on library defeq abuse,
-- so that this file still exercises `check_defeq_abuse` after corrections land.
/--
warning: check_defeq_abuse: tactic fails with `backward.isDefEq.respectTransparency true` but succeeds with `false`.
The following isDefEq checks are the root causes of the failure:
  ❌️ (i : ℕ) → (fun a => Prop) i =?= Set ℕ
-/
#guard_msgs in
example (s : Set ℕ) (a : ℕ) (ha : a ∉ s) : Disjoint s {a} := by
  check_defeq_abuse rw [Set.disjoint_singleton_right]
  exact ha

/-- info: check_defeq_abuse: tactic succeeds with `backward.isDefEq.respectTransparency true`. No abuse detected. -/
#guard_msgs in
example (a b : ℕ) (h : a = b) : a = b := by
  check_defeq_abuse rw [h]

-- Command mode: no abuse detected
/-- info: check_defeq_abuse: command succeeds with `backward.isDefEq.respectTransparency true`. No abuse detected. -/
#guard_msgs in
#check_defeq_abuse
def myTestFun (n : ℕ) : ℕ := n + 1
