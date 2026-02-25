import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.BooleanAlgebra
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.Tactic.CheckDefEqAbuse

-- This test case relies on a known defeq abuse in the `Set` lattice instances
-- (going through `Pi` rather than `setOf`). It is fine to delete once that is fixed.
-- TODO: add a self-contained test case that doesn't depend on library defeq abuse,
-- so that this file still exercises `#defeq_abuse` after corrections land.
/--
warning: #defeq_abuse: tactic fails with `backward.isDefEq.respectTransparency true` but succeeds with `false`.
The following isDefEq checks are the root causes of the failure:
  ❌️ (i : ℕ) → (fun a => Prop) i =?= Set ℕ
-/
#guard_msgs in
example (s : Set ℕ) (a : ℕ) (ha : a ∉ s) : Disjoint s {a} := by
  #defeq_abuse in rw [Set.disjoint_singleton_right]
  exact ha

/-- info: #defeq_abuse: tactic succeeds with `backward.isDefEq.respectTransparency true`. No abuse detected. -/
#guard_msgs in
example (a b : ℕ) (h : a = b) : a = b := by
  #defeq_abuse in rw [h]

-- Command mode: no abuse detected
/-- info: #defeq_abuse: command succeeds with `backward.isDefEq.respectTransparency true`. No abuse detected. -/
#guard_msgs in
#defeq_abuse in
def myTestFun (n : ℕ) : ℕ := n + 1

-- Command mode: synthesis failure detected
-- This test case comes from https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/backward.2EisDefEq.2ErespectTransparency/near/575690982
-- The warning output contains fvar IDs that vary between runs, so we just check it produces
-- a warning (not info or error).
#guard_msgs (drop info) in
#defeq_abuse in
instance {V : Type} [AddCommGroup V] [Module ℝ V] {l : Submodule ℝ V} :
    Module.Free ℝ l := Module.Free.of_divisionRing ℝ l
