import Mathlib.Topology.Instances.Real
import Mathlib.Topology.Algebra.Order.Compact
import Mathlib.Tactic.LibrarySearch

/-- warning: declaration uses 'sorry'
---
warning: unused variable `hK` [linter.unusedVariables]
-/
#guard_msgs(warning) in
example (f : ℝ → ℝ) {K : Set ℝ} (hK : IsCompact K) : ∃ x ∈ K, ∀ y ∈ K, f x ≤ f y := by
  fail_if_success exact?
  apply? -- Verify that this includes: `refine IsCompact.exists_forall_le hK ?_ ?_`
