import Mathlib.Tactic.LibrarySearch
import Mathlib.Topology.Algebra.Order.Compact
import Mathlib.Topology.Instances.Real

example (f : ℝ → ℝ) {K : Set ℝ} (hK : IsCompact K) : ∃ x ∈ K, ∀ y ∈ K, f x ≤ f y := by
  fail_if_success exact?
  apply? -- Verify that this includes: `refine IsCompact.exists_forall_le hK ?_ ?_`
