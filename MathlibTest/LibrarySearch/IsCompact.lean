import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact

-- TODO: uses sorry, but is hidden behind the `apply?`
/-- warning: declaration uses 'sorry' -/
#guard_msgs(warning, drop info) in
example (f : ℝ → ℝ) {K : Set ℝ} (_hK : IsCompact K) : ∃ x ∈ K, ∀ y ∈ K, f x ≤ f y := by
  fail_if_success exact?
  apply? -- Verify that this includes: `refine IsCompact.exists_forall_le _hK ?_ ?_`
