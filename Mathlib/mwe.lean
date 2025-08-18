import Mathlib

section complete

variable {E : Type*} [UniformSpace E]

variable [CompleteSpace E]

/- TVS III.8 for complete spaces -/
theorem isCompact_closure_of_totallyBounded_complete'
    {s : Set E} (ht : TotallyBounded s) : IsCompact (closure s) :=
  isCompact_of_totallyBounded_isClosed (TotallyBounded.closure ht) isClosed_closure

theorem isCompact_closedAbsConvexHull_of_totallyBounded_complete
    [AddCommGroup E] [Module ℝ E] [IsUniformAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] {s : Set E}
    (ht : TotallyBounded s) : IsCompact (closedAbsConvexHull ℝ s) := by
  exact isCompact_closedAbsConvexHull_of_totallyBounded ht

end complete
