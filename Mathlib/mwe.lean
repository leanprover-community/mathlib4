import Mathlib

#check TotallyBounded.isVonNBounded

#check isCompact_iff_totallyBounded_isComplete

variable (𝕜) (E : Type*)
-- variable [SeminormedRing 𝕜] [SMul 𝕜 E] [Zero E] [TopologicalSpace E]

section QuasiCompleteSpace

variable [SeminormedRing 𝕜] [SMul 𝕜 E] [UniformSpace E]

class QuasiCompleteSpace [Zero E] : Prop where
  quasiComplete : ∀ (s : Set E), Bornology.IsVonNBounded 𝕜 s ∧ IsClosed s → IsComplete s

instance [CompleteSpace E] [Zero E] : QuasiCompleteSpace 𝕜 E where
  quasiComplete := by
    intro s ⟨hs₁, hs₂⟩
    exact IsClosed.isComplete hs₂

variable {E}

/- TVS III.8 for complete spaces -/
theorem isCompact_closure_of_totallyBounded [CompleteSpace E]
    {s : Set E} (ht : TotallyBounded s) : IsCompact (closure s) :=
  isCompact_of_totallyBounded_isClosed (TotallyBounded.closure ht) isClosed_closure

end QuasiCompleteSpace


theorem isCompact_closedAbsConvexHull_of_totallyBounded {α : Type*} [UniformSpace α]
    [AddCommGroup α] [Module ℝ α] [IsUniformAddGroup α] [ContinuousSMul ℝ α] [CompleteSpace α]
    [LocallyConvexSpace ℝ α] {s : Set α}
    (ht : TotallyBounded s) : IsCompact (closedAbsConvexHull ℝ s) := by
  rw [closedAbsConvexHull_eq_closure_absConvexHull]
  exact isCompact_closure_of_totallyBounded (totallyBounded_absConvexHull α ht)
