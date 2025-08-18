import Mathlib

#check TotallyBounded.isVonNBounded

#check isCompact_iff_totallyBounded_isComplete

section LostInstance

variable {E : Type*}

variable (𝕜 : Type*) [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

/- Why is this needed?-/
instance : SMul 𝕜 E := Module.toDistribMulAction.toMulAction.toSMul

end LostInstance


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
  rw [closedAbsConvexHull_eq_closure_absConvexHull]
  exact isCompact_closure_of_totallyBounded_complete (totallyBounded_absConvexHull E ht)

end complete

section QuasiCompleteSpace

section NormedField

variable {E : Type*}

variable {𝕜 : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]

lemma isVonNBounded_closure_of_totallyBounded {s : Set E} (hs : TotallyBounded s) :
    Bornology.IsVonNBounded 𝕜 (closure s) :=
  TotallyBounded.isVonNBounded 𝕜 (TotallyBounded.closure hs)

variable [QuasiCompleteSpace 𝕜 E]

variable {s : Set E} (ht : TotallyBounded s)

end NormedField



/- TVS III.8 -/
theorem isCompact_closedAbsConvexHull_of_totallyBounded_quasiComplete {E : Type*}
    [AddCommGroup E] [Module ℝ E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] [QuasiCompleteSpace ℝ E] {s : Set E}
    (ht : TotallyBounded s) : IsCompact (closedAbsConvexHull ℝ s) := by
  rw [closedAbsConvexHull_eq_closure_absConvexHull]
  exact isCompact_closure_of_totallyBounded_quasiComplete (𝕜 := ℝ)
    (totallyBounded_absConvexHull E ht)

#find_home! isCompact_closedAbsConvexHull_of_totallyBounded_quasiComplete

end QuasiCompleteSpace
