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

variable {E : Type*} [UniformSpace E] [CompleteSpace E]

/- TVS III.8 for complete spaces -/
theorem isCompact_closure_of_totallyBounded_complete
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

section SeminormedRing



class QuasiCompleteSpace (𝕜 : Type*) (E : Type*) [Zero E] [UniformSpace E] [SeminormedRing 𝕜]
    [SMul 𝕜 E] : Prop where
  quasiComplete : ∀ ⦃s : Set E⦄, Bornology.IsVonNBounded 𝕜 s ∧ IsClosed s → IsComplete s

variable {𝕜 : Type*} {E : Type*} [UniformSpace E] [SeminormedRing 𝕜] [SMul 𝕜 E]

instance [CompleteSpace E] [Zero E] : QuasiCompleteSpace 𝕜 E where
  quasiComplete := by
    intro s ⟨hs₁, hs₂⟩
    exact IsClosed.isComplete hs₂

lemma totallyBounded_closure_of_totallyBounded {s : Set E} (ht : TotallyBounded s) :
    TotallyBounded (closure s) := by
  exact TotallyBounded.closure ht

end SeminormedRing

section NormedField

variable {E : Type*}

variable {𝕜 : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]

lemma isVonNBounded_closure_of_totallyBounded {s : Set E} (hs : TotallyBounded s) :
    Bornology.IsVonNBounded 𝕜 (closure s) :=
  TotallyBounded.isVonNBounded 𝕜 (totallyBounded_closure_of_totallyBounded hs)

variable [QuasiCompleteSpace 𝕜 E]

variable {s : Set E} (ht : TotallyBounded s)

#check QuasiCompleteSpace.quasiComplete
  ⟨isVonNBounded_closure_of_totallyBounded ht, isClosed_closure⟩

end NormedField

theorem isComplete_closure_of_totallyBounded_quasiComplete {E : Type*} {𝕜 : Type*} [NormedField 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]
    [QuasiCompleteSpace 𝕜 E] {s : Set E} (ht : TotallyBounded s) : IsComplete (closure s) :=
  QuasiCompleteSpace.quasiComplete (𝕜 := 𝕜)
    ⟨isVonNBounded_closure_of_totallyBounded ht, isClosed_closure⟩

/- TVS III.8 for complete spaces -/
theorem isCompact_closure_of_totallyBounded_quasiComplete {E : Type*} {𝕜 : Type*} [NormedField 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]
    [QuasiCompleteSpace 𝕜 E] {s : Set E} (ht : TotallyBounded s) : IsCompact (closure s) := by
  rw [isCompact_iff_totallyBounded_isComplete]
  constructor
  · exact totallyBounded_closure_of_totallyBounded ht
  · exact isComplete_closure_of_totallyBounded_quasiComplete (𝕜 := 𝕜) ht

#check TotallyBounded



end QuasiCompleteSpace
