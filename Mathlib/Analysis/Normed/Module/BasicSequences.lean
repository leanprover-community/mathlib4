variable (𝕜 X) in
/-- A basic sequence is a sequence (e n) such that e is a Schauder basis for
    the closedlinear span of (e n). -/
def BasicSequence (e : ℕ → X) : Prop :=
    SchauderBasis 𝕜
    (Submodule.topologicalClosure (Submodule.span 𝕜 (Set.range e)))
    (fun n => ⟨e n, by
        apply Submodule.closure_subset_topologicalClosure_span
        apply subset_closure
        exact Set.mem_range_self n⟩)

namespace BasicSequence

theorem grunblum_criterion {e : ℕ → X} (K : ℝ) (hC : 1 < K)
    (h : ∀ n : ℕ, ∀ m : ℕ, m ≤ n → ∀ a : ℕ → 𝕜,
        ‖∑ i ∈ Finset.range m, a i • e i‖ ≤ K * ‖∑ i ∈ Finset.range n, a i • e i‖) :
    BasicSequence 𝕜 X e := by
    sorry

lemma exists_perpendicular_vector (S : Set (WeakDual 𝕜 X)) (h0w : 0 ∈ closure S)
    (h0ns : 0 ∉ closure (WeakDual.toStrongDual '' S)) :
     ∃ x : X, ∀ f ∈ S, f.toLinearMap x = 0 := by
    sorry

theorem basic_sequence_of_infinite_dim : ¬FiniteDimensional 𝕜 X →
    ∃ e : ℕ → X, BasicSequence 𝕜 X e := by
    sorry





end BasicSequence
