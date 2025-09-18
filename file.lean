import Mathlib

open Function Metric Set Filter Finset Topology NNReal

/-- Following [Rudin, *Functional Analysis* (Theorem 4.12 (b) => (c))][rudin1991] -/
example {α β : Type*} [NormedAddCommGroup α] [NormedAddCommGroup β] [InnerProductSpace ℝ α]
    [InnerProductSpace ℝ β] [CompleteSpace β] [CompleteSpace α] (T : α →L[ℝ] β) {δ : ℝ} (h0 : δ > 0)
    (h : closure (T '' (Metric.ball (0 : α) 1)) ⊇ Metric.ball (0 : β) δ) :
    T '' (Metric.ball (0 : α) 1) ⊇ Metric.ball (0 : β) δ := by
  have int_t : interior (closure (⇑T '' Metric.ball 0 1)) ⊇ Metric.ball 0 δ :=
    (IsOpen.subset_interior_iff Metric.isOpen_ball).mpr h
  have convex_t : Convex ℝ ((T '' (Metric.ball (0 : α) 1))) :=
    (convex_ball 0 1).is_linear_image T.isBoundedLinearMap.toIsLinearMap
  have : IsOpenMap T := by
    apply ContinuousLinearMap.isOpenMap'
    use 1, 0
    exact mem_interior.mpr ⟨ball 0 δ, by simpa, by simpa⟩
  have : interior (closure (⇑T '' ball 0 1)) = interior (⇑T '' ball 0 1) := by
    apply Convex.interior_closure_eq_interior_of_nonempty_interior convex_t
    use 0
    exact mem_interior.mpr ⟨⇑T '' ball 0 1, by simp, this (ball 0 1) (isOpen_ball), by use 0; simp⟩
  rw [this] at int_t
  exact fun _ a => interior_subset (int_t a)

example {α β : Type*} [NormedAddCommGroup α] [NormedAddCommGroup β] [InnerProductSpace ℝ α]
    [InnerProductSpace ℝ β] [CompleteSpace β] [CompleteSpace α] (T : α →L[ℝ] β) {δ : ℝ} (h0 : δ > 0)
    (h : T '' (Metric.ball (0 : α) 1) ⊇ Metric.ball (0 : β) δ) : (⇑T).Surjective  := by
  intro y
  by_cases ch : y = 0
  · use 0
    simp [ch]
  · obtain ⟨ε, εpos, hε⟩ : ∃ ε > 0, ε < δ / ‖y‖ := by
      refine exists_between ?_
      positivity
    have : ε • y ∈ Metric.ball (0 : β) δ := by
      refine mem_ball_zero_iff.mpr ?_
      rwa [norm_smul, Real.norm_eq_abs, abs_of_pos εpos, mul_comm,
        ← propext (lt_div_iff₀' (norm_pos_iff.mpr ch))]
    obtain ⟨a, ain, ha⟩ : ε • y ∈ T '' (Metric.ball (0 : α) 1) := h this
    use (1 / ε) • a
    simpa [ha] using inv_smul_smul₀ (ne_of_lt εpos).symm y
