import Mathlib

open Function Metric Set Filter Finset Topology NNReal

open scoped LinearMap

lemma p12 {α β : Type*} [NormedAddCommGroup α] [NormedAddCommGroup β] [InnerProductSpace ℝ α]
    [InnerProductSpace ℝ β] (T : α →L[ℝ] β) {δ : ℝ} (h0 : δ > 0)
    (h : ∀ f : β →L[ℝ] ℝ , δ * ‖f‖ ≤ ‖f.comp T‖) :
    closure (T '' (Metric.ball (0 : α) 1)) ⊇ Metric.ball (0 : β) δ := fun y hy ↦ by
  have t1 : Convex ℝ (closure (T '' (Metric.ball (0 : α) 1))) :=
    Convex.is_linear_image (convex_ball 0 1) T.isBoundedLinearMap.toIsLinearMap |> .closure
  have t3 : Balanced ℝ (closure (⇑T '' Metric.ball 0 1)) := by
    refine Balanced.closure ?_
    intro _ ha _ ⟨_, ⟨_, hc, hd⟩, d⟩
    simp at d
    rw [← d, ← hd, ← ContinuousLinearMap.map_smul]
    exact Set.mem_image_of_mem (⇑T) (Balanced.smul_mem balanced_ball_zero ha hc)
  have t4 : (closure (⇑T '' Metric.ball 0 1)).Nonempty :=
    ⟨T 0, subset_closure ⟨0, by simp⟩⟩
  have : ∀ z ∉ closure (T '' (Metric.ball (0 : α) 1)), z ∉ Metric.ball (0 : β) δ := fun z hz ↦ by
    obtain ⟨f, hf1, hf2⟩ := RCLike.geometric_hahn_banach' t1 isClosed_closure t3 t4 z hz
    have ha : ∀ a ∈ Metric.closedBall (0 : α) 1, ‖f (T a)‖ < 1 := fun a ha ↦ by
      refine hf2 (T a) ((image_closure_subset_closure_image T.continuous) ?_)
      exact ⟨a, by simp [closure_ball (0 : α) (zero_ne_one' ℝ).symm, ha]⟩
    have : ‖((f : β →L[ℝ] ℝ).comp T)‖ ≤ 1 := by
      refine (f.comp T).opNorm_le_bound' (zero_le_one' ℝ) fun x hx ↦ ?_
      have xin : (1 / ‖x‖) • x ∈ Metric.closedBall 0 1 := by
        rw [mem_closedBall_zero_iff]
        simp [norm_smul_of_nonneg ?_ x, hx]
      refine le_of_lt (by calc
        _ = ‖(f.comp T) ((1 / ‖x‖) • x)‖ * ‖x‖ := by simp [field]
        _ < 1 * ‖x‖ := (mul_lt_mul_iff_of_pos_right (by positivity)).mpr (ha ((1 / ‖x‖) • x) xin))
    have : δ < ‖z‖ := by calc
      _ < δ * ‖f z‖ :=(lt_mul_iff_one_lt_right h0).mpr hf1
      _ ≤ δ * (‖f‖ * ‖z‖) := (mul_le_mul_iff_of_pos_left h0).mpr (f.le_opNorm z)
      _ ≤ ‖((f : β →L[ℝ] ℝ).comp T)‖ * ‖z‖ := by
        rw [← mul_assoc]
        refine mul_le_mul_of_nonneg_right (h f) (norm_nonneg z)
      _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right this (norm_nonneg z)
      _ = _ := by simp
    simp [le_of_lt this]
  by_contra! nh
  have := this y nh
  contradiction

/-- Following [Rudin, *Functional Analysis* (Theorem 4.12 (b) => (c))][rudin1991] -/
lemma p23 {α β : Type*} [NormedAddCommGroup α] [NormedAddCommGroup β] [InnerProductSpace ℝ α]
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

lemma p34 {α β : Type*} [NormedAddCommGroup α] [NormedAddCommGroup β] [InnerProductSpace ℝ α]
    [InnerProductSpace ℝ β] (T : α →L[ℝ] β) {δ : ℝ} (h0 : δ > 0)
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

lemma p41 {α β : Type*} [NormedAddCommGroup α] [NormedAddCommGroup β] [InnerProductSpace ℝ α]
    [InnerProductSpace ℝ β] [CompleteSpace β] [CompleteSpace α] (T : α →L[ℝ] β)
    (surj : (⇑T).Surjective) : ∃ δ > 0, ∀ f : β →L[ℝ] ℝ , δ * ‖f‖ ≤ ‖f.comp T‖ := by
  have : IsOpenMap T := ContinuousLinearMap.isOpenMap T surj
  have ho : IsOpen (T '' (ball 0 1)) := this (ball 0 1) isOpen_ball
  have : 0 ∈ T '' (ball 0 1) := by
    use 0
    simp
  rw [Metric.isOpen_iff] at ho
  obtain⟨δ, δpos, hδ⟩ : ∃ δ > 0, ball 0 δ ⊆ T '' (ball 0 1) := ho 0 this
  have : ∀ a : α , ‖T a‖ ≥ δ * ‖a‖ := by

    sorry
  use δ
  constructor
  · exact δpos
  · intro f
    rw [ContinuousLinearMap.norm_def (f.comp T)]
    apply le_csInf ?_ ?_
    · simp [Set.nonempty_def]
      use ‖f‖ * ‖T‖
      constructor
      · positivity
      · intro x
        calc
        _ ≤ ‖f‖ * ‖T x‖ := ContinuousLinearMap.le_opNorm f (T x)
        _ ≤ ‖f‖ * (‖T‖ * ‖x‖) := by
          have : ‖T x‖ ≤ ‖T‖ * ‖x‖ := ContinuousLinearMap.le_opNorm T x
          refine mul_le_mul_of_nonneg ?_ this (by positivity) (by positivity)
          simp
        _ = _ := by
          rw [mul_assoc]
    · intro c ⟨cpos, hc⟩
      have : ‖f‖ ≤ c / δ := by
        refine ContinuousLinearMap.opNorm_le_bound' f ?_ ?_
        · positivity
        · intro x ne
          obtain ⟨a, ha⟩ : ∃ a, T a = x := surj x
          rw [← ha]
          calc
          _ ≤ c * ‖a‖ := hc a
          _ ≤ _ := by

            sorry
      sorry


example {α β : Type*} [NormedAddCommGroup α] [NormedAddCommGroup β] [InnerProductSpace ℝ α]
    [InnerProductSpace ℝ β] [CompleteSpace β] [CompleteSpace α] (T : α →L[ℝ] β) : List.TFAE [
    ∃ δ > 0, ∀ f : β →L[ℝ] ℝ , δ * ‖f‖ ≤ ‖f.comp T‖,
    ∃ δ > 0, closure (T '' (Metric.ball (0 : α) 1)) ⊇ Metric.ball (0 : β) δ,
    ∃ δ > 0, T '' (Metric.ball (0 : α) 1) ⊇ Metric.ball (0 : β) δ,
    (⇑T).Surjective] := by
  tfae_have 1 → 2 := sorry
  tfae_have 2 → 3 := sorry
  tfae_have 3 → 4 := sorry
  tfae_have 4 → 1 := p41 T
  tfae_finish
