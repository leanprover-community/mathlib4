import Mathlib

open Function Metric Set

open scoped LinearMap

lemma p12 {α β : Type*} [NormedAddCommGroup α] [NormedAddCommGroup β] [InnerProductSpace ℝ α]
    [InnerProductSpace ℝ β] (T : α →L[ℝ] β) {δ : ℝ} (h0 : δ > 0)
    (h : ∀ f : β →L[ℝ] ℝ , δ * ‖f‖ ≤ ‖f.comp T‖) :
    closure (T '' (ball 0 1)) ⊇ ball 0 δ := fun y hy ↦ by
  have t1 : Convex ℝ (closure (T '' (ball 0 1))) :=
    (convex_ball 0 1).is_linear_image T.isBoundedLinearMap.toIsLinearMap |> .closure
  have t3 : Balanced ℝ (closure (⇑T '' ball 0 1)) := by
    refine Balanced.closure fun _ ha _ ⟨_, ⟨_, hc, hd⟩, d⟩ ↦ ?_
    simp only at d
    rw [← d, ← hd, ← ContinuousLinearMap.map_smul]
    exact Set.mem_image_of_mem (⇑T) (balanced_ball_zero.smul_mem ha hc)
  have t4 : (closure (⇑T '' ball 0 1)).Nonempty := ⟨T 0, subset_closure ⟨0, by simp⟩⟩
  have : ∀ z ∉ closure (T '' (ball 0 1)), z ∉ ball 0 δ := fun z hz ↦ by
    obtain ⟨f, hf1, hf2⟩ := RCLike.geometric_hahn_banach' t1 isClosed_closure t3 t4 z hz
    have ha : ∀ a ∈ closedBall (0 : α) 1, ‖f (T a)‖ < 1 := fun a ha ↦ by
      refine hf2 (T a) ((image_closure_subset_closure_image T.continuous) ?_)
      exact ⟨a, by simp [closure_ball (0 : α) (zero_ne_one' ℝ).symm, ha]⟩
    have : ‖((f : β →L[ℝ] ℝ).comp T)‖ ≤ 1 := by
      refine (f.comp T).opNorm_le_bound' (zero_le_one' ℝ) fun x hx ↦ ?_
      have xin : (1 / ‖x‖) • x ∈ closedBall 0 1 := by
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
    [InnerProductSpace ℝ β] [CompleteSpace β] [CompleteSpace α] (T : α →L[ℝ] β) {δ : ℝ}
    (h0 : δ > 0) (h : closure (T '' (ball 0 1)) ⊇ ball 0 δ) :
    T '' (ball 0 1) ⊇ ball 0 δ := by
  have int_t : interior (closure (⇑T '' ball 0 1)) ⊇ ball 0 δ :=
    (IsOpen.subset_interior_iff isOpen_ball).mpr h
  have convex_t : Convex ℝ ((T '' (ball 0 1))) :=
    (convex_ball 0 1).is_linear_image T.isBoundedLinearMap.toIsLinearMap
  have : IsOpenMap T := by
    apply T.isOpenMap'
    use 1, 0
    exact mem_interior.mpr ⟨ball 0 δ, by simpa, by simpa⟩
  have : interior (closure (⇑T '' ball 0 1)) = interior (⇑T '' ball 0 1) := by
    apply convex_t.interior_closure_eq_interior_of_nonempty_interior
    use 0
    exact mem_interior.mpr ⟨⇑T '' ball 0 1, subset_refl (T '' (ball 0 1)),
      this (ball 0 1) (isOpen_ball), by use 0; simp⟩
  rw [this] at int_t
  exact fun _ a => interior_subset (int_t a)

lemma p34 {α β : Type*} [NormedAddCommGroup α] [NormedAddCommGroup β] [InnerProductSpace ℝ α]
    [InnerProductSpace ℝ β] (T : α →L[ℝ] β) {δ : ℝ} (h0 : δ > 0)
    (h : T '' (ball 0 1) ⊇ ball 0 δ) : (⇑T).Surjective := fun y ↦ by
  by_cases ch : y = 0
  · exact ⟨0, by simp [ch]⟩
  · obtain ⟨ε, εpos, hε⟩ : ∃ ε > 0, ε < δ / ‖y‖ := exists_between (by positivity)
    have : ε • y ∈ ball 0 δ := by
      refine mem_ball_zero_iff.mpr ?_
      rwa [norm_smul, Real.norm_eq_abs, abs_of_pos εpos, mul_comm,
        ← propext (lt_div_iff₀' (norm_pos_iff.mpr ch))]
    obtain ⟨a, _, ha⟩ : ε • y ∈ T '' (ball 0 1) := h this
    use (1 / ε) • a
    simpa [ha] using inv_smul_smul₀ (ne_of_lt εpos).symm y

lemma p41 {α β : Type*} [NormedAddCommGroup α] [NormedAddCommGroup β] [InnerProductSpace ℝ α]
    [InnerProductSpace ℝ β] [CompleteSpace β] [CompleteSpace α] (T : α →L[ℝ] β)
    (surj : (⇑T).Surjective) : ∃ δ > 0, ∀ f : β →L[ℝ] ℝ , δ * ‖f‖ ≤ ‖f.comp T‖ := by
  have ho : IsOpen (T '' (ball 0 1)) := T.isOpenMap surj (ball 0 1) isOpen_ball
  rw [Metric.isOpen_iff] at ho
  obtain⟨δ, δpos, hδ⟩ : ∃ δ > 0, ball 0 δ ⊆ T '' (ball 0 1) := ho 0 ⟨0, by simp⟩
  have : ∀ a : α , ‖T a‖ ≥ δ * ‖a‖ := by
    have := closure_image_closure T.continuous (s := ball 0 1)
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
        _ ≤ _ := by
          have : ‖T x‖ ≤ ‖T‖ * ‖x‖ := ContinuousLinearMap.le_opNorm T x
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg ?_ this (by positivity) (by positivity)
          simp
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
    ∃ δ > 0, closure (T '' (ball 0 1)) ⊇ ball 0 δ,
    ∃ δ > 0, T '' (ball 0 1) ⊇ ball 0 δ,
    (⇑T).Surjective] := by
  tfae_have 1 → 2 := sorry
  tfae_have 2 → 3 := sorry
  tfae_have 3 → 4 := sorry
  tfae_have 4 → 1 := p41 T
  tfae_finish
