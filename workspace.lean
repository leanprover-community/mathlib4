import Mathlib

/- Reference : https://www-users.cse.umn.edu/~arnold/502.s97/functional.pdf
-/

open scoped LinearMap InnerProduct

lemma adjoint_Invertible_of_Invertible {α β : Type*} [NormedAddCommGroup α] [NormedAddCommGroup β]
    [InnerProductSpace ℝ α] [InnerProductSpace ℝ β] [CompleteSpace α] [CompleteSpace β]
    (f : α →L[ℝ] β) (h : f.IsInvertible) : (f†).IsInvertible := by
  -- If $S=T^{-1}: Y \rightarrow X$ exists
  rcases h with ⟨g, hg⟩
  have eq1 := ContinuousLinearMap.adjoint_comp f g.symm.toContinuousLinearMap
  nth_rw 1 [← hg] at eq1
  simp at eq1
  have eq2 := ContinuousLinearMap.adjoint_comp g.symm.toContinuousLinearMap f
  nth_rw 1 [← hg] at eq2
  simp at eq2
  -- then $S T=I_X$ and $T S=I_Y$, so $T^* S^*=I_{X^*}$ and $S^* T^*=I_{Y^*}$
  -- which shows that $T^*$ is invertible.
  exact ContinuousLinearMap.IsInvertible.of_inverse (id (Eq.symm eq2)) (id (Eq.symm eq1))

/-- Theorem. Let $T: X \rightarrow Y$ be a bounded linear operator between Banach spaces.
Then $T$ is invertible iff $T^*$ is. -/
lemma adjoint_Invertible_iff_Invertible {α β : Type*} [NormedAddCommGroup α] [NormedAddCommGroup β]
    [InnerProductSpace ℝ α] [InnerProductSpace ℝ β] [CompleteSpace α] [CompleteSpace β]
    (f : α →L[ℝ] β) : f.IsInvertible ↔ (f†).IsInvertible := by
  constructor
  · exact fun a => adjoint_Invertible_of_Invertible f a
  · intro h
    simpa using adjoint_Invertible_of_Invertible (f†) h

lemma eq_zero_of_inner_right {α : Type*} [NormedAddCommGroup α] [InnerProductSpace ℝ α] (x : α) :
    x = 0 ↔ ∀ (y : α), inner ℝ y x = 0 := by
  constructor
  · simp_all
  · exact fun h ↦ Dense.eq_zero_of_inner_right (K := ⊤) (by simp) (fun v ↦ h v)

lemma adjoint_range_ker_complement {α β : Type*} [NormedAddCommGroup α] [NormedAddCommGroup β]
    [InnerProductSpace ℝ α] [InnerProductSpace ℝ β] [CompleteSpace α] [CompleteSpace β]
    (A : α →L[ℝ] β) : LinearMap.ker (A†) = (LinearMap.range A)ᗮ := by
  exact Eq.symm (ContinuousLinearMap.orthogonal_range A)




lemma test {α β : Type*} [NormedAddCommGroup α] [NormedAddCommGroup β]
    [InnerProductSpace ℝ α] [InnerProductSpace ℝ β] [CompleteSpace α] [CompleteSpace β]
    (A : α →L[ℝ] β) (δ : ℝ) (h : ∀ y : β, ‖(A†) y‖ ≥ δ * ‖y‖ ) :
    closure (A '' (Metric.ball 0 1)) ⊇ Metric.ball 0 δ := by
  refine Set.compl_subset_compl.mp ?_
  intro y hy
  simp at hy
  sorry

lemma ha {E : Type u_2} [TopologicalSpace E] (f : E → ℝ) (hf : Continuous f) (B : Set E) (s : ℝ)
    (hb : ∀ x ∈ B, s < f x) : ∀ x ∈ closure B, s ≤ f x := by
  refine le_on_closure (f := fun x ↦ s) ?_ continuousOn_const (Continuous.continuousOn hf)
  · intro x hx
    simp
    linarith [hb x hx]

theorem RCLike.geometric_hahn_b.{u_1, u_2} {𝕜 : Type u_1} {E : Type u_2} [TopologicalSpace E]
    [AddCommGroup E] [Module ℝ E] [RCLike 𝕜] [Module 𝕜 E] [IsScalarTower ℝ 𝕜 E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] {B : Set E}
    (hs₁ : Convex ℝ B) (hs₂ : IsClosed B) (hs₃ : Balanced ℝ B) (x₀ : E) (hx : x₀ ∉ B) :
    ∃ (f : StrongDual 𝕜 E), (‖(f x₀)‖ > 1) ∧ ∀ b ∈ B, ‖f b‖ ≤ 1 := by
  obtain ⟨f, u, v, ⟨h1, h2, h3⟩⟩ : ∃ (f : StrongDual 𝕜 E) (u v : ℝ),
      (∀ a ∈ ({x₀} : Set E), re (f a) < u) ∧ u < v ∧ ∀ b ∈ B, v < re (f b) :=
    RCLike.geometric_hahn_banach_compact_closed (t := B) (s := {x₀}) (by simp) (by simp) hs₁ hs₂
      (by simp [hx])
  have : re (f x₀) < u := h1 x₀ (by simp)
  have h3 : ∀ z ∈ f '' B, v < re z := by
    rintro z ⟨y, ⟨hy, eq⟩⟩
    rw [← eq]
    exact h3 y hy
  have : f x₀ ∉ closure (f '' B) := by
    intro h
    have : v ≤ re (f x₀) := ha (E := 𝕜) (fun x ↦ re x) continuous_re (f '' B) v h3 (f x₀) h
    linarith
  have : Balanced ℝ (closure (f '' B)) := by
    refine Balanced.closure ?_
    intro a ha z ⟨w, ⟨⟨t, ht⟩, hw⟩⟩
    simp [← ht.2] at hw
    use a • t
    constructor
    · exact Balanced.smul_mem hs₃ ha ht.1
    simp [hw]
  set K := (closure (⇑f '' B)) with hk
  set r := ‖f x₀‖
  have : ∃ s, 0 < s ∧ s < r ∧ (∀ z ∈ K, ‖z‖ < s) := by
    set g : 𝕜 → ℝ := fun x ↦ ‖x‖ with hg
    have : Continuous g := continuous_norm
    set s := sSup (g '' K) with hs
    sorry
  sorry
