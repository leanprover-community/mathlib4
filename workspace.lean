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

lemma le_on_closure_of_lt {E : Type u_2} [TopologicalSpace E] {f : E → ℝ} (hf : Continuous f)
    {B : Set E} {s : ℝ} (hb : ∀ x ∈ B, s < f x) : ∀ x ∈ closure B, s ≤ f x := by
  refine le_on_closure (f := fun x ↦ s) ?_ continuousOn_const (Continuous.continuousOn hf)
  · intro x hx
    simp
    linarith [hb x hx]

lemma RCLike.balanced {𝕜 : Type*} [RCLike 𝕜] {K : Set 𝕜} (Balanced_K : Balanced 𝕜 K) (x : 𝕜)
    (hx : x ∈ K) (h0 : ‖x‖ > 0) : ∀ z : 𝕜, 0 ≤ ‖z‖ ∧ ‖z‖ ≤ ‖x‖ → z ∈ K := fun z ⟨t1, t2⟩ ↦ by
  have : ‖z / x‖ ≤ 1 := by calc
    _ = ‖z‖ / ‖x‖ := by rw [norm_div]
    _ ≤ _ := (div_le_one₀ h0).mpr t2
  have ne : x ≠ 0 := fun nh ↦ by simp [nh] at h0
  simpa [ne] using balanced_iff_smul_mem.mp Balanced_K this hx

theorem closed_balanced_sep {𝕜 : Type*} [RCLike 𝕜] {r : ℝ} {K : Set 𝕜} (compact_K : IsCompact K)
    (zero_in : 0 ∈ K) (norm_lt_r : ∀ x ∈ K, ‖x‖ < r) :
    ∃ s, 0 < s ∧ s < r ∧ (∀ z ∈ K, ‖z‖ < s) := by
  set g : 𝕜 → ℝ := fun x ↦ ‖x‖ with hg
  obtain ⟨x, xin, eq⟩ : sSup (g '' K) ∈ g '' K :=
    IsCompact.sSup_mem (IsCompact.image compact_K continuous_norm) ⟨0, 0, zero_in, norm_zero⟩
  have g_le : ∀ z ∈ K, g z ≤ g x := fun z hz ↦ by
    rw [eq]
    refine le_csSup ?_ (Set.mem_image_of_mem g hz)
    exact ⟨r, fun y ⟨x, hx, _⟩ ↦ by linarith [norm_lt_r x hx]⟩
  obtain ⟨s, hs₁, hs₂⟩ : ∃ s, g x < s ∧ s < r := exists_between (by simp only [norm_lt_r x xin, g])
  exact ⟨s, by linarith [norm_nonneg x], hs₂, fun z hz ↦ by linarith [norm_lt_r x xin, g_le z hz]⟩

/-- Rudin 3.7 Theorem Suppose B is a convex, balanced, closed set in a locally convex space $X,
x_0 \in X$, but $x_0 \notin B$. Then there exists $\Lambda \in X^*$ such that $|\Lambda x| \leq 1$
for all $x \in B$, but $\Lambda x_0 > 1$. -/
theorem RCLike.geometric_hahn_b {𝕜 : Type*} {E : Type*} [TopologicalSpace E] [AddCommGroup E]
    [Module ℝ E] [RCLike 𝕜] [Module 𝕜 E] [IsScalarTower ℝ 𝕜 E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] {B : Set E} (hs₁ : Convex ℝ B) (hs₂ : IsClosed B)
    (hs₃ : Balanced 𝕜 B) (hs₄ : B.Nonempty) (x₀ : E) (hx : x₀ ∉ B) :
    ∃ (f : StrongDual 𝕜 E), (‖(f x₀)‖ > 1) ∧ ∀ b ∈ B, ‖f b‖ < 1 := by
  /- proof. Since $B$ is closed and convex, we can apply (b) of Theorem 3.4, with $A= {x_0}$,
  to obtain $\Lambda_1 \in X^*$ such that $\Lambda_1 x_0=r e^{i \theta}$ lies outside the
  closure $K$ of $\Lambda_1(B)$. -/
  obtain ⟨f, u, v, h1, h2, h3⟩ : ∃ (f : StrongDual 𝕜 E) (u v : ℝ),
      (∀ a ∈ ({x₀} : Set E), re (f a) < u) ∧ u < v ∧ ∀ b ∈ B, v < re (f b) :=
    RCLike.geometric_hahn_banach_compact_closed (convex_singleton x₀) isCompact_singleton hs₁ hs₂
      (Set.disjoint_singleton_left.mpr hx)
  have : re (f x₀) < u := h1 x₀ rfl
  have h3 : ∀ z ∈ f '' B, v < re z := fun z ⟨y, ⟨hy, eq⟩⟩ ↦ by
    rw [← eq]
    exact h3 y hy
  set K := closure (⇑f '' B)
  have notin : f x₀ ∉ K := fun h ↦ by linarith [le_on_closure_of_lt continuous_re h3 (f x₀) h]
  /- Since $B$ is balanced, so is $K$.-/
  have Balanced_K : Balanced 𝕜 K := by
    refine Balanced.closure (fun a ha _ ⟨_, ⟨⟨t, ht, _⟩, _⟩⟩ ↦ ?_)
    exact ⟨a • t, Balanced.smul_mem hs₃ ha ht, by simp_all⟩
  have zero_in : 0 ∈ K :=
    have : 0 ∈ f '' B := ⟨0, by simpa using Balanced.zero_mem hs₃ hs₄⟩
    subset_closure this
  set r := ‖f x₀‖ with hr
  have ne : f x₀ ≠ 0 := fun nh ↦ by simp [nh, zero_in] at notin
  have r_pos : r > 0 := by simp [hr, ne]
  have norm_lt_r : ∀ x ∈ K, ‖x‖ < r := fun x hx ↦ by
    by_contra! nh
    have := RCLike.balanced Balanced_K x hx (by linarith) (f x₀) ⟨norm_nonneg (f x₀), nh⟩
    contradiction
  have compact_K : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded isClosed_closure ?_
    refine (Metric.isBounded_iff_subset_ball 0 (s := K)).mpr ?_
    exact ⟨r, fun x hx ↦ mem_ball_zero_iff.mpr (norm_lt_r x hx)⟩
  /- Hence there exists $s, 0 < s < r$ , so that $|z| \leq s$ for all $z \in K$. -/
  obtain ⟨s, s_pos, s_lt, hs⟩ : ∃ s, 0 < s ∧ s < r ∧ (∀ z ∈ K, ‖z‖ < s) :=
    closed_balanced_sep compact_K zero_in norm_lt_r
  /- The functional $\Lambda=s^{-1} e^{-i \theta} \Lambda_1$ has the desired properties.-/
  use (r / (s * (f x₀))) • f
  have (x : E): ‖((r / (s * f x₀)) • f) x‖ = (r * ‖f x‖) / (s * ‖f x₀‖) := by
    have eq1 : |r| = r := abs_norm (f x₀)
    have eq2 : |s| = s := abs_of_pos s_pos
    simp [div_mul_eq_mul_div₀, eq1, eq2]
  have mul_pos : s * ‖f x₀‖ > 0 := Left.mul_pos s_pos r_pos
  constructor
  · rw [this, mul_comm]
    exact (one_lt_div₀ mul_pos).mpr ((mul_lt_mul_iff_of_pos_right r_pos).mpr s_lt)
  · intro b hb
    rw [this, hr, mul_comm, div_lt_one₀ mul_pos]
    refine (mul_lt_mul_iff_of_pos_right r_pos).mpr ?_
    exact hs (f b) (subset_closure (Set.mem_image_of_mem (⇑f) hb))
