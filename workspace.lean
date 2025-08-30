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
  refine Submodule.ext fun x ↦ ?_
  calc
  _ ↔ (A†) x = 0 := LinearMap.mem_ker
  _ ↔ ∀ y , inner ℝ y ((A†) x) = 0 := eq_zero_of_inner_right ((ContinuousLinearMap.adjoint A) x)
  _ ↔ ∀ y , inner ℝ (A y) x = 0 := by simp [ContinuousLinearMap.adjoint_inner_right]
  _ ↔ ∀ z ∈ LinearMap.range A, inner ℝ z x = 0 := Iff.symm Set.forall_mem_range
  _ ↔ _ := (Submodule.mem_orthogonal (LinearMap.range A) x).symm
