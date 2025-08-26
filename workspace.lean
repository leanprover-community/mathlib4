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
    have := adjoint_Invertible_of_Invertible (f†) h
    simpa using this

lemma adjoint_range_ker_complement {α β : Type*} [NormedAddCommGroup α] [NormedAddCommGroup β]
    [InnerProductSpace ℝ α] [InnerProductSpace ℝ β] [CompleteSpace α] [CompleteSpace β]
    (A : α →L[ℝ] β) : LinearMap.range (A†) = (LinearMap.ker A)ᗮ := by
  sorry
