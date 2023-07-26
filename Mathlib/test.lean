import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

open LinearMap Set

open BigOperators Classical Convex Pointwise


#exit


lemma foo {E : Type _} [AddCommGroup E] [Module ℝ E] (x y : E) (h : LinearIndependent ℝ ![x, y])
    (s t : ℝ) (hs : s ≠ t) : [x -[ℝ]- t • y] ∩ [x -[ℝ]- s • y] ⊆ {x} := by
  intro z ⟨hzt, hzs⟩
  rw [segment_eq_image, mem_image] at hzt hzs
  rcases hzt with ⟨p, ⟨p0, p1⟩, rfl⟩
  rcases hzs with ⟨q, ⟨q0, q1⟩, H⟩
  have : (p - q) • x + (p * t - q * s) • y = 0 := by
    rw [← sub_eq_zero_of_eq H, ← sub_eq_zero]
    simp [sub_smul, smul_smul]
    abel



  simp [sub_smul] at T
