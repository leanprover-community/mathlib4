import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.Instances.Real
import Mathlib.LinearAlgebra.Finrank
import Mathlib.Analysis.Convolution
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.SetTheory.Cardinal.CountableCover
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Data.Real.Cardinality

set_option autoImplicit false

open LinearMap Set

open BigOperators Classical Convex Pointwise Filter

universe u v

open Filter Set

open scoped Cardinal Topology


#exit

lemma foo {E : Type _} [AddCommGroup E] [Module ℝ E] (x y : E) (h : LinearIndependent ℝ ![x, y])
    (s t : ℝ) (hs : s ≠ t) : [x -[ℝ]- t • y] ∩ [x -[ℝ]- s • y] ⊆ {x} := by
  intro z ⟨hzt, hzs⟩
  rw [segment_eq_image, mem_image] at hzt hzs
  rcases hzt with ⟨p, ⟨p0, p1⟩, rfl⟩
  rcases hzs with ⟨q, ⟨q0, q1⟩, H⟩
  simp only [smul_smul] at H
  obtain rfl : q = p := by simpa using (h.eq_of_pair H).1
  rcases q0.eq_or_gt with rfl|hq0'
  · simp
  · have A : s = t := by simpa [mul_eq_mul_left_iff, hq0'.ne'] using (h.eq_of_pair H).2
    exact (hs A).elim




theorem glouglou1 {E : Type _} [TopologicalSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nontrivial E] (s : Set E) (hs : s.Countable) : Dense sᶜ := by
  exact?



theorem glouglou {E : Type _} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (h : 2 ≤ Module.rank ℝ E) (s : Set E) (hs : s.Countable) :
    IsConnected sᶜ := by
  sorry
