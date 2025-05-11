import Mathlib.Analysis.SpecialFunctions.Bernstein

open Topology Filter unitInterval

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [Module ℝ E] [ContinuousSMul ℝ E] {a b : E}

namespace Path

/-- Bernstein polynomial function approximating a bundled `Path`. -/
protected noncomputable def bernsteinApproximation (p : Path a b) (n : ℕ) (hn : n ≠ 0) :
    Path a b where
  toContinuousMap := bernsteinApproximation n p.1
  source' := by simp
  target' := by simp [hn]

theorem tendsto_bernsteinApproximation [LocallyConvexSpace ℝ E] (p : Path a b) :
    Tendsto (fun n ↦ p.bernsteinApproximation (n + 1) n.succ_ne_zero) atTop (𝓝 p) := by
  rw [isInducing_toContinuousMap.tendsto_nhds_iff]
  exact (bernsteinApproximation_uniform (p : C(I, E))).comp (tendsto_add_atTop_nat 1)

end Path
