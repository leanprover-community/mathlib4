import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

/-! # Metric conditions for continuity of functions into uniform convergence spaces.

If `X` and `β` are (pseudo) metric spaces, and `𝔖` is a set of subsets of `α`,
then a function `f : X → α →ᵤ[𝔖] β` is continuous if for each `a ∈ s ∈ 𝔖`, the
function `x ↦ f x a` is Lipschitz (with constant depending on `s`). In certain
contexts, this is a more convenient criterion for continuity of `f`.

Likewise, for `f : X → α →ᵤ β`, if `x ↦ f x a` is Lipschitz for each fixed `a : α`
(with the same Lipschitz constant), then `f` is continuous.
-/

open scoped NNReal UniformConvergence

variable {X α β : Type*} {𝔖 : Set (Set α)} [PseudoMetricSpace X] [PseudoMetricSpace β]

/-- If `f : X → α →ᵤ[𝔖] β` is Lipschitz for each fixed `a ∈ s ∈ 𝔖`, with Lipschitz
constant depending on `s`, then `f` is continuous. -/
lemma UniformOnFun.continuous_of_lipschitzWith {f : X → α →ᵤ[𝔖] β}
    (C : Set α → ℝ≥0) (hf : ∀ s ∈ 𝔖, ∀ a ∈ s, LipschitzWith (C s) (fun x ↦ toFun _ (f x) a)) :
    Continuous f := by
  simp_rw [continuous_iff_continuousAt, ContinuousAt, UniformOnFun.tendsto_iff_tendstoUniformlyOn,
    Metric.nhds_basis_closedBall.tendstoUniformlyOn_iff Metric.uniformity_basis_dist_le]
  refine fun x₀ s hs ε hε ↦ ⟨ε / (C s + 1), by positivity, fun x hx a ha ↦ ?_⟩
  simp only [Metric.mem_closedBall, dist_comm x, Function.comp_apply, Set.mem_setOf_eq] at hx ⊢
  calc
    _ ≤ C s * dist x₀ x := (hf s hs a ha).dist_le_mul _ _
    _ ≤ C s * (ε / (C s + 1)) := by gcongr
    _ ≤ ε := by
      rw [← mul_div_assoc, div_le_iff₀' (by positivity)]
      gcongr
      simp

/-- If `f : X → α →ᵤ β` is Lipschitz for each fixed `a ∈ s ∈ 𝔖`, with Lipschitz
constant depending on `s`, then `f` is continuous. -/
lemma UniformFun.continuous_of_lipschitzWith {f : X → α →ᵤ β} (C : ℝ≥0)
    (hf : ∀ a, LipschitzWith C (fun x ↦ toFun (f x) a)) :
    Continuous f := by
  let e := UniformOnFun.uniformEquivUniformFun (α := α) (𝔖 := {Set.univ}) β (by simp)
  rw [e.symm.isUniformInducing.isInducing.continuous_iff]
  apply UniformOnFun.continuous_of_lipschitzWith (fun _ ↦ C)
  rintro - - a -
  exact hf a
