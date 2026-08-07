/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# If an `Lp` space is complete, so is the target space
-/

@[expose] public section

open scoped ENNReal Topology
open Filter ContinuousLinearMap

namespace MeasureTheory

variable {α E : Type*} [NormedAddCommGroup E] {mα : MeasurableSpace α} {p : ℝ≥0∞} {μ : Measure α}

variable [NormedSpace ℝ E]

variable (E p μ) in
/-- If an `L^p` space is complete and nontrivial, then the target space is complete. -/
lemma completeSpace_of_completeSpace_Lp [hp : Fact (1 ≤ p)]
    [CompleteSpace (Lp E p μ)] [Nontrivial (Lp E p μ)] : CompleteSpace E := by
  /- Consider a nonzero function `f : α → ℝ` in `L^p`. Given a Cauchy sequence `uₙ` in `E`, form
  the Cauchy sequence `f • uₙ` in `L^p E`. By completeness, it converges. Consider a subsequence
  which converges almost everywhere. As `f` is nonzero, we get some `x` such that `f x • uₙ`
  converges along this subsequence and `f x ≠ 0`. Then `uₙ` converges along this subsequence, and
  therefore along all indices as it is Cauchy. -/
  obtain ⟨f, hf⟩ : ∃ f : Lp ℝ p μ, f ≠ 0 := by
    have : Nontrivial (Lp ℝ p μ) :=
      nontrivial_Lp_real_of_nontrivial_Lp (E := E) (p := p) (μ := μ)
    exact exists_ne 0
  let m : E →L[ℝ] Lp E p μ := ((ContinuousLinearMap.lsmul ℝ ℝ).flip.compLpL₂ p μ).flip f
  apply Metric.complete_of_cauchySeq_tendsto (fun u hu ↦ ?_)
  obtain ⟨g, hg⟩ : ∃ g, Tendsto (m ∘ u) atTop (𝓝 g) :=
    cauchySeq_tendsto_of_complete (m.lipschitz.cauchySeq_comp hu)
  let f' : ℕ → (α → E) := fun n ↦ (m ∘ u) n
  obtain ⟨ns, hns, nslim⟩ : ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂μ, Tendsto (fun i ↦ f' (ns i) x) atTop (𝓝 (g x)) :=
    (tendstoInMeasure_of_tendsto_Lp hg).exists_seq_tendsto_ae
  have : (ae (μ.restrict (Function.support f))).NeBot := by
    apply ae_restrict_neBot.2
    apply μ.measure_support_eq_zero_iff.not.2
    contrapose! hf
    ext
    grw [Lp.coeFn_zero]
    exact hf
  have A : ∀ᵐ x ∂(μ.restrict (Function.support f)),
    Tendsto (fun i ↦ f' (ns i) x) atTop (𝓝 (g x)) := ae_restrict_of_ae nslim
  have B : ∀ᵐ x ∂(μ.restrict (Function.support f)), x ∈ Function.support f :=
    ae_restrict_mem (measurableSet_support (by fun_prop))
  have C : ∀ᵐ x ∂(μ.restrict (Function.support f)), ∀ n, m (u n) x = (f x) • u n := by
    apply ae_restrict_of_ae
    apply ae_all_iff.2 (fun n ↦ ?_)
    filter_upwards [(toSpanSingleton ℝ (u n)).coeFn_compLp f] with x hx using by simp [m, hx]
  obtain ⟨x, xlim, hx, hmx⟩ : ∃ x, Tendsto (fun i ↦ f' (ns i) x) atTop (𝓝 (g x))
    ∧ x ∈ Function.support f ∧ ∀ n, m (u n) x = (f x) • u n := (A.and (B.and C)).exists
  simp only [Function.comp_apply, hmx, f'] at xlim
  refine ⟨(f x)⁻¹ • g x, ?_⟩
  apply tendsto_nhds_of_cauchySeq_of_subseq hu hns.tendsto_atTop
  convert xlim.const_smul (f x)⁻¹ with n
  rw [smul_smul, inv_mul_cancel₀, one_smul, Function.comp]
  exact hx

end MeasureTheory
