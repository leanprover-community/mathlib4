/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# If an `Lp` space is complete, so is the target space
-/

@[expose] public section

open scoped ENNReal Topology
open MeasureTheory Filter ContinuousLinearMap

variable {α E : Type*} [NormedAddCommGroup E] [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}

namespace MeasureTheory

lemma FinStronglyMeasurable.exists_measurableSet_measure_pos_lt_top {f : α → E}
    (hf : FinStronglyMeasurable f μ) (h'f : ¬(f =ᵐ[μ] 0)) :
    ∃ s, MeasurableSet s ∧ 0 < μ s ∧ μ s < ∞ := by
  contrapose! h'f
  rcases hf with ⟨fn, hfn, hfn_lim⟩
  have A n : μ (Function.support (fn n)) = 0 := by
    by_contra!
    have := h'f (Function.support (fn n)) (fn n).measurableSet_support (by positivity)
    exact (lt_irrefl _ (this.trans_lt (hfn n))).elim
  have B : ∀ᵐ x ∂μ, ∀ n, fn n x = 0 := ae_all_iff.mpr A
  filter_upwards [B] with x hx
  apply tendsto_nhds_unique (hfn_lim x)
  simp [hx]

lemma AEFinStronglyMeasurable.exists_measurableSet_measure_pos_lt_top {f : α → E}
    (hf : AEFinStronglyMeasurable f μ) (h'f : ¬(f =ᵐ[μ] 0)) :
    ∃ s, MeasurableSet s ∧ 0 < μ s ∧ μ s < ∞ := by
  apply hf.finStronglyMeasurable_mk.exists_measurableSet_measure_pos_lt_top
  contrapose! h'f
  exact hf.ae_eq_mk.trans h'f

lemma foo [Nontrivial (Lp E p μ)] : Nontrivial (Lp ℝ p μ) := by



variable [NormedSpace ℝ E]

/-- If an `Lp` space is complete, then the target space is automatically complete unless the
`Lp` space is trivial. -/
lemma completeSpace_of_completeSpace_Lp  [Fact (1 ≤ p)]
    [CompleteSpace (Lp E p μ)] [Nontrivial (Lp ℝ p μ)] :
    CompleteSpace E := by
  /- Consider a nonzero function `f : α → ℝ` in `L^p`. Given a Cauchy sequence `uₙ` in `E`, form
  the Cauchy sequence `f • uₙ` in `L^p E`. By completeness, it converges. Consider a subsequence
  which converges almost everywhere. As `f` is nonzero, we get some `x` such that `f x • uₙ`
  converges along this subsequence and `f x ≠ 0`. Then `uₙ` converges along this subsequence, and
  therefore along all indices as it is Cauchy. -/
  obtain ⟨f, hf⟩ : ∃ f : Lp ℝ p μ, f ≠ 0 := exists_ne 0
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
    have : NeZero μ := by
      contrapose! hf
      simp [neZero_iff] at hf
      ext
      simp only [hf, ae_zero, ZeroMemClass.coe_zero]
      trivial
    contrapose! hf
    ext
    filter_upwards [compl_mem_ae_iff.2 hf] with y hy
    simp at hy
    simp [hy]
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
  apply tendsto_nhds_of_cauchySeq_of_subseq hu (StrictMono.tendsto_atTop hns)
  convert Tendsto.const_smul xlim (f x)⁻¹ with n
  rw [smul_smul, inv_mul_cancel₀, one_smul, Function.comp]
  exact hx
