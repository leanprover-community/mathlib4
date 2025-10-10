/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Implications between different notions of convergence of measures

This file contains results relating convergence in probability (`TendstoInMeasure`)
and convergence in distribution (`Tendsto` in the `ProbabilityMeasure` type of the law of the
random variable).

## Main statements

* `tendsto_of_tendstoInMeasure_sub_of_tendsto`: the main technical tool for the next results.
  Let `f, f'` be two sequences of measurable functions such that `f n` converges in distribution
  to `g`, and `f' n - f n` converges in probability to `0`.
  Then `f' n` converges in distribution to `g`.
* `tendsto_map_of_tendstoInMeasure`: convergence in probability implies convergence in distribution.
* `tendsto_prodMk_of_tendstoInMeasure_const_of_tendsto`: **Slutsky's theorem**.
  If `f n` converges in distribution to `g`, and `f' n` converges in probability to a constant `c`,
  then the pair `(f n, f' n)` converges in distribution to `(g, c)`.

-/

open Filter
open scoped Topology

namespace MeasureTheory.ProbabilityMeasure

variable {α ι E : Type*} {m : MeasurableSpace α} [NormedAddCommGroup E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] {μ : Measure α} [IsProbabilityMeasure μ]
  {f f' : ι → α → E} {g : α → E} {l : Filter ι}

/-- Let `f, f'` be two sequences of measurable functions such that `f n` converges in distribution
to `g`, and `f' n - f n` converges in probability to `0`.
Then `f' n` converges in distribution to `g`. -/
lemma tendsto_of_tendstoInMeasure_sub_of_tendsto [l.IsCountablyGenerated]
    (hf' : ∀ i, AEMeasurable (f' i) μ) (hf : ∀ i, AEMeasurable (f i) μ)
    (hg : AEMeasurable g μ) (hff' : TendstoInMeasure μ (fun n ↦ f' n - f n) l 0)
    (hfg : Tendsto (β := ProbabilityMeasure E)
      (fun n ↦ ⟨μ.map (f n), Measure.isProbabilityMeasure_map (hf n)⟩) l
      (𝓝 ⟨μ.map g, Measure.isProbabilityMeasure_map hg⟩)) :
    Tendsto (β := ProbabilityMeasure E)
      (fun n ↦ ⟨μ.map (f' n), Measure.isProbabilityMeasure_map (hf' n)⟩) l
      (𝓝 ⟨μ.map g, Measure.isProbabilityMeasure_map hg⟩) := by
  rcases isEmpty_or_nonempty E with hE | hE
  · simp only [Subsingleton.elim _ (0 : Measure E)]
    exact tendsto_const_nhds
  let x₀ : E := hE.some
  -- We show convergence in distribution by verifying the convergence of integrals of any bounded
  -- Lipschitz function `F`
  suffices ∀ (F : E → ℝ) (hF_bounded : ∃ (C : ℝ), ∀ x y, dist (F x) (F y) ≤ C)
      (hF_lip : ∃ L, LipschitzWith L F),
      Tendsto (fun n ↦ ∫ ω, F ω ∂(μ.map (f' n))) l (𝓝 (∫ ω, F ω ∂(μ.map g))) by
    rwa [tendsto_iff_forall_lipschitz_integral_tendsto]
  rintro F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
  have hF_cont : Continuous F := hF_lip.continuous
  -- If `F` is 0-Lipschitz, then it is constant, and all integrals are equal to that constant
  by_cases hL : L = 0
  · simp only [hL, LipschitzWith.zero_iff] at hF_lip
    specialize hF_lip x₀
    simp_rw [eq_comm (a := F x₀)] at hF_lip
    simp only [hF_lip, integral_const, smul_eq_mul]
    have h_prob n : IsProbabilityMeasure (μ.map (f' n)) := Measure.isProbabilityMeasure_map (hf' n)
    have : IsProbabilityMeasure (μ.map g) := Measure.isProbabilityMeasure_map hg
    simp only [measureReal_univ_eq_one, one_mul]
    exact tendsto_const_nhds
  -- now `F` is `L`-Lipschitz with `L > 0`
  replace hL : 0 < L := lt_of_le_of_ne L.2 (Ne.symm hL)
  rw [Metric.tendsto_nhds]
  simp_rw [Real.dist_eq]
  suffices ∀ ε > 0, ∀ᶠ n in l, |∫ ω, F ω ∂(μ.map (f' n)) - ∫ ω, F ω ∂(μ.map g)| < L * ε by
    intro ε hε
    specialize this (ε / L) (by positivity)
    convert this
    field_simp
  intro ε hε
  -- We cut the difference into three pieces, two of which are small by the convergence assumptions
  have h_le n : |∫ ω, F ω ∂(μ.map (f' n)) - ∫ ω, F ω ∂(μ.map g)|
      ≤ L * (ε / 2) + M * μ.real {ω | ε / 2 ≤ ‖f' n ω - f n ω‖}
        + |∫ ω, F ω ∂(μ.map (f n)) - ∫ ω, F ω ∂(μ.map g)| := by
    refine (dist_triangle (∫ ω, F ω ∂(μ.map (f' n))) (∫ ω, F ω ∂(μ.map (f n)))
      (∫ ω, F ω ∂(μ.map g))).trans ?_
    gcongr
    swap; · rw [Real.dist_eq]
    rw [Real.dist_eq]
    -- `⊢ |∫ ω, F ω ∂(μ.map (f' n)) - ∫ ω, F ω ∂(μ.map (f n))|`
    -- `    ≤ L * (ε / 2) + M * μ.real {ω | ε / 2 ≤ ‖f' n ω - f n ω‖}`
    -- We prove integrability of the functions involved to be able to manipulate the integrals.
    have h_int_f' : Integrable (fun x ↦ F (f' n x)) μ := by
      refine Integrable.of_bound (by fun_prop) (‖F x₀‖ + M) (ae_of_all _ fun a ↦ ?_)
      specialize hF_bounded (f' n a) x₀
      rw [← sub_le_iff_le_add']
      exact (abs_sub_abs_le_abs_sub (F (f' n a)) (F x₀)).trans hF_bounded
    have h_int_f : Integrable (fun x ↦ F (f n x)) μ := by
      refine Integrable.of_bound (by fun_prop) (‖F x₀‖ + M) (ae_of_all _ fun a ↦ ?_)
      specialize hF_bounded (f n a) x₀
      rw [← sub_le_iff_le_add']
      exact (abs_sub_abs_le_abs_sub (F (f n a)) (F x₀)).trans hF_bounded
    have h_int_sub : Integrable (fun a ↦ ‖F (f' n a) - F (f n a)‖) μ := by
      rw [integrable_norm_iff (by fun_prop)]
      exact h_int_f'.sub h_int_f
    -- Now we prove the inequality
    rw [integral_map (by fun_prop) (by fun_prop), integral_map (by fun_prop) (by fun_prop),
      ← integral_sub h_int_f' h_int_f]
    rw [← Real.norm_eq_abs]
    calc ‖∫ a, F (f' n a) - F (f n a) ∂μ‖
    _ ≤ ∫ a, ‖F (f' n a) - F (f n a)‖ ∂μ := norm_integral_le_integral_norm _
    -- Either `‖f' n x - f n x‖` is smaller than `ε / 2`, or it is not
    _ = ∫ a in {x | ‖f' n x - f n x‖ < ε / 2}, ‖F (f' n a) - F (f n a)‖ ∂μ
        + ∫ a in {x | ε / 2 ≤ ‖f' n x - f n x‖}, ‖F (f' n a) - F (f n a)‖ ∂μ := by
      symm
      simp_rw [← not_lt]
      refine integral_add_compl₀ ?_ h_int_sub
      exact nullMeasurableSet_lt (by fun_prop) (by fun_prop)
    -- If it is smaller, we use the Lipschitz property of `F`
    -- If not, we use the boundedness of `F`.
    _ ≤ ∫ a in {x | ‖f' n x - f n x‖ < ε / 2}, L * (ε / 2) ∂μ
        + ∫ a in {x | ε / 2 ≤ ‖f' n x - f n x‖}, M ∂μ := by
      gcongr ?_ + ?_
      · refine setIntegral_mono_on' h_int_sub.integrableOn integrableOn_const ?_ ?_
        · exact nullMeasurableSet_lt (by fun_prop) (by fun_prop)
        · intro x hx
          simp only [Set.mem_setOf_eq] at hx
          rw [← dist_eq_norm] at hx ⊢
          exact hF_lip.dist_le_mul_of_le hx.le
      · refine setIntegral_mono h_int_sub.integrableOn integrableOn_const fun a ↦ ?_
        rw [← dist_eq_norm]
        convert hF_bounded _ _
    -- The goal is now a simple computation
    _ = L * (ε / 2) * μ.real {x | ‖f' n x - f n x‖ < ε / 2}
        + M * μ.real {ω | ε / 2 ≤ ‖f' n ω - f n ω‖} := by
      simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply, Set.univ_inter,
        smul_eq_mul]
      ring
    _ ≤ L * (ε / 2) + M * μ.real {ω | ε / 2 ≤ ‖f' n ω - f n ω‖} := by
      rw [mul_assoc]
      gcongr
      conv_rhs => rw [← mul_one (ε / 2)]
      gcongr
      exact measureReal_le_one
  -- We finally show that the right-hand side tends to `L * ε / 2`, which is smaller than `L * ε`
  have h_tendsto :
      Tendsto (fun n ↦ L * (ε / 2) + M * μ.real {ω | ε / 2 ≤ ‖f' n ω - f n ω‖}
        + |∫ ω, F ω ∂(μ.map (f n)) - ∫ ω, F ω ∂(μ.map g)|) l (𝓝 (L * ε / 2)) := by
    suffices Tendsto (fun n ↦ L * (ε / 2) + M * μ.real {ω | ε / 2 ≤ ‖f' n ω - f n ω‖}
        + |∫ ω, F ω ∂(μ.map (f n)) - ∫ ω, F ω ∂(μ.map g)|) l (𝓝 (L * ε / 2 + M * 0 + 0)) by
      simpa
    refine (Tendsto.add ?_ (Tendsto.const_mul _ ?_)).add ?_
    · rw [mul_div_assoc]
      exact tendsto_const_nhds
    · simp only [tendstoInMeasure_iff_norm, Pi.zero_apply, sub_zero] at hff'
      have h_tendsto := hff' (ε / 2) (by positivity) -- the result, up to `μ.real` vs `μ`
      refine Tendsto.comp ?_ h_tendsto
      exact ENNReal.tendsto_toReal (ENNReal.zero_ne_top)
    · simp_rw [tendsto_iff_forall_lipschitz_integral_tendsto] at hfg
      simpa [tendsto_iff_dist_tendsto_zero] using hfg F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
  have h_lt : L * ε / 2 < L * ε := by
    rw [mul_div_assoc]
    gcongr
    exact half_lt_self hε
  filter_upwards [h_tendsto.eventually_lt_const h_lt] with n hn using (h_le n).trans_lt hn

/-- Convergence in probability (`TendstoInMeasure`) implies convergence in distribution
(`Tendsto` in the `ProbabilityMeasure` type). -/
lemma tendsto_map_of_tendstoInMeasure [l.IsCountablyGenerated]
    (hf : ∀ i, AEMeasurable (f i) μ) (hg : AEMeasurable g μ) (h : TendstoInMeasure μ f l g) :
    Tendsto (β := ProbabilityMeasure E)
      (fun n ↦ ⟨μ.map (f n), Measure.isProbabilityMeasure_map (hf n)⟩) l
      (𝓝 ⟨μ.map g, Measure.isProbabilityMeasure_map hg⟩) := by
  refine ProbabilityMeasure.tendsto_of_tendstoInMeasure_sub_of_tendsto hf (fun _ ↦ hg) hg ?_
    tendsto_const_nhds
  simpa [tendstoInMeasure_iff_norm] using h

/-- **Slutsky's theorem**: if `f n` converges in distribution to `g`, and `f' n` converges in
probability to a constant `c`, then the pair `(f n, f' n)` converges in distribution to `(g, c)`. -/
lemma tendsto_prodMk_of_tendstoInMeasure_const_of_tendsto
    [l.IsCountablyGenerated] (hf' : ∀ i, AEMeasurable (f' i) μ) (hf : ∀ i, AEMeasurable (f i) μ)
    {c : E} (hg : AEMeasurable g μ) (hff' : TendstoInMeasure μ (fun n ↦ f' n) l (fun _ ↦ c))
    (hfg : Tendsto (β := ProbabilityMeasure E)
      (fun n ↦ ⟨μ.map (f n), Measure.isProbabilityMeasure_map (hf n)⟩) l
      (𝓝 ⟨μ.map g, Measure.isProbabilityMeasure_map hg⟩)) :
    Tendsto (β := ProbabilityMeasure (E × E))
      (fun n ↦ ⟨μ.map (fun ω ↦ (f n ω, f' n ω)),
        Measure.isProbabilityMeasure_map ((hf n).prodMk (hf' n))⟩) l
      (𝓝 ⟨μ.map (fun ω ↦ (g ω, c)),
        Measure.isProbabilityMeasure_map (hg.prodMk (by fun_prop))⟩) := by
  refine ProbabilityMeasure.tendsto_of_tendstoInMeasure_sub_of_tendsto (f := fun n ω ↦ (f n ω, c))
    (f' := fun n ω ↦ (f n ω, f' n ω)) (g := fun ω ↦ (g ω, c)) (μ := μ) (l := l)
    (by fun_prop) (by fun_prop) (by fun_prop) ?_ ?_
  · suffices TendstoInMeasure μ (fun n ω ↦ ((0 : E), f' n ω - c)) l 0 by
      convert this with n ω
      simp
    simpa [tendstoInMeasure_iff_norm] using hff'
  · rw [tendsto_iff_forall_lipschitz_integral_tendsto] at hfg ⊢
    intro F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
    simp only [coe_mk]
    have hFc_lip : LipschitzWith L (fun x ↦ F (x, c)) := by
      intro x y
      specialize hF_lip (x, c) (y, c)
      refine hF_lip.trans ?_
      simp [edist_eq_enorm_sub, enorm_eq_nnnorm]
    have h_eq (f : α → E) (hf : AEMeasurable f μ) :
        ∫ ω, F ω ∂μ.map (fun ω ↦ (f ω, c)) = ∫ ω, (fun x ↦ F (x, c)) ω ∂(μ.map f) := by
      rw [integral_map (by fun_prop), integral_map (by fun_prop)]
      · exact hFc_lip.continuous.stronglyMeasurable.aestronglyMeasurable
      · exact hF_lip.continuous.stronglyMeasurable.aestronglyMeasurable
    simp_rw [h_eq (f _) (hf _), h_eq g hg]
    specialize hfg (fun x ↦ F (x, c)) ⟨M, ?_⟩ ⟨L, hFc_lip⟩
    · exact fun x y ↦ hF_bounded (x, c) (y, c)
    · simpa

end MeasureTheory.ProbabilityMeasure
