/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Convergence in distribution

We introduce a definition of convergence in distribution of random variables: this is the
weak convergence of the laws of the random variables. In Mathlib terms this is a `Tendsto` in the
`ProbabilityMeasure` type.

The definition assumes that the random variables are defined on the same probability space, which
is the most common setting in applications. Convergence in distribution for random variables
on different probability spaces can be talked about using the `ProbabilityMeasure` type directly.

We also state results relating convergence in probability (`TendstoInMeasure`)
and convergence in distribution.

## Main definitions

* `TendstoInDistribution X l Z μ`: the sequence of random variables `X n` converges in
  distribution to the random variable `Z` along the filter `l` with respect to the probability
  measure `μ`.

## Main statements

* `TendstoInDistribution.continuous_comp`: **Continuous mapping theorem**.
  If `X n` tends to `Z` in distribution and `g` is continuous, then `g ∘ X n` tends to `g ∘ Z`
  in distribution.
* `tendstoInDistribution_of_tendstoInMeasure_sub`: the main technical tool for the next results.
  Let `X, Y` be two sequences of measurable functions such that `X n` converges in distribution
  to `Z`, and `Y n - X n` converges in probability to `0`.
  Then `Y n` converges in distribution to `Z`.
* `TendstoInMeasure.tendstoInDistribution`: convergence in probability implies convergence in
  distribution.
* `TendstoInDistribution.prodMk_of_tendstoInMeasure_const`: **Slutsky's theorem**.
  If `X n` converges in distribution to `Z`, and `Y n` converges in probability to a constant `c`,
  then the pair `(X n, Y n)` converges in distribution to `(Z, c)`.

-/

open Filter
open scoped Topology

namespace MeasureTheory

variable {Ω ι E : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  [TopologicalSpace E] {mE : MeasurableSpace E} {X Y : ι → Ω → E} {Z : Ω → E} {l : Filter ι}

section TendstoInDistribution

/-- Convergence in distribution of random variables.
This is the weak convergence of the laws of the random variables: `Tendsto` in the
`ProbabilityMeasure` type. -/
structure TendstoInDistribution [OpensMeasurableSpace E] (X : ι → Ω → E) (l : Filter ι) (Z : Ω → E)
    (μ : Measure Ω := by volume_tac) [IsProbabilityMeasure μ] : Prop where
  forall_aemeasurable : ∀ i, AEMeasurable (X i) μ
  aemeasurable_limit : AEMeasurable Z μ := by fun_prop
  tendsto : Tendsto (β := ProbabilityMeasure E)
      (fun n ↦ ⟨μ.map (X n), Measure.isProbabilityMeasure_map (forall_aemeasurable n)⟩) l
      (𝓝 ⟨μ.map Z, Measure.isProbabilityMeasure_map aemeasurable_limit⟩)

lemma tendstoInDistribution_const [OpensMeasurableSpace E] (hZ : AEMeasurable Z μ) :
    TendstoInDistribution (fun _ ↦ Z) l Z μ where
  forall_aemeasurable := fun _ ↦ by fun_prop
  tendsto := tendsto_const_nhds

lemma tendstoInDistribution_unique [HasOuterApproxClosed E] [BorelSpace E]
    (X : ι → Ω → E) {Z W : Ω → E} [l.NeBot]
    (h1 : TendstoInDistribution X l Z μ) (h2 : TendstoInDistribution X l W μ) :
    μ.map Z = μ.map W := by
  have h_eq := tendsto_nhds_unique h1.tendsto h2.tendsto
  rw [Subtype.ext_iff] at h_eq
  simpa using h_eq

/-- **Continuous mapping theorem**: if `X n` tends to `Z` in distribution and `g` is continuous,
then `g ∘ X n` tends to `g ∘ Z` in distribution. -/
theorem TendstoInDistribution.continuous_comp {F : Type*} [OpensMeasurableSpace E]
    [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F] {g : E → F} (hg : Continuous g)
    (h : TendstoInDistribution X l Z μ) :
    TendstoInDistribution (fun n ↦ g ∘ X n) l (g ∘ Z) μ where
  forall_aemeasurable := fun n ↦ hg.measurable.comp_aemeasurable (h.forall_aemeasurable n)
  aemeasurable_limit := hg.measurable.comp_aemeasurable h.aemeasurable_limit
  tendsto := by
    convert ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ h.tendsto hg
    · simp only [ProbabilityMeasure.map, ProbabilityMeasure.coe_mk, Subtype.mk.injEq]
      rw [AEMeasurable.map_map_of_aemeasurable hg.aemeasurable (h.forall_aemeasurable _)]
    · simp only [ProbabilityMeasure.map, ProbabilityMeasure.coe_mk]
      congr
      rw [AEMeasurable.map_map_of_aemeasurable hg.aemeasurable h.aemeasurable_limit]

end TendstoInDistribution

variable [SeminormedAddCommGroup E] [SecondCountableTopology E] [BorelSpace E]

/-- Let `X, Y` be two sequences of measurable functions such that `X n` converges in distribution
to `Z`, and `Y n - X n` converges in probability to `0`.
Then `Y n` converges in distribution to `Z`. -/
lemma tendstoInDistribution_of_tendstoInMeasure_sub
    [l.IsCountablyGenerated] (hX : ∀ i, AEMeasurable (X i) μ) (Y : ι → Ω → E) (Z : Ω → E)
    (hXZ : TendstoInDistribution X l Z μ) (hXY : TendstoInMeasure μ (fun n ↦ Y n - X n) l 0) :
    TendstoInDistribution Y l Z μ := by
  by_cases hY : ∀ i, AEMeasurable (Y i) μ
  swap; · simp [hY]
  by_cases hZ : AEMeasurable Z μ
  swap; · simp [hZ]
  rcases isEmpty_or_nonempty E with hE | hE
  · simp only [tendstoInDistribution_def hY hZ, Subsingleton.elim _ (0 : Measure E)]
    exact tendsto_const_nhds
  let x₀ : E := hE.some
  -- We show convergence in distribution by verifying the convergence of integrals of any bounded
  -- Lipschitz function `F`
  suffices ∀ (F : E → ℝ) (hF_bounded : ∃ (C : ℝ), ∀ x y, dist (F x) (F y) ≤ C)
      (hF_lip : ∃ L, LipschitzWith L F),
      Tendsto (fun n ↦ ∫ ω, F ω ∂(μ.map (Y n))) l (𝓝 (∫ ω, F ω ∂(μ.map Z))) by
    rwa [tendstoInDistribution_def hY hZ, tendsto_iff_forall_lipschitz_integral_tendsto]
  rintro F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
  have hF_cont : Continuous F := hF_lip.continuous
  -- If `F` is 0-Lipschitz, then it is constant, and all integrals are equal to that constant
  by_cases hL : L = 0
  · simp only [hL, LipschitzWith.zero_iff] at hF_lip
    specialize hF_lip x₀
    simp_rw [eq_comm (a := F x₀)] at hF_lip
    simp only [hF_lip, integral_const, smul_eq_mul]
    have h_prob n : IsProbabilityMeasure (μ.map (Y n)) := Measure.isProbabilityMeasure_map (hY n)
    have : IsProbabilityMeasure (μ.map Z) := Measure.isProbabilityMeasure_map hZ
    simp only [measureReal_univ_eq_one, one_mul]
    exact tendsto_const_nhds
  -- now `F` is `L`-Lipschitz with `L > 0`
  replace hL : 0 < L := lt_of_le_of_ne L.2 (Ne.symm hL)
  rw [Metric.tendsto_nhds]
  simp_rw [Real.dist_eq]
  suffices ∀ ε > 0, ∀ᶠ n in l, |∫ ω, F ω ∂(μ.map (Y n)) - ∫ ω, F ω ∂(μ.map Z)| < L * ε by
    intro ε hε
    specialize this (ε / L) (by positivity)
    convert this
    field_simp
  intro ε hε
  -- We cut the difference into three pieces, two of which are small by the convergence assumptions
  have h_le n : |∫ ω, F ω ∂(μ.map (Y n)) - ∫ ω, F ω ∂(μ.map Z)|
      ≤ L * (ε / 2) + M * μ.real {ω | ε / 2 ≤ ‖Y n ω - X n ω‖}
        + |∫ ω, F ω ∂(μ.map (X n)) - ∫ ω, F ω ∂(μ.map Z)| := by
    refine (dist_triangle (∫ ω, F ω ∂(μ.map (Y n))) (∫ ω, F ω ∂(μ.map (X n)))
      (∫ ω, F ω ∂(μ.map Z))).trans ?_
    gcongr
    swap; · rw [Real.dist_eq]
    rw [Real.dist_eq]
    -- `⊢ |∫ ω, F ω ∂(μ.map (Y n)) - ∫ ω, F ω ∂(μ.map (X n))|`
    -- `    ≤ L * (ε / 2) + M * μ.real {ω | ε / 2 ≤ ‖Y n ω - X n ω‖}`
    -- We prove integrability of the functions involved to be able to manipulate the integrals.
    have h_int_Y : Integrable (fun x ↦ F (Y n x)) μ := by
      refine Integrable.of_bound (by fun_prop) (‖F x₀‖ + M) (ae_of_all _ fun a ↦ ?_)
      specialize hF_bounded (Y n a) x₀
      rw [← sub_le_iff_le_add']
      exact (abs_sub_abs_le_abs_sub (F (Y n a)) (F x₀)).trans hF_bounded
    have h_int_X : Integrable (fun x ↦ F (X n x)) μ := by
      refine Integrable.of_bound (by fun_prop) (‖F x₀‖ + M) (ae_of_all _ fun a ↦ ?_)
      specialize hF_bounded (X n a) x₀
      rw [← sub_le_iff_le_add']
      exact (abs_sub_abs_le_abs_sub (F (X n a)) (F x₀)).trans hF_bounded
    have h_int_sub : Integrable (fun a ↦ ‖F (Y n a) - F (X n a)‖) μ := by
      rw [integrable_norm_iff (by fun_prop)]
      exact h_int_Y.sub h_int_X
    -- Now we prove the inequality
    rw [integral_map (by fun_prop) (by fun_prop), integral_map (by fun_prop) (by fun_prop),
      ← integral_sub h_int_Y h_int_X]
    rw [← Real.norm_eq_abs]
    calc ‖∫ a, F (Y n a) - F (X n a) ∂μ‖
    _ ≤ ∫ a, ‖F (Y n a) - F (X n a)‖ ∂μ := norm_integral_le_integral_norm _
    -- Either `‖Y n x - X n x‖` is smaller than `ε / 2`, or it is not
    _ = ∫ a in {x | ‖Y n x - X n x‖ < ε / 2}, ‖F (Y n a) - F (X n a)‖ ∂μ
        + ∫ a in {x | ε / 2 ≤ ‖Y n x - X n x‖}, ‖F (Y n a) - F (X n a)‖ ∂μ := by
      symm
      simp_rw [← not_lt]
      refine integral_add_compl₀ ?_ h_int_sub
      exact nullMeasurableSet_lt (by fun_prop) (by fun_prop)
    -- If it is smaller, we use the Lipschitz property of `F`
    -- If not, we use the boundedness of `F`.
    _ ≤ ∫ a in {x | ‖Y n x - X n x‖ < ε / 2}, L * (ε / 2) ∂μ
        + ∫ a in {x | ε / 2 ≤ ‖Y n x - X n x‖}, M ∂μ := by
      gcongr ?_ + ?_
      · refine setIntegral_mono_on₀ h_int_sub.integrableOn integrableOn_const ?_ ?_
        · exact nullMeasurableSet_lt (by fun_prop) (by fun_prop)
        · intro x hx
          simp only [Set.mem_setOf_eq] at hx
          rw [← dist_eq_norm] at hx ⊢
          exact hF_lip.dist_le_mul_of_le hx.le
      · refine setIntegral_mono h_int_sub.integrableOn integrableOn_const fun a ↦ ?_
        rw [← dist_eq_norm]
        convert hF_bounded _ _
    -- The goal is now a simple computation
    _ = L * (ε / 2) * μ.real {x | ‖Y n x - X n x‖ < ε / 2}
        + M * μ.real {ω | ε / 2 ≤ ‖Y n ω - X n ω‖} := by
      simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply, Set.univ_inter,
        smul_eq_mul]
      ring
    _ ≤ L * (ε / 2) + M * μ.real {ω | ε / 2 ≤ ‖Y n ω - X n ω‖} := by
      rw [mul_assoc]
      gcongr
      conv_rhs => rw [← mul_one (ε / 2)]
      gcongr
      exact measureReal_le_one
  -- We finally show that the right-hand side tends to `L * ε / 2`, which is smaller than `L * ε`
  have h_tendsto :
      Tendsto (fun n ↦ L * (ε / 2) + M * μ.real {ω | ε / 2 ≤ ‖Y n ω - X n ω‖}
        + |∫ ω, F ω ∂(μ.map (X n)) - ∫ ω, F ω ∂(μ.map Z)|) l (𝓝 (L * ε / 2)) := by
    suffices Tendsto (fun n ↦ L * (ε / 2) + M * μ.real {ω | ε / 2 ≤ ‖Y n ω - X n ω‖}
        + |∫ ω, F ω ∂(μ.map (X n)) - ∫ ω, F ω ∂(μ.map Z)|) l (𝓝 (L * ε / 2 + M * 0 + 0)) by
      simpa
    refine (Tendsto.add ?_ (Tendsto.const_mul _ ?_)).add ?_
    · rw [mul_div_assoc]
      exact tendsto_const_nhds
    · simp only [tendstoInMeasure_iff_norm, Pi.zero_apply, sub_zero] at hXY
      have h_tendsto := hXY (ε / 2) (by positivity) -- the result, up to `μ.real` vs `μ`
      refine Tendsto.comp ?_ h_tendsto
      exact ENNReal.tendsto_toReal (ENNReal.zero_ne_top)
    · simp_rw [tendstoInDistribution_def hX hZ,
        tendsto_iff_forall_lipschitz_integral_tendsto] at hXZ
      simpa [tendsto_iff_dist_tendsto_zero] using hXZ F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
  have h_lt : L * ε / 2 < L * ε := by
    rw [mul_div_assoc]
    gcongr
    exact half_lt_self hε
  filter_upwards [h_tendsto.eventually_lt_const h_lt] with n hn using (h_le n).trans_lt hn

/-- Convergence in probability (`TendstoInMeasure`) implies convergence in distribution
(`TendstoInDistribution`). -/
lemma TendstoInMeasure.tendstoInDistribution [l.IsCountablyGenerated]
    (h : TendstoInMeasure μ X l Z) :
    TendstoInDistribution X l Z μ := by
  by_cases hZ : AEMeasurable Z μ
  · exact tendstoInDistribution_of_tendstoInMeasure_sub (fun _ ↦ hZ) X Z tendstoInDistribution_const
      (by simpa [tendstoInMeasure_iff_norm] using h)
  · simp [hZ]

/-- **Slutsky's theorem**: if `X n` converges in distribution to `Z`, and `Y n` converges in
probability to a constant `c`, then the pair `(X n, Y n)` converges in distribution to `(Z, c)`. -/
theorem TendstoInDistribution.prodMk_of_tendstoInMeasure_const
    {E' : Type*} {mE' : MeasurableSpace E'} [SeminormedAddCommGroup E'] [SecondCountableTopology E']
    [BorelSpace E']
    [l.IsCountablyGenerated] (X : ι → Ω → E) (Y : ι → Ω → E') (Z : Ω → E)
    {c : E'} (hXZ : TendstoInDistribution X l Z μ)
    (hY : TendstoInMeasure μ (fun n ↦ Y n) l (fun _ ↦ c)) :
    TendstoInDistribution (fun n ω ↦ (X n ω, Y n ω)) l (fun ω ↦ (Z ω, c)) μ := by
  by_cases hX : ∀ i, AEMeasurable (X i) μ
  swap
  · refine tendstoInDistribution_of_not_aemeasurable_left fun hfc ↦ hX fun i ↦ ?_
    have h_eq i : X i = Prod.fst ∘ (fun ω ↦ (X i ω, c)) := by ext; simp
    rw [h_eq i]
    exact (hfc i).fst
  by_cases hZ : AEMeasurable Z μ
  swap
  · refine tendstoInDistribution_of_not_aemeasurable_right fun hgc ↦ hZ ?_
    have h_eq : Z = Prod.fst ∘ (fun ω ↦ (Z ω, c)) := by ext; simp
    rw [h_eq]
    exact hgc.fst
  refine tendstoInDistribution_of_tendstoInMeasure_sub (X := fun n ω ↦ (X n ω, c))
    (Y := fun n ω ↦ (X n ω, Y n ω)) (Z := fun ω ↦ (Z ω, c)) (μ := μ) (l := l)
    (by fun_prop) ?_ ?_
  · specialize hXZ hX hZ
    intro _ _
    rw [tendsto_iff_forall_lipschitz_integral_tendsto] at hXZ ⊢
    intro F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
    have hFc_lip : LipschitzWith L (fun x ↦ F (x, c)) := by
      refine fun x y ↦ (hF_lip (x, c) (y, c)).trans ?_
      simp [edist_eq_enorm_sub, enorm_eq_nnnorm]
    have h_eq (f : Ω → E) (hf : AEMeasurable f μ) :
        ∫ ω, F ω ∂μ.map (fun ω ↦ (f ω, c)) = ∫ ω, (fun x ↦ F (x, c)) ω ∂(μ.map f) := by
      rw [integral_map (by fun_prop), integral_map (by fun_prop)]
      · exact hFc_lip.continuous.stronglyMeasurable.aestronglyMeasurable
      · exact hF_lip.continuous.stronglyMeasurable.aestronglyMeasurable
    simp_rw [ProbabilityMeasure.coe_mk, h_eq (X _) (hX _), h_eq Z hZ]
    simpa using hXZ (fun x ↦ F (x, c)) ⟨M, fun x y ↦ hF_bounded (x, c) (y, c)⟩ ⟨L, hFc_lip⟩
  · suffices TendstoInMeasure μ (fun n ω ↦ ((0 : E), Y n ω - c)) l 0 by
      convert this with n ω
      simp
    simpa [tendstoInMeasure_iff_norm] using hY

/-- **Slutsky's theorem** for a continuous function: if `X n` converges in distribution to `Z`,
 `Y n` converges in probability to a constant `c`, and `g` is a continuous function, then
 `g (X n, Y n)` converges in distribution to `g (Z, c)`. -/
theorem TendstoInDistribution.continuous_comp_prodMk_of_tendstoInMeasure_const {E' F : Type*}
    {mE' : MeasurableSpace E'} [SeminormedAddCommGroup E'] [SecondCountableTopology E']
    [BorelSpace E']
    [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F] {g : E × E' → F} (hg : Continuous g)
    [l.IsCountablyGenerated] {X : ι → Ω → E} {Y : ι → Ω → E'}
    {c : E'} (hXZ : TendstoInDistribution X l Z μ)
    (hY_tendsto : TendstoInMeasure μ (fun n ↦ Y n) l (fun _ ↦ c))
    (hX : ∀ i, AEMeasurable (X i) μ) (hY : ∀ i, AEMeasurable (Y i) μ) (hZ : AEMeasurable Z μ) :
    TendstoInDistribution (fun n ω ↦ g (X n ω, Y n ω)) l (fun ω ↦ g (Z ω, c)) μ := by
  refine TendstoInDistribution.continuous_comp hg ?_ (by fun_prop) (by fun_prop)
  exact hXZ.prodMk_of_tendstoInMeasure_const X Y Z hY_tendsto

lemma TendstoInDistribution.add_of_tendstoInMeasure_const
    [l.IsCountablyGenerated] {c : E} (hXZ : TendstoInDistribution X l Z μ)
    (hY_tendsto : TendstoInMeasure μ (fun n ↦ Y n) l (fun _ ↦ c))
    (hX : ∀ i, AEMeasurable (X i) μ) (hY : ∀ i, AEMeasurable (Y i) μ) (hZ : AEMeasurable Z μ) :
    TendstoInDistribution (fun n ↦ X n + Y n) l (fun ω ↦ Z ω + c) μ :=
  hXZ.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun (x : E × E) ↦ x.1 + x.2) (by fun_prop) hY_tendsto hX hY hZ

end MeasureTheory
