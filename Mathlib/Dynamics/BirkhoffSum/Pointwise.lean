/-
Copyright (c) 2025 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis, Oliver Butterley
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
public import Mathlib.Dynamics.BirkhoffSum.Maximal
public import Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.MeasurableSpace.Invariants
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.Separation.CompletelyRegular

/-!
# Pointwise Ergodic Theorem

The Pointwise Ergodic Theorem, also known as Birkhoff's Ergodic Theorem, establishes the convergence
of time averages for dynamical systems.

Let `(α, μ)` be a probability space and `f: α → α` be a measure-preserving transformation. The
result states that, for any integrable function `φ  ∈ L¹(μ)`, the time averages
`(1/n)∑_{k=0}^{n-1} φ(f^k x)` converge almost everywhere as `n → ∞` to a limit function `φ*`.
Moreover the limit function `φ*` is essentially `f`-invariant and integrable with
`∫ φ* dμ = ∫ φ dμ`.
If the system is ergodic, then `φ*` equals the constant `∫ f dμ` almost everywhere.

The limit function `φ*` is equal to the conditional expectation of `φ` with respect to the σ-algebra
of `f`-invariant sets. This is used explicitly during this proof and also in the main statement.

## Main statements

* `ae_tendsTo_birkhoffAverage_condExp_real`: time average coincides with conditional expectation

-/

section DivergentSet

open MeasureTheory Measure MeasurableSpace Filter Topology

variable {α : Type*} {f : α → α} {g : α → ℝ} {n : ℕ} {x : α}

variable (f g) in
/-- The set of `x` where `birkhoffSumSup f g x = ⊤`. -/
def divergentSet : Set α := {x | birkhoffSumSup f g x = ⊤}

lemma divergentSet_invariant : f x ∈ divergentSet f g ↔ x ∈ divergentSet f g := by
  simp only [divergentSet, birkhoffSumSup, Set.mem_setOf_eq]
  nth_rw 2 [← sup_iSup_nat_succ]
  simp only [birkhoffSum_zero', Pi.zero_apply, EReal.coe_zero, birkhoffSum_succ', EReal.coe_add,
    max_eq_top, EReal.zero_ne_top, false_or]
  rw [← EReal.add_iSup, EReal.add_eq_top_iff_eq_top_right (by simp) (by simp)]

lemma birkhoffMax_tendsto_atTop_of_mem_divergentSet (hx : x ∈ divergentSet f g) :
    Tendsto (birkhoffMax f g · x) atTop atTop := by
  simp only [divergentSet, birkhoffSumSup, iSup_eq_top, Set.mem_setOf_eq] at hx
  refine tendsto_atTop_atTop.mpr fun b ↦ ?_
  obtain ⟨N, hN⟩ := hx b (by simp)
  norm_cast at hN
  exact ⟨N, fun n hn ↦ hN.le.trans (le_partialSups_of_le (birkhoffSum f g) hn _)⟩

/-- The difference `birkhoffMax f g (n + 1) x - birkhoffMax f g n (f x)`. -/
def birkhoffMaxDiff (f : α → α) (g : α → ℝ) (n : ℕ) (x : α) :=
  birkhoffMax f g (n + 1) x - birkhoffMax f g n (f x)

lemma birkhoffMaxDiff_aux :
    birkhoffMaxDiff f g n x = g x - (0 ⊓ (g x + birkhoffMax f g n (f x))) := by
  rw [birkhoffMaxDiff, sub_eq_sub_iff_add_eq_add, birkhoffMax_succ, max_add_min, zero_add]

lemma birkhoffMaxDiff_antitone : Antitone (birkhoffMaxDiff f g) := by
  intro m n hmn x
  simp only [birkhoffMaxDiff_aux]
  gcongr
  exact (birkhoffMax f g).mono hmn (f x)

lemma tendsTo_birkhoffMaxDiff_of_mem_divergentSet (hx : x ∈ divergentSet f g) :
    Tendsto (birkhoffMaxDiff f g · x) atTop (𝓝 (g x)) := by
  have hx' : f x ∈ divergentSet f g := divergentSet_invariant.mpr hx
  obtain ⟨N, hN⟩ :=
    tendsto_atTop_atTop.mp (birkhoffMax_tendsto_atTop_of_mem_divergentSet hx') (- g x)
  refine tendsto_atTop_of_eventually_const (i₀ := N) fun n hn ↦ ?_
  rw [birkhoffMaxDiff_aux, inf_of_le_left]
  · ring
  · simpa [add_comm] using sub_nonneg_of_le (hN n hn)

lemma limsup_birkhoffAverage_nonpos_of_notMem_divergentSet (hx : x ∉ divergentSet f g) :
    limsup (birkhoffAverage ℝ f g · x |>.toEReal) atTop ≤ 0 := by
  /- from `hx` hypothesis, the birkhoff sums are bounded above by some real `M` -/
  simp only [divergentSet, birkhoffSumSup, Set.mem_setOf_eq, iSup_eq_top, not_forall, not_exists,
    not_lt] at hx
  obtain ⟨M, hM, hbound⟩ := hx
  lift M to ℝ using ⟨hM.ne, ((EReal.bot_lt_coe _).trans_le (hbound 0)).ne'⟩
  /- hence the birkhoff averages are bounded by `M / n`, which tends to `0` -/
  refine le_of_le_of_eq (limsup_le_limsup (v := fun n : ℕ ↦ ((M / n : ℝ) : EReal)) ?_) ?_
  · refine Eventually.of_forall fun n ↦ EReal.coe_le_coe_iff.mpr ?_
    rw [birkhoffAverage, smul_eq_mul, div_eq_inv_mul]
    gcongr
    exact EReal.coe_le_coe_iff.mp (hbound n)
  · rw [← EReal.coe_zero]
    exact (EReal.tendsto_coe.mpr (tendsto_const_div_atTop_nhds_zero_nat M)).limsup_eq

variable [MeasurableSpace α] (f_meas : Measurable f) (g_meas : Measurable g) (μ : Measure α)
  (hf : MeasurePreserving f μ μ) (hg : Integrable g μ)

include f_meas g_meas in
lemma measurable_divergentSet : MeasurableSet (divergentSet f g) :=
  measurable_birkhoffSumSup f_meas g_meas (measurableSet_singleton ⊤)

include f_meas g_meas in
lemma measurable_invariants_divergentSet : MeasurableSet[invariants f] (divergentSet f g) :=
  ⟨measurable_divergentSet f_meas g_meas, funext fun _ ↦ propext divergentSet_invariant⟩

include hf hg in
@[fun_prop]
lemma integrable_birkhoffMaxDiff : Integrable (birkhoffMaxDiff f g n) μ :=
  (integrable_birkhoffMax μ hf hg).sub
    (hf.integrable_comp_of_integrable (integrable_birkhoffMax μ hf hg))

include g_meas hf hg in
lemma tendsTo_setIntegral_birkhoffMaxDiff_in_divergentSet :
    Tendsto (fun n ↦ ∫ x in divergentSet f g, birkhoffMaxDiff f g n x ∂μ) atTop
    (𝓝 <| ∫ x in divergentSet f g, g x ∂μ) := by
  apply tendsto_integral_of_dominated_convergence (abs g ⊔ abs (birkhoffMaxDiff f g 0))
    (fun _ ↦ by apply Integrable.aestronglyMeasurable; fun_prop) (by fun_prop)
  · intro n
    refine ae_of_all _ fun x ↦ ?_
    apply abs_le_max_abs_abs (by simp [birkhoffMaxDiff_aux])
      (birkhoffMaxDiff_antitone n.zero_le _)
  · exact (ae_restrict_iff' (measurable_divergentSet hf.measurable g_meas)).mpr
      (ae_of_all _ fun _ hx ↦ tendsTo_birkhoffMaxDiff_of_mem_divergentSet hx)

include g_meas hf hg in
lemma setIntegral_birkhoffMaxDiff_in_divergentSet_nonneg :
    0 ≤ ∫ x in divergentSet f g, birkhoffMaxDiff f g n x ∂μ := by
  have hres : MeasurePreserving f (μ.restrict (divergentSet f g))
      (μ.restrict (divergentSet f g)) := by
    convert! hf.restrict_preimage (measurable_divergentSet hf.measurable g_meas)
    ext
    exact divergentSet_invariant.symm
  have mi {n : ℕ} := integrable_birkhoffMax μ hf hg (n := n)
  unfold birkhoffMaxDiff
  rw [integral_sub, sub_nonneg]
  · rw [← integral_map hres.aemeasurable
      (measurable_birkhoffMax hf.measurable g_meas).aestronglyMeasurable, hres.map_eq]
    exact integral_mono mi.restrict mi.restrict ((birkhoffMax f g).monotone n.le_succ)
  · exact mi.restrict
  · exact hres.integrable_comp_of_integrable mi.restrict

include g_meas hf hg in
lemma setIntegral_in_divergentSet_nonneg : 0 ≤ ∫ x in divergentSet f g, g x ∂μ :=
  le_of_tendsto_of_tendsto' tendsto_const_nhds
    (tendsTo_setIntegral_birkhoffMaxDiff_in_divergentSet g_meas μ hf hg)
    fun _ ↦ setIntegral_birkhoffMaxDiff_in_divergentSet_nonneg g_meas μ hf hg

include g_meas hf hg in
lemma measure_divergentSet_eq_zero_of_condExp_neg [IsFiniteMeasure μ]
    (h : ∀ᵐ x ∂μ, μ[g | invariants f] x < 0) :
    μ (divergentSet f g) = 0 := by
  by_contra hm
  apply (setIntegral_in_divergentSet_nonneg g_meas μ hf hg).not_gt
  have pos : 0 ≤ᵐ[μ.restrict (divergentSet f g)] fun x ↦ -μ[g|invariants f] x :=
    ae_restrict_of_ae <| h.mono fun _ hx ↦ (neg_pos.mpr hx).le
  rw [← setIntegral_condExp (invariants_le f) hg
      (measurable_invariants_divergentSet hf.measurable g_meas),
    ← Left.neg_pos_iff, ← integral_neg,
    setIntegral_pos_iff_support_of_nonneg_ae pos integrable_condExp.restrict.neg]
  refine (pos_iff_ne_zero.mpr hm).trans_le (measure_mono_ae ?_)
  filter_upwards [h] with x hx hxd
  exact ⟨by simpa using hx.ne, hxd⟩

include g_meas hf hg in
lemma ae_tendsTo_birkhoffAverage_of_condExp_neg [IsFiniteMeasure μ]
    (h : ∀ᵐ x ∂μ, μ[g | invariants f] x < 0) :
    ∀ᵐ x ∂μ, limsup (birkhoffAverage ℝ f g · x |>.toEReal) atTop ≤ 0 := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp
    (measure_divergentSet_eq_zero_of_condExp_neg g_meas μ hf hg h)] with x
  exact limsup_birkhoffAverage_nonpos_of_notMem_divergentSet

end DivergentSet

section Real

open MeasureTheory Measure MeasurableSpace Filter Topology

variable {α : Type*} {f : α → α} {g : α → ℝ} [MeasurableSpace α] (g_meas : Measurable g)
    (μ : Measure α := by volume_tac) [IsProbabilityMeasure μ] (hf : MeasurePreserving f μ μ)
    (hg : Integrable g μ)

include g_meas hf hg in
/-- The time average is a.e., eventually not much less than the conditional expectation. -/
lemma ae_tendsTo_birkhoffAverage_sub_condExp_nonneg {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂μ, limsup
      (fun n ↦ (birkhoffAverage ℝ f g n x - (μ[g|invariants f] x + ε)).toEReal) atTop ≤ 0 := by
  -- Let `h` denote the difference between `g` and the conditional expectation of `g` plus `ε`.
  let h := g - (μ[g|invariants f] + fun _ ↦ ε)
  have h_integrable : Integrable h μ := by fun_prop
  have h_measurable : Measurable h :=
    g_meas.sub ((stronglyMeasurable_condExp.measurable.le (invariants_le f)).add measurable_const)
  -- It follows from the definition of `h` that it is a.e. equal to `-ε`.
  have h_condexp_const : μ[h|invariants f] =ᵐ[μ] - fun _ ↦ ε := calc
    _ =ᵐ[μ] μ[g|invariants f] - μ[μ[g|invariants f] + fun _ ↦ ε|invariants f] :=
      condExp_sub hg (integrable_condExp.add (integrable_const _)) _
    _ =ᵐ[μ] μ[g|invariants f] - (μ[μ[g|invariants f]|invariants f] + μ[fun _ ↦ ε|invariants f]) :=
      (condExp_add integrable_condExp (integrable_const _) _).neg.add_left
    _ =ᵐ[μ] μ[g|invariants f] - (μ[g|invariants f] + μ[fun _ ↦ ε|invariants f]) :=
      (condExp_condExp_of_le (le_of_eq rfl) (invariants_le f)).add_right.neg.add_left
    _ = - μ[fun _ ↦ ε|invariants f] := by simp
    _ = - fun _ ↦ ε := by rw [condExp_const <| invariants_le f]
  -- For typical points the time average of `h` is eventually non-negative.
  have limsup_nonpos : ∀ᵐ x ∂μ, limsup (birkhoffAverage ℝ f h · x |>.toEReal) atTop ≤ 0 := by
    suffices ∀ᵐ x ∂μ, μ[h|invariants f] x < 0 from
      ae_tendsTo_birkhoffAverage_of_condExp_neg h_measurable μ hf h_integrable this
    exact h_condexp_const.mono fun x hx ↦ by simp [hx, hε]
  -- Transfer the result on `h` to the required result on `g`.
  have hcomp : μ[g|invariants f] ∘ f = μ[g|invariants f] :=
    comp_eq_of_measurable_invariants stronglyMeasurable_condExp.measurable
  refine limsup_nonpos.mono fun x hx ↦ le_of_eq_of_le (limsup_congr ?_) hx
  filter_upwards [eventually_ne_atTop 0] with n hn
  simp [h, birkhoffAverage_sub, birkhoffAverage_add,
    birkhoffAverage_of_comp_eq ℝ (show (fun _ : α ↦ ε) ∘ f = fun _ ↦ ε from rfl) (by norm_cast),
    birkhoffAverage_of_comp_eq ℝ hcomp (by norm_cast)]

include g_meas hf hg in
/-- Same as `ae_tendsTo_birkhoffAverage_condExp_real` but assuming `Measurable g`. -/
private lemma ae_tendsTo_birkhoffAverage_condExp_aux :
    ∀ᵐ x ∂μ, Tendsto (birkhoffAverage ℝ f g · x) atTop (𝓝 (μ[g|invariants f] x)) := by
  have : ∀ᵐ x ∂μ, ∀ k : ℕ,
      ∀ᶠ n in atTop, |birkhoffAverage ℝ f g n x - μ[g|invariants f] x| < (k + 1 : ℝ)⁻¹ := by
    refine ae_all_iff.mpr fun k ↦ ?_
    let δ := (k + 1 : ℝ)⁻¹ / 2
    have hδ : 0 < δ := by positivity
    have hδ' : (0 : EReal) < δ := by norm_cast
    have p₁ := ae_tendsTo_birkhoffAverage_sub_condExp_nonneg g_meas μ hf hg hδ
    have p₂ := ae_tendsTo_birkhoffAverage_sub_condExp_nonneg g_meas.neg μ hf hg.neg hδ
    filter_upwards [p₁, p₂, condExp_neg (μ := μ) g (invariants f)] with x hx₁ hx₂ hx₃
    filter_upwards [eventually_lt_of_limsup_lt (hx₁.trans_lt hδ'),
      eventually_lt_of_limsup_lt (hx₂.trans_lt hδ')] with m hm₁ hm₂
    norm_cast at hm₁ hm₂
    simp only [birkhoffAverage_neg, Pi.neg_apply, hx₃] at hm₂
    grind
  filter_upwards [this] with x hx
  apply Metric.tendsto_atTop.mpr fun ε hε ↦ ?_
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hx k)
  exact ⟨N, fun n hn ↦ (hN n hn).trans (by rwa [one_div] at hk)⟩

include hf hg in
/-- **Pointwise Ergodic Theorem** a.k.a. **Birkhoff's Ergodic Theorem**

Time average coincides with conditional expectation for typical points. -/
public theorem ae_tendsTo_birkhoffAverage_condExp_real :
    ∀ᵐ x ∂μ, Tendsto (birkhoffAverage ℝ f g · x) atTop (𝓝 (μ[g|invariants f] x)) := by
  have g_eq : g =ᵐ[μ] hg.left.mk := hg.left.ae_eq_mk
  have h1 := condExp_congr_ae (m := invariants f) g_eq
  have h2 := ae_tendsTo_birkhoffAverage_condExp_aux hg.left.measurable_mk μ hf (hg.congr g_eq)
  have h3 := ae_all_iff.mpr <| hf.quasiMeasurePreserving.birkhoffAverage_ae_eq_of_ae_eq ℝ g_eq
  filter_upwards [h1, h2, h3] with _ h1' h2' h3'
  simp [h1', h2', h3']

end Real
