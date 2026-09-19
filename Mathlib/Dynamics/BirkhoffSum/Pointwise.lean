/-
Copyright (c) 2025 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis, Oliver Butterley
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
public import Mathlib.Dynamics.BirkhoffSum.Maximal
public import Mathlib.Dynamics.BirkhoffSum.NormedSpace
public import Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.MeasurableSpace.Invariants
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.Separation.CompletelyRegular

/-!
# Pointwise Ergodic Theorem

The Pointwise Ergodic Theorem, also known as Birkhoff's Ergodic Theorem, establishes the pointwise
convergence of time averages for dynamical systems.

Let `(α, μ)` be a probability space and `f : α → α` be a measure-preserving transformation. The
result states that for any integrable function `φ ∈ L¹(μ)`, the Birkhoff averages
`(1/n)∑_{k=0}^{n-1} φ(f^k x)` converge almost everywhere as `n → ∞` to a limit function `φ*`, which
can be chosen to be the conditional expectation of `φ` with respect to the σ-algebra of
`f`-invariant sets. This chosen limit is strictly `f`-invariant and also integrable with
`∫ φ* dμ = ∫ φ dμ` (see `MeasureTheory.integral_condExp`).

## Main statements

* `ae_tendsTo_birkhoffAverage_condExp`: for an integrable function with values in a Banach space,
  the time average coincides almost everywhere with the conditional expectation with respect to
  the σ-algebra of invariant sets.
-/

section DivergentSet

open MeasureTheory Measure MeasurableSpace Filter Topology

attribute [local fun_prop] MeasurePreserving.integrable_comp_of_integrable

variable {α : Type*} {f : α → α} {g : α → ℝ} {n : ℕ} {x : α}

variable (f g) in
/-- The set of `x` where `birkhoffSumSup f g x = ⊤`. -/
def divergentSet : Set α := {x | birkhoffSumSup f g x = ⊤}

lemma divergentSet_invariant : f x ∈ divergentSet f g ↔ x ∈ divergentSet f g := by
  simp only [divergentSet, birkhoffSumSup, Set.mem_ofPred_eq]
  conv_rhs => rw [← sup_iSup_nat_succ]
  simp only [birkhoffSum_apply_zero, EReal.coe_zero, birkhoffSum_apply_succ', EReal.coe_add,
    max_eq_top, EReal.zero_ne_top, false_or, ← EReal.add_iSup]
  rw [EReal.add_eq_top_iff_eq_top_right (by simp) (by simp)]

lemma birkhoffMax_tendsto_atTop_of_mem_divergentSet (hx : x ∈ divergentSet f g) :
    Tendsto (birkhoffMax f g · x) atTop atTop := by
  simp only [divergentSet, birkhoffSumSup, iSup_eq_top, Set.mem_ofPred_eq] at hx
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
  simp_rw [birkhoffMaxDiff_aux]
  gcongr

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
  simp only [divergentSet, birkhoffSumSup, Set.mem_ofPred_eq, iSup_eq_top, not_forall, not_exists,
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

variable [MeasurableSpace α] (μ : Measure α)

lemma measurable_divergentSet (hf : Measurable f) (hg : Measurable g) :
    MeasurableSet (divergentSet f g) :=
  measurable_birkhoffSumSup hf hg (measurableSet_singleton ⊤)

lemma measurable_invariants_divergentSet (hf : Measurable f) (hg : Measurable g) :
    MeasurableSet[invariants f] (divergentSet f g) :=
  ⟨measurable_divergentSet hf hg, funext fun _ ↦ propext divergentSet_invariant⟩

@[fun_prop]
lemma integrable_birkhoffMaxDiff (hf : MeasurePreserving f μ μ) (hg : Integrable g μ) :
    Integrable (birkhoffMaxDiff f g n) μ := by
  fun_prop [birkhoffMaxDiff]

lemma tendsTo_setIntegral_birkhoffMaxDiff_in_divergentSet (g_meas : Measurable g)
    (hf : MeasurePreserving f μ μ) (hg : Integrable g μ) :
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

lemma setIntegral_birkhoffMaxDiff_in_divergentSet_nonneg (g_meas : Measurable g)
    (hf : MeasurePreserving f μ μ) (hg : Integrable g μ) :
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
  · fun_prop

lemma setIntegral_in_divergentSet_nonneg (g_meas : Measurable g) (hf : MeasurePreserving f μ μ)
    (hg : Integrable g μ) : 0 ≤ ∫ x in divergentSet f g, g x ∂μ :=
  le_of_tendsto_of_tendsto' tendsto_const_nhds
    (tendsTo_setIntegral_birkhoffMaxDiff_in_divergentSet μ g_meas hf hg)
    fun _ ↦ setIntegral_birkhoffMaxDiff_in_divergentSet_nonneg μ g_meas hf hg

lemma measure_divergentSet_eq_zero_of_condExp_neg [IsFiniteMeasure μ] (g_meas : Measurable g)
    (hf : MeasurePreserving f μ μ) (hg : Integrable g μ)
    (h : ∀ᵐ x ∂μ, μ[g | invariants f] x < 0) :
    μ (divergentSet f g) = 0 := by
  by_contra hm
  apply (setIntegral_in_divergentSet_nonneg μ g_meas hf hg).not_gt
  have pos : 0 ≤ᵐ[μ.restrict (divergentSet f g)] fun x ↦ -μ[g|invariants f] x :=
    ae_restrict_of_ae <| h.mono fun _ hx ↦ (neg_pos.mpr hx).le
  rw [← setIntegral_condExp (invariants_le f) hg
      (measurable_invariants_divergentSet hf.measurable g_meas),
    ← Left.neg_pos_iff, ← integral_neg,
    setIntegral_pos_iff_support_of_nonneg_ae pos integrable_condExp.restrict.neg]
  refine (pos_iff_ne_zero.mpr hm).trans_le (measure_mono_ae ?_)
  filter_upwards [h] with x hx hxd
  exact ⟨by simpa using hx.ne, hxd⟩

lemma ae_limsup_birkhoffAverage_nonpos_of_condExp_neg [IsFiniteMeasure μ]
    (hf : MeasurePreserving f μ μ) (hg : Integrable g μ)
    (h : ∀ᵐ x ∂μ, μ[g | invariants f] x < 0) :
    ∀ᵐ x ∂μ, limsup (birkhoffAverage ℝ f g · x |>.toEReal) atTop ≤ 0 := by
  -- Replace `g` by an a.e. equal measurable representative `g'`.
  set g' := hg.aemeasurable.mk g
  have g_eq : g =ᵐ[μ] g' := hg.aemeasurable.ae_eq_mk
  have h' : ∀ᵐ x ∂μ, μ[g' | invariants f] x < 0 := by
    filter_upwards [condExp_congr_ae g_eq, h] with x hx₁ hx₂
    rwa [← hx₁]
  have hae := ae_all_iff.mpr <| hf.quasiMeasurePreserving.birkhoffAverage_ae_eq_of_ae_eq ℝ g_eq
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (measure_divergentSet_eq_zero_of_condExp_neg
    μ hg.aemeasurable.measurable_mk hf (hg.congr g_eq) h'), hae] with x hx hx'
  exact le_of_eq_of_le (limsup_congr <| Eventually.of_forall fun n ↦ by rw [hx' n])
    (limsup_birkhoffAverage_nonpos_of_notMem_divergentSet hx)

end DivergentSet

section Real

open MeasureTheory Measure MeasurableSpace Filter Topology

variable {α : Type*} {f : α → α} {g : α → ℝ} [MeasurableSpace α]
    (μ : Measure α := by volume_tac) [IsProbabilityMeasure μ]

lemma ae_tendsTo_birkhoffAverage_sub_condExp_nonneg (hf : MeasurePreserving f μ μ)
    (hg : Integrable g μ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂μ,
    limsup (birkhoffAverage ℝ f g · x - (μ[g|invariants f] x + ε) |>.toEReal) atTop ≤ 0 := by
  let h x := g x - (μ[g|invariants f] x + ε)
  have const_condExp_h : μ[h|invariants f] =ᵐ[μ] - fun _ ↦ ε :=
    calc
      _ =ᵐ[μ] μ[g|invariants f] - μ[μ[g|invariants f] + fun _ ↦ ε|invariants f] :=
        condExp_sub hg (by fun_prop) _
      _ =ᵐ[μ] μ[g|invariants f] - (μ[g|invariants f] + μ[fun _ ↦ ε|invariants f]) := by
        grw [condExp_add integrable_condExp (integrable_const _),
          condExp_condExp_of_le (le_of_eq rfl) (invariants_le f)]
      _ = - μ[fun _ ↦ ε|invariants f] := by
        ring
      _ = - fun _ ↦ ε := by
        rw [condExp_const (invariants_le f)]
  have limsup_nonpos : ∀ᵐ x ∂μ, limsup (birkhoffAverage ℝ f h · x |>.toEReal) atTop ≤ 0 := by
    apply ae_limsup_birkhoffAverage_nonpos_of_condExp_neg μ hf (by fun_prop)
    exact const_condExp_h.mono fun x hx ↦ by simp [hx, hε]
  have hcomp : μ[g|invariants f] ∘ f = μ[g|invariants f] :=
    comp_eq_of_measurable_invariants stronglyMeasurable_condExp.measurable
  filter_upwards [limsup_nonpos] with x hx
  refine le_of_eq_of_le (limsup_congr ?_) hx
  filter_upwards [eventually_ne_atTop 0] with n hn
  simp_rw [h, fun_birkhoffAverage_sub, fun_birkhoffAverage_add,
    birkhoffAverage_of_comp_eq ℝ (show (fun _ ↦ ε) ∘ f = fun _ ↦ ε from rfl) (by norm_cast),
    birkhoffAverage_of_comp_eq ℝ hcomp (by norm_cast)]

theorem ae_tendsTo_birkhoffAverage_condExp_real (hf : MeasurePreserving f μ μ)
    (hg : Integrable g μ) :
    ∀ᵐ x ∂μ, Tendsto (birkhoffAverage ℝ f g · x) atTop (𝓝 (μ[g|invariants f] x)) := by
  have : ∀ᵐ x ∂μ, ∀ k : ℕ,
      ∀ᶠ n in atTop, |birkhoffAverage ℝ f g n x - μ[g|invariants f] x| < (k + 1 : ℝ)⁻¹ := by
    refine ae_all_iff.mpr fun k ↦ ?_
    let δ := (k + 1 : ℝ)⁻¹ / 2
    have hδ : 0 < δ := by positivity
    have hδ' : (0 : EReal) < δ := by norm_cast
    have p₁ := ae_tendsTo_birkhoffAverage_sub_condExp_nonneg μ hf hg hδ
    have p₂ := ae_tendsTo_birkhoffAverage_sub_condExp_nonneg μ hf hg.neg hδ
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

end Real

section NormedAddCommGroup

open MeasureTheory Measure MeasurableSpace Filter Topology

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f : α → α} {g : α → E}

/-- The set of points where the Birkhoff average is `ε`-away from the conditional expectation for
infinitely many `n`. -/
def birkhoffExceptionalSet (μ : Measure α) (f : α → α) (g : α → E) (ε : ℝ) : Set α :=
  {x | ∃ᶠ n in atTop, ε ≤ dist (birkhoffAverage ℝ f g n x) (μ[g|invariants f] x)}

/-- The exceptional set for a fixed `ε` has measure at most `2 * δ / ε` whenever `g` is within `L¹`
distance `δ` of a function `s` already satisfying the theorem. -/
lemma measure_limsup_birkhoffAverage_sub_condExp_le (hf : MeasurePreserving f μ μ)
    (g_integrable : Integrable g μ) {s : α → E} (s_integrable : Integrable s μ)
    (s_tendsto : ∀ᵐ x ∂μ, Tendsto (birkhoffAverage ℝ f s · x) atTop (𝓝 (μ[s | invariants f] x)))
    {ε δ : ℝ} (hε : 0 < ε) (hs_close : ∫ y, ‖g y - s y‖ ∂μ < δ) :
    ε * μ.real (birkhoffExceptionalSet μ f g ε) ≤ 2 * δ := by
  -- Write `e` for the small difference between `g` and `s`.
  set e : α → E := g - s with e_def
  have e_int : Integrable e μ := g_integrable.sub s_integrable
  have e_close : ∫ y, ‖e y‖ ∂μ < δ := hs_close
  have e_eq_sum : g = s + e := by simp [e_def]
  have e_tendsto := ae_tendsTo_birkhoffAverage_condExp_real μ hf e_int.norm
  have hsplit : μ[g | invariants f] =ᵐ[μ] μ[s | invariants f] + μ[e | invariants f] :=
    e_eq_sum ▸ condExp_add s_integrable e_int _
  have hnorm : (‖μ[e | invariants f] ·‖) ≤ᵐ[μ] μ[(‖e ·‖) | invariants f] := norm_condExp_le _
  -- The exceptional set is a.e. a subset of a set whose measure we can control.
  have hsub : birkhoffExceptionalSet μ f g ε ≤ᵐ[μ] {x | ε ≤ 2 * μ[(‖e ·‖) | invariants f] x} := by
    filter_upwards [s_tendsto, e_tendsto, hsplit, hnorm] with x hxs hxe hxsplit hxnorm hmem
    -- The dominating sequence `‖Aₙ s - 𝔼 s‖ + (Aₙ ‖e‖ + 𝔼 ‖e‖)` converges to `2 * 𝔼 ‖e‖`: the
    -- first term tends to `0` by hypothesis on `s`, the second to `𝔼 ‖e‖` by the real case.
    have hu : Tendsto (fun n ↦ ‖birkhoffAverage ℝ f s n x - μ[s|invariants f] x‖ +
        (birkhoffAverage ℝ f (‖e ·‖) n x + μ[(‖e ·‖) | invariants f] x)) atTop
        (𝓝 (2 * μ[(‖e ·‖) | invariants f] x)) := by
      simpa [two_mul] using (hxs.sub_const (μ[s|invariants f] x)).norm.add
        (hxe.add_const (μ[(‖e ·‖) | invariants f] x))
    -- So `ε ≤ dist (Aₙ g) (𝔼 g)` infinitely often forces `ε ≤ 2 * 𝔼 ‖e‖`.
    refine isClosed_Ici.mem_of_frequently_of_tendsto (hmem.mono fun n hn ↦ hn.trans ?_) hu
    rw [hxsplit]
    simp only [e_eq_sum, birkhoffAverage_add, Pi.add_apply, dist_eq_norm, add_sub_add_comm]
    grw [norm_add_le]
    gcongr
    grw [norm_sub_le, norm_birkhoffAverage_le]
    gcongr
  calc
    _ ≤ ε * μ.real {x | ε ≤ 2 * μ[(‖e ·‖) | invariants f] x} := by
        grw [measureReal_mono_ae hsub]
    _ ≤ 2 * δ := by
        -- By Markov's inequality, `μ[‖e‖|invariants f]` has integral `∫ ‖e‖ < δ`.
        have hnn := condExp_nonneg (m := invariants f) (ae_of_all μ fun y ↦ norm_nonneg (e y))
        apply mul_meas_ge_le_integral_of_nonneg (hnn.mono fun x hx ↦ mul_nonneg zero_le_two hx)
          (by fun_prop) ε |>.trans
        rw [integral_const_mul, integral_condExp (invariants_le f)]
        grw [e_close]

/-- The set of functions satisfying the pointwise theorem is closed in `L¹`: if for every `δ > 0`,
there is an integrable `s` satisfying the theorem with `∫ ‖g - s‖ < δ`, then `g` satisfies the
theorem. -/
lemma ae_tendsTo_birkhoffAverage_condExp_of_approx (hf : MeasurePreserving f μ μ)
    (hg : Integrable g μ)
    (h : ∀ δ : ℝ, 0 < δ → ∃ s : α → E, Integrable s μ ∧
      (∀ᵐ x ∂μ, Tendsto (birkhoffAverage ℝ f s · x) atTop (𝓝 (μ[s|invariants f] x))) ∧
      ∫ y, ‖g y - s y‖ ∂μ < δ) :
    ∀ᵐ x ∂μ, Tendsto (birkhoffAverage ℝ f g · x) atTop (𝓝 (μ[g|invariants f] x)) := by
  refine ae_tendsto_iff_forall_measure_frequently_eq_zero.2 fun ε hε ↦ ?_
  rw [← measureReal_eq_zero_iff]
  refine le_antisymm (le_of_forall_gt_imp_ge_of_dense fun δ hδ ↦ ?_) (by positivity)
  obtain ⟨s, hs_int, hs_tendsto, hs_close⟩ := h (ε * δ / 2) (by positivity)
  calc
    _ ≤ 2 * (ε * δ / 2) / ε := by
        rw [le_div_iff₀' hε]
        exact measure_limsup_birkhoffAverage_sub_condExp_le hf hg hs_int hs_tendsto hε hs_close
    _ = δ := by field_simp

/-- **Pointwise Ergodic Theorem**, also known as **Birkhoff's Ergodic Theorem**.

For an integrable function `g` with values in a Banach space, the time averages converge almost
everywhere to the conditional expectation of `g` with respect to the σ-algebra of invariant
sets. -/
public theorem ae_tendsTo_birkhoffAverage_condExp (hf : MeasurePreserving f μ μ)
    (hg : Integrable g μ) :
    ∀ᵐ x ∂μ, Tendsto (birkhoffAverage ℝ f g · x) atTop (𝓝 (μ[g|invariants f] x)) := by
  apply hg.induction (P := _)
  case h_ind =>
    intro c s hs _
    let g y := s.indicator (fun _ ↦ (1 : ℝ)) y
    have hcoe : (s.indicator fun _ ↦ c) = fun y ↦ g y • c := by
      simpa using Set.indicator_smul_const s (fun _ ↦ (1 : ℝ)) c
    rw [hcoe]
    have hind_int : Integrable g μ := by fun_prop
    filter_upwards [ae_tendsTo_birkhoffAverage_condExp_real μ hf hind_int,
      condExp_smul_const (m := invariants f) hind_int c] with x hx hcx
    simp only [birkhoffAverage_smul_const, hcx]
    exact hx.smul_const c
  case h_add =>
    intro g₁ g₂ _ g₁_int g₂_int hg₁ hg₂
    have hadd := condExp_add g₁_int g₂_int (invariants f)
    filter_upwards [hg₁, hg₂, hadd] with x hx₁ hx₂ hx₃
    rw [birkhoffAverage_add, hx₃]
    exact hx₁.add hx₂
  case h_closed =>
    refine isClosed_of_closure_subset fun g hg ↦ ?_
    refine ae_tendsTo_birkhoffAverage_condExp_of_approx hf (L1.integrable_coeFn g) fun δ hδ ↦ ?_
    obtain ⟨s, hs_mem, hs_dist⟩ := Metric.mem_closure_iff.mp hg δ hδ
    refine ⟨s, L1.integrable_coeFn s, hs_mem, ?_⟩
    calc ∫ y, ‖g y - s y‖ ∂μ
        = dist g s := by
          rw [dist_eq_norm, L1.norm_eq_integral_norm]
          exact integral_congr_ae ((AEEqFun.coeFn_sub (g : α →ₘ[μ] E) s).mono (by intros; simp [*]))
      _ < δ := hs_dist
  case h_ae =>
    intro g₁ g₂ hae g₁_int hg₁
    have h₁ := ae_all_iff.mpr <|
      hf.quasiMeasurePreserving.birkhoffAverage_ae_eq_of_ae_eq (R := ℝ) hae
    have h₂ := condExp_congr_ae (m := invariants f) hae
    filter_upwards [h₁, h₂, hg₁] with x hx₁ hx₂ hx₃
    conv in birkhoffAverage .. => rw [← hx₁]
    rwa [← hx₂]

section Invariant

omit [IsProbabilityMeasure μ] [CompleteSpace E] in
public lemma comp_eq_condExp_invariants : μ[g | invariants f] ∘ f = μ[g | invariants f] := by
  borelize E
  exact comp_eq_of_measurable_invariants stronglyMeasurable_condExp.measurable

end Invariant

end NormedAddCommGroup
