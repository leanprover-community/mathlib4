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

* `ae_tendsTo_birkhoffAverage_condExp`: time average coincides with conditional expectation

-/

section DivergentSet

open MeasureTheory Measure MeasurableSpace Filter Topology

variable {α : Type*}

def divergentSet (f : α → α) (g : α → ℝ) : Set α := {x | birkhoffSumSup f g x = ⊤}

lemma divergentSet_invariant {f : α → α} {x g} : f x ∈ divergentSet f g ↔ x ∈ divergentSet f g := by
  simp only [divergentSet, birkhoffSumSup, Set.mem_setOf_eq]
  nth_rw 2 [← sup_iSup_nat_succ]
  simp only [birkhoffSum_zero', Pi.zero_apply, EReal.coe_zero, birkhoffSum_succ', EReal.coe_add,
    max_eq_top, EReal.zero_ne_top, false_or]
  rw [← EReal.add_iSup, EReal.add_eq_top_iff_eq_top_right (by simp) (by simp)]

lemma divergentSet_measurable {f : α → α} [MeasurableSpace α] (hf : Measurable f) {g : α → ℝ}
    (hg : Measurable g) : MeasurableSet (divergentSet f g) :=
  measurable_birkhoffSumSup hf hg (measurableSet_singleton ⊤)

lemma divergentSet_mem_invalg [MeasurableSpace α] {f : α → α} (hf : Measurable f) {g : α → ℝ}
    (hg : Measurable g) : MeasurableSet[invariants f] (divergentSet f g) :=
  ⟨divergentSet_measurable hf hg, funext (fun _ ↦ propext divergentSet_invariant)⟩

lemma birkhoffMax_tendsto_top_mem_divergentSet {f : α → α} {x g} (hx : x ∈ divergentSet f g) :
    Tendsto (birkhoffMax f g · x) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  simp only [divergentSet, birkhoffSumSup, iSup_eq_top, Set.mem_setOf_eq] at hx
  obtain ⟨N, hN⟩ := hx b (by simp)
  norm_cast at hN
  use N, fun n hn ↦ le_trans (le_of_lt hN) ?_
  exact le_partialSups_of_le (birkhoffSum f g) hn _

abbrev birkhoffMaxDiff (f : α → α) (g : α → ℝ) (n : ℕ) (x : α) :=
  birkhoffMax f g (n + 1) x - birkhoffMax f g n (f x)

lemma birkhoffMaxDiff_aux {f : α → α} {g n x} :
    birkhoffMaxDiff f g n x = g x - (0 ⊓ (g x + birkhoffMax f g n (f x))) := by
  rw [sub_eq_sub_iff_add_eq_add, birkhoffMax_succ, max_add_min, zero_add]

lemma birkhoffMaxDiff_antitone {f : α → α} {g : α → ℝ} : Antitone (birkhoffMaxDiff f g) := by
  intro m n hmn x
  simp only [birkhoffMaxDiff_aux]
  gcongr
  exact (birkhoffMax f g).mono hmn (f x)

lemma birkhoffMaxDiff_tendsto_of_mem_divergentSet {f : α → α} {x g} (hx : x ∈ divergentSet f g) :
    Tendsto (birkhoffMaxDiff f g · x) atTop (𝓝 (g x)) := by
  have hx' : f x ∈ divergentSet f g := divergentSet_invariant.mpr hx
  obtain ⟨N, hN⟩ := tendsto_atTop_atTop.mp (birkhoffMax_tendsto_top_mem_divergentSet hx') (- g x)
  refine tendsto_atTop_of_eventually_const (i₀ := N) fun n hn ↦ ?_
  rw [birkhoffMaxDiff_aux, inf_of_le_left]
  · ring
  · simpa [add_comm] using sub_nonneg_of_le (hN n hn)

lemma birkhoffAverage_tendsto_nonpos_of_not_mem_divergentSet {f : α → α} {x g}
    (hx : x ∉ divergentSet f g) : limsup (birkhoffAverage ℝ f g · x |>.toEReal) atTop ≤ 0 := by
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

variable {f : α → α} [MeasurableSpace α] (μ : Measure α := by volume_tac) {g : α → ℝ}

lemma birkhoffMaxDiff_integrable (hf : MeasurePreserving f μ μ) (hg : Integrable g μ) {n} :
    Integrable (birkhoffMaxDiff f g n) μ :=
  (integrable_birkhoffMax μ hf hg).sub
    (hf.integrable_comp_of_integrable (integrable_birkhoffMax μ hf hg))

lemma int_birkhoffMaxDiff_in_divergentSet_tendsto (hf : MeasurePreserving f μ μ)
    (hg : Integrable g μ) (hg' : Measurable g) :
    Tendsto (fun n ↦ ∫ x in divergentSet f g, birkhoffMaxDiff f g n x ∂μ) atTop
            (𝓝 <| ∫ x in divergentSet f g, g x ∂ μ) := by
  apply MeasureTheory.tendsto_integral_of_dominated_convergence
    (abs g ⊔ abs (birkhoffMaxDiff f g 0))
  · exact fun _ ↦ (birkhoffMaxDiff_integrable μ hf hg).aestronglyMeasurable.restrict
  · apply Integrable.sup <;> apply Integrable.abs
    · exact hg.restrict
    · exact (birkhoffMaxDiff_integrable μ hf hg).restrict
  · intro n
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs]
    exact abs_le_max_abs_abs (by simp [birkhoffMaxDiff_aux])
      (birkhoffMaxDiff_antitone n.zero_le _)
  · exact (ae_restrict_iff' (divergentSet_measurable hf.measurable hg')).mpr
      (ae_of_all _ fun _ hx ↦ birkhoffMaxDiff_tendsto_of_mem_divergentSet hx)

lemma int_birkhoffMaxDiff_in_divergentSet_nonneg (hf : MeasurePreserving f μ μ)
    (hg : Integrable g μ) (hg' : Measurable g) {n} :
    0 ≤ ∫ x in divergentSet f g, birkhoffMaxDiff f g n x ∂μ := by
  have hres : MeasurePreserving f (μ.restrict (divergentSet f g)) (μ.restrict (divergentSet f g)) :=
    ⟨hf.measurable, by nth_rw 1 [← (divergentSet_mem_invalg hf.measurable hg').2,
      ← μ.restrict_map hf.measurable (divergentSet_measurable hf.measurable hg'), hf.map_eq]⟩
  have mi {n : ℕ} := integrable_birkhoffMax μ hf hg (n := n)
  rw [integral_sub, sub_nonneg]
  · rw [← integral_map hres.aemeasurable
      (measurable_birkhoffMax hf.measurable hg').aestronglyMeasurable, hres.map_eq]
    exact integral_mono mi.restrict mi.restrict ((birkhoffMax f g).monotone (Nat.le_succ _))
  · exact mi.restrict
  · exact hres.integrable_comp_of_integrable mi.restrict

lemma int_in_divergentSet_nonneg (hf : MeasurePreserving f μ μ)
    (hg : Integrable g μ) (hg' : Measurable g) : 0 ≤ ∫ x in divergentSet f g, g x ∂μ :=
  le_of_tendsto_of_tendsto' tendsto_const_nhds
    (int_birkhoffMaxDiff_in_divergentSet_tendsto μ hf hg hg')
    (fun _ ↦ int_birkhoffMaxDiff_in_divergentSet_nonneg μ hf hg hg')

omit [MeasurableSpace α] in
lemma nullMeasurableSpace_le [msα : MeasurableSpace α] {μ : Measure α} :
    msα ≤ NullMeasurableSpace.instMeasurableSpace (α := α) (μ := μ) :=
  fun s hs ↦ ⟨s, hs, ae_eq_refl s⟩

lemma divergentSet_zero_meas_of_condexp_neg [hμ : IsProbabilityMeasure μ]
    (h : ∀ᵐ x ∂μ, (μ[g | invariants f]) x < 0) (hf : MeasurePreserving f μ μ)
    (hg : Integrable g μ) (hg' : Measurable g) :
    μ (divergentSet f g) = 0 := by
  have pos : ∀ᵐ x ∂μ.restrict (divergentSet f g), 0 < -(μ[g|invariants f]) x :=
    ae_restrict_of_ae (h.mono fun _ hx ↦ neg_pos.mpr hx)
  have ds_meas := divergentSet_mem_invalg hf.measurable hg'
  by_contra hm; simp_rw [← pos_iff_ne_zero] at hm
  have : ∫ x in divergentSet f g, g x ∂μ < 0 := by
    rw [← setIntegral_condExp (invariants_le f) hg ds_meas,
      ← Left.neg_pos_iff, ← integral_neg, integral_pos_iff_support_of_nonneg_ae]
    · unfold Function.support
      rw [(ae_iff_measure_eq _).mp]
      · rwa [Measure.restrict_apply_univ _]
      · conv in _ ≠ _ => rw [ne_comm]
        exact Eventually.ne_of_lt pos
      · apply measurableSet_support _
        apply (stronglyMeasurable_condExp).measurable.neg.le _
        refine (le_trans (invariants_le f) nullMeasurableSpace_le)
    · exact ae_le_of_ae_lt pos
    · exact integrable_condExp.restrict.neg
  exact this.not_ge (int_in_divergentSet_nonneg μ hf hg hg')

lemma ae_tendsTo_birkhoffAverage_of_condExp_neg [hμ : IsProbabilityMeasure μ]
    (hf : MeasurePreserving f μ μ) (hg : Integrable g μ) (hg' : Measurable g)
    (h : ∀ᵐ x ∂μ, (μ[g | invariants f]) x < 0) :
    ∀ᵐ x ∂μ, limsup (birkhoffAverage ℝ f g · x |>.toEReal) atTop ≤ 0 := by
  apply Eventually.mono _ fun _ ↦ birkhoffAverage_tendsto_nonpos_of_not_mem_divergentSet
  apply ae_iff.mpr
  simp only [not_not, Set.setOf_mem_eq]
  exact divergentSet_zero_meas_of_condexp_neg μ h hf hg hg'

end DivergentSet

section Real

open MeasureTheory Measure MeasurableSpace Filter Topology

variable {α : Type*} {f : α → α} [MeasurableSpace α] (μ : Measure α := by volume_tac)
    {g : α → ℝ} [hμ : IsProbabilityMeasure μ]

/-- The time average is a.e., eventually not much less than the conditional expectation. -/
lemma ae_tendsTo_birkhoffAverage_sub_condExp_nonneg {ε : ℝ} (hε : 0 < ε)
    (hf : MeasurePreserving f μ μ) (hg : Integrable g μ) (hg' : Measurable g) :
    ∀ᵐ x ∂μ, limsup
      (fun n ↦ (birkhoffAverage ℝ f g n x - (μ[g|invariants f] x + ε)).toEReal) atTop ≤ 0 := by
  -- Let `ψ` denote the difference between `g` and the conditional expectation of `g` plus `ε`.
  let h := g - (μ[g|invariants f] + fun _ ↦ ε)
  have h_integrable : Integrable h μ := hg.sub (integrable_condExp.add (integrable_const _))
  have h_measurable : Measurable h := by
    suffices Measurable (μ[g|invariants f]) by measurability
    exact stronglyMeasurable_condExp.measurable.le (invariants_le f)
  -- It follows from the definition of `ψ` that it is a.e. equal to `-ε`.
  have h_condexp_const : μ[h|invariants f] =ᵐ[μ] - fun _ ↦ ε := calc
    _ =ᵐ[μ] μ[g|invariants f] - μ[μ[g|invariants f] + fun _ ↦ ε|invariants f] :=
      condExp_sub hg (integrable_condExp.add (integrable_const _)) _
    _ =ᵐ[μ] μ[g|invariants f] - (μ[μ[g|invariants f]|invariants f] + μ[fun _ ↦ ε|invariants f]) :=
      (condExp_add integrable_condExp (integrable_const _) _).neg.add_left
    _ =ᵐ[μ] μ[g|invariants f] - (μ[g|invariants f] + μ[fun _ ↦ ε|invariants f]) :=
      (condExp_condExp_of_le (le_of_eq rfl) (invariants_le f)).add_right.neg.add_left
    _ = - μ[fun _ ↦ ε|invariants f] := by simp
    _ = - fun _ ↦ ε := by rw [condExp_const <| invariants_le f]
  -- For typical points the time average of `ψ` is eventually non-negative.
  have limsup_nonpos : ∀ᵐ x ∂μ, limsup (birkhoffAverage ℝ f h · x |>.toEReal) atTop ≤ 0 := by
    suffices ∀ᵐ x ∂μ, μ[h|invariants f] x < 0 from
      ae_tendsTo_birkhoffAverage_of_condExp_neg μ hf h_integrable h_measurable this
    exact h_condexp_const.mono fun x hx ↦ by simp [hx, hε]
  -- Transfer the result on `ψ` to the required result on `g`.
  refine limsup_nonpos.mono fun x hx => ?_
  refine le_of_eq_of_le (limsup_congr ?_) hx
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hcomp : μ[g|invariants f] ∘ f = μ[g|invariants f] :=
    comp_eq_of_measurable_invariants stronglyMeasurable_condExp.measurable
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  simp [h, birkhoffAverage_sub, birkhoffAverage_add,
    birkhoffAverage_of_comp_eq ℝ (show (fun _ : α ↦ ε) ∘ f = fun _ ↦ ε from rfl) hn',
    birkhoffAverage_of_comp_eq ℝ hcomp hn']

/-- Same as the main result `ae_tendsTo_birkhoffAverage_condExp` but assuming `Measurable g`. -/
private lemma ae_tendsTo_birkhoffAverage_condExp_aux
    (hf : MeasurePreserving f μ μ) (hg : Integrable g μ) (hg' : Measurable g) :
    ∀ᵐ x ∂μ, Tendsto (birkhoffAverage ℝ f g · x) atTop (𝓝 (μ[g|invariants f] x)) := by
  have : ∀ᵐ x ∂μ, ∀ (k : {k : ℕ // k > 0}),
      ∀ᶠ n in atTop, |birkhoffAverage ℝ f g n x - (μ[g|invariants f] x)| < (k : ℝ)⁻¹ := by
    apply ae_all_iff.mpr
    rintro ⟨k, hk⟩
    let δ := (k : ℝ)⁻¹ / 2
    have hδ : δ > 0 := by simpa [δ]
    have p₁ := ae_tendsTo_birkhoffAverage_sub_condExp_nonneg μ hδ hf hg hg'
    have p₂ := ae_tendsTo_birkhoffAverage_sub_condExp_nonneg μ hδ hf hg.neg hg'.neg
    have : μ[-g|invariants f] =ᵐ[μ] - μ[g|invariants f] := condExp_neg _ _
    refine ((p₁.and p₂).and this).mono fun x ⟨⟨hx₁, hx₂⟩, hx₃⟩ => ?_
    have hδ' : (0 : EReal) < (δ : ℝ) := EReal.coe_pos.mpr hδ
    filter_upwards [eventually_lt_of_limsup_lt (hx₁.trans_lt hδ'),
      eventually_lt_of_limsup_lt (hx₂.trans_lt hδ')] with m hm₁ hm₂
    rw [EReal.coe_lt_coe_iff] at hm₁ hm₂
    rw [hx₃, birkhoffAverage_neg] at hm₂
    norm_num at hm₂
    simp_rw [δ] at hm₁ hm₂
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  refine this.mono fun x hx ↦ Metric.tendsto_atTop.mpr fun ε hε ↦ ?_
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  simp only [eventually_atTop, Subtype.forall, gt_iff_lt] at hx
  obtain ⟨N, hN⟩ := hx (k + 1) k.succ_pos
  refine ⟨N, fun n hn ↦ (hN n hn).trans ?_⟩
  rw [one_div] at hk
  exact_mod_cast hk

/-- **Pointwise Ergodic Theorem** a.k.a. **Birkhoff's Ergodic Theorem**

Time average coincides with conditional expectation for typical points. -/
public theorem ae_tendsTo_birkhoffAverage_condExp_real {g : α → ℝ} (hf : MeasurePreserving f μ μ)
    (hg : Integrable g μ) :
    ∀ᵐ x ∂μ, Tendsto (birkhoffAverage ℝ f g · x) atTop (𝓝 (μ[g|invariants f] x)) := by
  let h := hg.left.mk
  have g_ae_eq_h : g =ᵐ[μ] h := hg.left.ae_eq_mk
  have h_integrable : Integrable h μ := (integrable_congr hg.left.ae_eq_mk).mp hg
  have h1 := condExp_congr_ae (m := invariants f) g_ae_eq_h
  have h2 := ae_tendsTo_birkhoffAverage_condExp_aux μ hf h_integrable hg.left.measurable_mk
  have h3 := ae_all_iff.mpr <| hf.quasiMeasurePreserving.birkhoffAverage_ae_eq_of_ae_eq ℝ g_ae_eq_h
  filter_upwards [h1, h2, h3] with _ h1' h2' h3'
  simp [h1', h2', h3']

end Real
