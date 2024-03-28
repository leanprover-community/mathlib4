/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
import Mathlib.Analysis.NormedSpace.BoundedLinearMaps
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.Topology.Algebra.Module.FiniteDimension

#align_import measure_theory.function.strongly_measurable.basic from "leanprover-community/mathlib"@"3b52265189f3fb43aa631edffce5d060fafaf82f"

/-!
# Strongly measurable and finitely strongly measurable functions

A function `f` is said to be strongly measurable if `f` is the sequential limit of simple functions.
It is said to be finitely strongly measurable with respect to a measure `μ` if the supports
of those simple functions have finite measure. We also provide almost everywhere versions of
these notions.

Almost everywhere strongly measurable functions form the largest class of functions that can be
integrated using the Bochner integral.

If the target space has a second countable topology, strongly measurable and measurable are
equivalent.

If the measure is sigma-finite, strongly measurable and finitely strongly measurable are equivalent.

The main property of finitely strongly measurable functions is
`FinStronglyMeasurable.exists_set_sigmaFinite`: there exists a measurable set `t` such that the
function is supported on `t` and `μ.restrict t` is sigma-finite. As a consequence, we can prove some
results for those functions as if the measure was sigma-finite.

## Main definitions

* `StronglyMeasurable f`: `f : α → β` is the limit of a sequence `fs : ℕ → SimpleFunc α β`.
* `FinStronglyMeasurable f μ`: `f : α → β` is the limit of a sequence `fs : ℕ → SimpleFunc α β`
  such that for all `n ∈ ℕ`, the measure of the support of `fs n` is finite.
* `AEStronglyMeasurable f μ`: `f` is almost everywhere equal to a `StronglyMeasurable` function.
* `AEFinStronglyMeasurable f μ`: `f` is almost everywhere equal to a `FinStronglyMeasurable`
  function.

* `AEFinStronglyMeasurable.sigmaFiniteSet`: a measurable set `t` such that
  `f =ᵐ[μ.restrict tᶜ] 0` and `μ.restrict t` is sigma-finite.

## Main statements

* `AEFinStronglyMeasurable.exists_set_sigmaFinite`: there exists a measurable set `t` such that
  `f =ᵐ[μ.restrict tᶜ] 0` and `μ.restrict t` is sigma-finite.

We provide a solid API for strongly measurable functions, and for almost everywhere strongly
measurable functions, as a basis for the Bochner integral.

## References

* Hytönen, Tuomas, Jan Van Neerven, Mark Veraar, and Lutz Weis. Analysis in Banach spaces.
  Springer, 2016.

-/


open MeasureTheory Filter TopologicalSpace Function Set MeasureTheory.Measure

open ENNReal Topology MeasureTheory NNReal BigOperators

variable {α β γ ι : Type*} [Countable ι]

namespace MeasureTheory

local infixr:25 " →ₛ " => SimpleFunc

section Definitions

variable [TopologicalSpace β]

/-- A function is `StronglyMeasurable` if it is the limit of simple functions. -/
def StronglyMeasurable [MeasurableSpace α] (f : α → β) : Prop :=
  ∃ fs : ℕ → α →ₛ β, ∀ x, Tendsto (fun n => fs n x) atTop (𝓝 (f x))
#align measure_theory.strongly_measurable MeasureTheory.StronglyMeasurable

/-- The notation for StronglyMeasurable giving the measurable space instance explicitly. -/
scoped notation "StronglyMeasurable[" m "]" => @MeasureTheory.StronglyMeasurable _ _ _ m

/-- A function is `FinStronglyMeasurable` with respect to a measure if it is the limit of simple
  functions with support with finite measure. -/
def FinStronglyMeasurable [Zero β] {_ : MeasurableSpace α} (f : α → β) (μ : Measure α) : Prop :=
  ∃ fs : ℕ → α →ₛ β, (∀ n, μ (support (fs n)) < ∞) ∧ ∀ x, Tendsto (fun n => fs n x) atTop (𝓝 (f x))
#align measure_theory.fin_strongly_measurable MeasureTheory.FinStronglyMeasurable

/-- A function is `AEStronglyMeasurable` with respect to a measure `μ` if it is almost everywhere
equal to the limit of a sequence of simple functions. -/
def AEStronglyMeasurable {_ : MeasurableSpace α} (f : α → β) (μ : Measure α) : Prop :=
  ∃ g, StronglyMeasurable g ∧ f =ᵐ[μ] g
#align measure_theory.ae_strongly_measurable MeasureTheory.AEStronglyMeasurable

/-- A function is `AEFinStronglyMeasurable` with respect to a measure if it is almost everywhere
equal to the limit of a sequence of simple functions with support with finite measure. -/
def AEFinStronglyMeasurable [Zero β] {_ : MeasurableSpace α} (f : α → β) (μ : Measure α) : Prop :=
  ∃ g, FinStronglyMeasurable g μ ∧ f =ᵐ[μ] g
#align measure_theory.ae_fin_strongly_measurable MeasureTheory.AEFinStronglyMeasurable

end Definitions

open MeasureTheory

/-! ## Strongly measurable functions -/

@[aesop 30% apply (rule_sets := [Measurable])]
protected theorem StronglyMeasurable.aestronglyMeasurable {α β} {_ : MeasurableSpace α}
    [TopologicalSpace β] {f : α → β} {μ : Measure α} (hf : StronglyMeasurable f) :
    AEStronglyMeasurable f μ :=
  ⟨f, hf, EventuallyEq.refl _ _⟩
#align measure_theory.strongly_measurable.ae_strongly_measurable MeasureTheory.StronglyMeasurable.aestronglyMeasurable

@[simp]
theorem Subsingleton.stronglyMeasurable {α β} [MeasurableSpace α] [TopologicalSpace β]
    [Subsingleton β] (f : α → β) : StronglyMeasurable f := by
  let f_sf : α →ₛ β := ⟨f, fun x => ?_, Set.Subsingleton.finite Set.subsingleton_of_subsingleton⟩
  · exact ⟨fun _ => f_sf, fun x => tendsto_const_nhds⟩
  · have h_univ : f ⁻¹' {x} = Set.univ := by
      ext1 y
      simp [eq_iff_true_of_subsingleton]
    rw [h_univ]
    exact MeasurableSet.univ
#align measure_theory.subsingleton.strongly_measurable MeasureTheory.Subsingleton.stronglyMeasurable

theorem SimpleFunc.stronglyMeasurable {α β} {_ : MeasurableSpace α} [TopologicalSpace β]
    (f : α →ₛ β) : StronglyMeasurable f :=
  ⟨fun _ => f, fun _ => tendsto_const_nhds⟩
#align measure_theory.simple_func.strongly_measurable MeasureTheory.SimpleFunc.stronglyMeasurable

@[nontriviality]
theorem StronglyMeasurable.of_finite [Finite α] {_ : MeasurableSpace α}
    [MeasurableSingletonClass α] [TopologicalSpace β]
    (f : α → β) : StronglyMeasurable f :=
  ⟨fun _ => SimpleFunc.ofFinite f, fun _ => tendsto_const_nhds⟩

@[deprecated] -- Since 2024/02/05
alias stronglyMeasurable_of_fintype := StronglyMeasurable.of_finite

@[deprecated StronglyMeasurable.of_finite]
theorem stronglyMeasurable_of_isEmpty [IsEmpty α] {_ : MeasurableSpace α} [TopologicalSpace β]
    (f : α → β) : StronglyMeasurable f :=
  .of_finite f
#align measure_theory.strongly_measurable_of_is_empty MeasureTheory.StronglyMeasurable.of_finite

theorem stronglyMeasurable_const {α β} {_ : MeasurableSpace α} [TopologicalSpace β] {b : β} :
    StronglyMeasurable fun _ : α => b :=
  ⟨fun _ => SimpleFunc.const α b, fun _ => tendsto_const_nhds⟩
#align measure_theory.strongly_measurable_const MeasureTheory.stronglyMeasurable_const

@[to_additive]
theorem stronglyMeasurable_one {α β} {_ : MeasurableSpace α} [TopologicalSpace β] [One β] :
    StronglyMeasurable (1 : α → β) :=
  stronglyMeasurable_const
#align measure_theory.strongly_measurable_one MeasureTheory.stronglyMeasurable_one
#align measure_theory.strongly_measurable_zero MeasureTheory.stronglyMeasurable_zero

/-- A version of `stronglyMeasurable_const` that assumes `f x = f y` for all `x, y`.
This version works for functions between empty types. -/
theorem stronglyMeasurable_const' {α β} {m : MeasurableSpace α} [TopologicalSpace β] {f : α → β}
    (hf : ∀ x y, f x = f y) : StronglyMeasurable f := by
  nontriviality α
  inhabit α
  convert stronglyMeasurable_const (β := β) using 1
  exact funext fun x => hf x default
#align measure_theory.strongly_measurable_const' MeasureTheory.stronglyMeasurable_const'

-- Porting note: changed binding type of `MeasurableSpace α`.
@[simp]
theorem Subsingleton.stronglyMeasurable' {α β} [MeasurableSpace α] [TopologicalSpace β]
    [Subsingleton α] (f : α → β) : StronglyMeasurable f :=
  stronglyMeasurable_const' fun x y => by rw [Subsingleton.elim x y]
#align measure_theory.subsingleton.strongly_measurable' MeasureTheory.Subsingleton.stronglyMeasurable'

namespace StronglyMeasurable

variable {f g : α → β}

section BasicPropertiesInAnyTopologicalSpace

variable [TopologicalSpace β]

/-- A sequence of simple functions such that
`∀ x, Tendsto (fun n => hf.approx n x) atTop (𝓝 (f x))`.
That property is given by `stronglyMeasurable.tendsto_approx`. -/
protected noncomputable def approx {_ : MeasurableSpace α} (hf : StronglyMeasurable f) :
    ℕ → α →ₛ β :=
  hf.choose
#align measure_theory.strongly_measurable.approx MeasureTheory.StronglyMeasurable.approx

protected theorem tendsto_approx {_ : MeasurableSpace α} (hf : StronglyMeasurable f) :
    ∀ x, Tendsto (fun n => hf.approx n x) atTop (𝓝 (f x)) :=
  hf.choose_spec
#align measure_theory.strongly_measurable.tendsto_approx MeasureTheory.StronglyMeasurable.tendsto_approx

/-- Similar to `stronglyMeasurable.approx`, but enforces that the norm of every function in the
sequence is less than `c` everywhere. If `‖f x‖ ≤ c` this sequence of simple functions verifies
`Tendsto (fun n => hf.approxBounded n x) atTop (𝓝 (f x))`. -/
noncomputable def approxBounded {_ : MeasurableSpace α} [Norm β] [SMul ℝ β]
    (hf : StronglyMeasurable f) (c : ℝ) : ℕ → SimpleFunc α β := fun n =>
  (hf.approx n).map fun x => min 1 (c / ‖x‖) • x
#align measure_theory.strongly_measurable.approx_bounded MeasureTheory.StronglyMeasurable.approxBounded

theorem tendsto_approxBounded_of_norm_le {β} {f : α → β} [NormedAddCommGroup β] [NormedSpace ℝ β]
    {m : MeasurableSpace α} (hf : StronglyMeasurable[m] f) {c : ℝ} {x : α} (hfx : ‖f x‖ ≤ c) :
    Tendsto (fun n => hf.approxBounded c n x) atTop (𝓝 (f x)) := by
  have h_tendsto := hf.tendsto_approx x
  simp only [StronglyMeasurable.approxBounded, SimpleFunc.coe_map, Function.comp_apply]
  by_cases hfx0 : ‖f x‖ = 0
  · rw [norm_eq_zero] at hfx0
    rw [hfx0] at h_tendsto ⊢
    have h_tendsto_norm : Tendsto (fun n => ‖hf.approx n x‖) atTop (𝓝 0) := by
      convert h_tendsto.norm
      rw [norm_zero]
    refine' squeeze_zero_norm (fun n => _) h_tendsto_norm
    calc
      ‖min 1 (c / ‖hf.approx n x‖) • hf.approx n x‖ =
          ‖min 1 (c / ‖hf.approx n x‖)‖ * ‖hf.approx n x‖ :=
        norm_smul _ _
      _ ≤ ‖(1 : ℝ)‖ * ‖hf.approx n x‖ := by
        refine' mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        rw [norm_one, Real.norm_of_nonneg]
        · exact min_le_left _ _
        · exact le_min zero_le_one (div_nonneg ((norm_nonneg _).trans hfx) (norm_nonneg _))
      _ = ‖hf.approx n x‖ := by rw [norm_one, one_mul]
  rw [← one_smul ℝ (f x)]
  refine' Tendsto.smul _ h_tendsto
  have : min 1 (c / ‖f x‖) = 1 := by
    rw [min_eq_left_iff, one_le_div (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hfx0))]
    exact hfx
  nth_rw 2 [this.symm]
  refine' Tendsto.min tendsto_const_nhds _
  exact Tendsto.div tendsto_const_nhds h_tendsto.norm hfx0
#align measure_theory.strongly_measurable.tendsto_approx_bounded_of_norm_le MeasureTheory.StronglyMeasurable.tendsto_approxBounded_of_norm_le

theorem tendsto_approxBounded_ae {β} {f : α → β} [NormedAddCommGroup β] [NormedSpace ℝ β]
    {m m0 : MeasurableSpace α} {μ : Measure α} (hf : StronglyMeasurable[m] f) {c : ℝ}
    (hf_bound : ∀ᵐ x ∂μ, ‖f x‖ ≤ c) :
    ∀ᵐ x ∂μ, Tendsto (fun n => hf.approxBounded c n x) atTop (𝓝 (f x)) := by
  filter_upwards [hf_bound] with x hfx using tendsto_approxBounded_of_norm_le hf hfx
#align measure_theory.strongly_measurable.tendsto_approx_bounded_ae MeasureTheory.StronglyMeasurable.tendsto_approxBounded_ae

theorem norm_approxBounded_le {β} {f : α → β} [SeminormedAddCommGroup β] [NormedSpace ℝ β]
    {m : MeasurableSpace α} {c : ℝ} (hf : StronglyMeasurable[m] f) (hc : 0 ≤ c) (n : ℕ) (x : α) :
    ‖hf.approxBounded c n x‖ ≤ c := by
  simp only [StronglyMeasurable.approxBounded, SimpleFunc.coe_map, Function.comp_apply]
  refine' (norm_smul_le _ _).trans _
  by_cases h0 : ‖hf.approx n x‖ = 0
  · simp only [h0, _root_.div_zero, min_eq_right, zero_le_one, norm_zero, mul_zero]
    exact hc
  rcases le_total ‖hf.approx n x‖ c with h | h
  · rw [min_eq_left _]
    · simpa only [norm_one, one_mul] using h
    · rwa [one_le_div (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0))]
  · rw [min_eq_right _]
    · rw [norm_div, norm_norm, mul_comm, mul_div, div_eq_mul_inv, mul_comm, ← mul_assoc,
        inv_mul_cancel h0, one_mul, Real.norm_of_nonneg hc]
    · rwa [div_le_one (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0))]
#align measure_theory.strongly_measurable.norm_approx_bounded_le MeasureTheory.StronglyMeasurable.norm_approxBounded_le

theorem _root_.stronglyMeasurable_bot_iff [Nonempty β] [T2Space β] :
    StronglyMeasurable[⊥] f ↔ ∃ c, f = fun _ => c := by
  cases' isEmpty_or_nonempty α with hα hα
  · simp only [@Subsingleton.stronglyMeasurable' _ _ ⊥ _ _ f,
      eq_iff_true_of_subsingleton, exists_const]
  refine' ⟨fun hf => _, fun hf_eq => _⟩
  · refine' ⟨f hα.some, _⟩
    let fs := hf.approx
    have h_fs_tendsto : ∀ x, Tendsto (fun n => fs n x) atTop (𝓝 (f x)) := hf.tendsto_approx
    have : ∀ n, ∃ c, ∀ x, fs n x = c := fun n => SimpleFunc.simpleFunc_bot (fs n)
    let cs n := (this n).choose
    have h_cs_eq : ∀ n, ⇑(fs n) = fun _ => cs n := fun n => funext (this n).choose_spec
    conv at h_fs_tendsto => enter [x, 1, n]; rw [h_cs_eq]
    have h_tendsto : Tendsto cs atTop (𝓝 (f hα.some)) := h_fs_tendsto hα.some
    ext1 x
    exact tendsto_nhds_unique (h_fs_tendsto x) h_tendsto
  · obtain ⟨c, rfl⟩ := hf_eq
    exact stronglyMeasurable_const
#align strongly_measurable_bot_iff stronglyMeasurable_bot_iff

end BasicPropertiesInAnyTopologicalSpace

theorem finStronglyMeasurable_of_set_sigmaFinite [TopologicalSpace β] [Zero β]
    {m : MeasurableSpace α} {μ : Measure α} (hf_meas : StronglyMeasurable f) {t : Set α}
    (ht : MeasurableSet t) (hft_zero : ∀ x ∈ tᶜ, f x = 0) (htμ : SigmaFinite (μ.restrict t)) :
    FinStronglyMeasurable f μ := by
  haveI : SigmaFinite (μ.restrict t) := htμ
  let S := spanningSets (μ.restrict t)
  have hS_meas : ∀ n, MeasurableSet (S n) := measurable_spanningSets (μ.restrict t)
  let f_approx := hf_meas.approx
  let fs n := SimpleFunc.restrict (f_approx n) (S n ∩ t)
  have h_fs_t_compl : ∀ n, ∀ x, x ∉ t → fs n x = 0 := by
    intro n x hxt
    rw [SimpleFunc.restrict_apply _ ((hS_meas n).inter ht)]
    refine' Set.indicator_of_not_mem _ _
    simp [hxt]
  refine' ⟨fs, _, fun x => _⟩
  · simp_rw [SimpleFunc.support_eq]
    refine' fun n => (measure_biUnion_finset_le _ _).trans_lt _
    refine' ENNReal.sum_lt_top_iff.mpr fun y hy => _
    rw [SimpleFunc.restrict_preimage_singleton _ ((hS_meas n).inter ht)]
    swap
    · letI : (y : β) → Decidable (y = 0) := fun y => Classical.propDecidable _
      rw [Finset.mem_filter] at hy
      exact hy.2
    refine' (measure_mono (Set.inter_subset_left _ _)).trans_lt _
    have h_lt_top := measure_spanningSets_lt_top (μ.restrict t) n
    rwa [Measure.restrict_apply' ht] at h_lt_top
  · by_cases hxt : x ∈ t
    swap
    · rw [funext fun n => h_fs_t_compl n x hxt, hft_zero x hxt]
      exact tendsto_const_nhds
    have h : Tendsto (fun n => (f_approx n) x) atTop (𝓝 (f x)) := hf_meas.tendsto_approx x
    obtain ⟨n₁, hn₁⟩ : ∃ n, ∀ m, n ≤ m → fs m x = f_approx m x := by
      obtain ⟨n, hn⟩ : ∃ n, ∀ m, n ≤ m → x ∈ S m ∩ t := by
        rsuffices ⟨n, hn⟩ : ∃ n, ∀ m, n ≤ m → x ∈ S m
        · exact ⟨n, fun m hnm => Set.mem_inter (hn m hnm) hxt⟩
        rsuffices ⟨n, hn⟩ : ∃ n, x ∈ S n
        · exact ⟨n, fun m hnm => monotone_spanningSets (μ.restrict t) hnm hn⟩
        rw [← Set.mem_iUnion, iUnion_spanningSets (μ.restrict t)]
        trivial
      refine' ⟨n, fun m hnm => _⟩
      simp_rw [fs, SimpleFunc.restrict_apply _ ((hS_meas m).inter ht),
        Set.indicator_of_mem (hn m hnm)]
    rw [tendsto_atTop'] at h ⊢
    intro s hs
    obtain ⟨n₂, hn₂⟩ := h s hs
    refine' ⟨max n₁ n₂, fun m hm => _⟩
    rw [hn₁ m ((le_max_left _ _).trans hm.le)]
    exact hn₂ m ((le_max_right _ _).trans hm.le)
#align measure_theory.strongly_measurable.fin_strongly_measurable_of_set_sigma_finite MeasureTheory.StronglyMeasurable.finStronglyMeasurable_of_set_sigmaFinite

/-- If the measure is sigma-finite, all strongly measurable functions are
  `FinStronglyMeasurable`. -/
@[aesop 5% apply (rule_sets := [Measurable])]
protected theorem finStronglyMeasurable [TopologicalSpace β] [Zero β] {m0 : MeasurableSpace α}
    (hf : StronglyMeasurable f) (μ : Measure α) [SigmaFinite μ] : FinStronglyMeasurable f μ :=
  hf.finStronglyMeasurable_of_set_sigmaFinite MeasurableSet.univ (by simp)
    (by rwa [Measure.restrict_univ])
#align measure_theory.strongly_measurable.fin_strongly_measurable MeasureTheory.StronglyMeasurable.finStronglyMeasurable

/-- A strongly measurable function is measurable. -/
@[aesop 5% apply (rule_sets := [Measurable])]
protected theorem measurable {_ : MeasurableSpace α} [TopologicalSpace β] [PseudoMetrizableSpace β]
    [MeasurableSpace β] [BorelSpace β] (hf : StronglyMeasurable f) : Measurable f :=
  measurable_of_tendsto_metrizable (fun n => (hf.approx n).measurable)
    (tendsto_pi_nhds.mpr hf.tendsto_approx)
#align measure_theory.strongly_measurable.measurable MeasureTheory.StronglyMeasurable.measurable

/-- A strongly measurable function is almost everywhere measurable. -/
@[aesop 5% apply (rule_sets := [Measurable])]
protected theorem aemeasurable {_ : MeasurableSpace α} [TopologicalSpace β]
    [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β] {μ : Measure α}
    (hf : StronglyMeasurable f) : AEMeasurable f μ :=
  hf.measurable.aemeasurable
#align measure_theory.strongly_measurable.ae_measurable MeasureTheory.StronglyMeasurable.aemeasurable

theorem _root_.Continuous.comp_stronglyMeasurable {_ : MeasurableSpace α} [TopologicalSpace β]
    [TopologicalSpace γ] {g : β → γ} {f : α → β} (hg : Continuous g) (hf : StronglyMeasurable f) :
    StronglyMeasurable fun x => g (f x) :=
  ⟨fun n => SimpleFunc.map g (hf.approx n), fun x => (hg.tendsto _).comp (hf.tendsto_approx x)⟩
#align continuous.comp_strongly_measurable Continuous.comp_stronglyMeasurable

@[to_additive]
nonrec theorem measurableSet_mulSupport {m : MeasurableSpace α} [One β] [TopologicalSpace β]
    [MetrizableSpace β] (hf : StronglyMeasurable f) : MeasurableSet (mulSupport f) := by
  borelize β
  exact measurableSet_mulSupport hf.measurable
#align measure_theory.strongly_measurable.measurable_set_mul_support MeasureTheory.StronglyMeasurable.measurableSet_mulSupport
#align measure_theory.strongly_measurable.measurable_set_support MeasureTheory.StronglyMeasurable.measurableSet_support

protected theorem mono {m m' : MeasurableSpace α} [TopologicalSpace β]
    (hf : StronglyMeasurable[m'] f) (h_mono : m' ≤ m) : StronglyMeasurable[m] f := by
  let f_approx : ℕ → @SimpleFunc α m β := fun n =>
    @SimpleFunc.mk α m β
      (hf.approx n)
      (fun x => h_mono _ (SimpleFunc.measurableSet_fiber' _ x))
      (SimpleFunc.finite_range (hf.approx n))
  exact ⟨f_approx, hf.tendsto_approx⟩
#align measure_theory.strongly_measurable.mono MeasureTheory.StronglyMeasurable.mono

protected theorem prod_mk {m : MeasurableSpace α} [TopologicalSpace β] [TopologicalSpace γ]
    {f : α → β} {g : α → γ} (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    StronglyMeasurable fun x => (f x, g x) := by
  refine' ⟨fun n => SimpleFunc.pair (hf.approx n) (hg.approx n), fun x => _⟩
  rw [nhds_prod_eq]
  exact Tendsto.prod_mk (hf.tendsto_approx x) (hg.tendsto_approx x)
#align measure_theory.strongly_measurable.prod_mk MeasureTheory.StronglyMeasurable.prod_mk

theorem comp_measurable [TopologicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ}
    {f : α → β} {g : γ → α} (hf : StronglyMeasurable f) (hg : Measurable g) :
    StronglyMeasurable (f ∘ g) :=
  ⟨fun n => SimpleFunc.comp (hf.approx n) g hg, fun x => hf.tendsto_approx (g x)⟩
#align measure_theory.strongly_measurable.comp_measurable MeasureTheory.StronglyMeasurable.comp_measurable

theorem of_uncurry_left [TopologicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ}
    {f : α → γ → β} (hf : StronglyMeasurable (uncurry f)) {x : α} : StronglyMeasurable (f x) :=
  hf.comp_measurable measurable_prod_mk_left
#align measure_theory.strongly_measurable.of_uncurry_left MeasureTheory.StronglyMeasurable.of_uncurry_left

theorem of_uncurry_right [TopologicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ}
    {f : α → γ → β} (hf : StronglyMeasurable (uncurry f)) {y : γ} :
    StronglyMeasurable fun x => f x y :=
  hf.comp_measurable measurable_prod_mk_right
#align measure_theory.strongly_measurable.of_uncurry_right MeasureTheory.StronglyMeasurable.of_uncurry_right

section Arithmetic

variable {mα : MeasurableSpace α} [TopologicalSpace β]

@[to_additive (attr := aesop safe 20 apply (rule_sets := [Measurable]))]
protected theorem mul [Mul β] [ContinuousMul β] (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) : StronglyMeasurable (f * g) :=
  ⟨fun n => hf.approx n * hg.approx n, fun x => (hf.tendsto_approx x).mul (hg.tendsto_approx x)⟩
#align measure_theory.strongly_measurable.mul MeasureTheory.StronglyMeasurable.mul
#align measure_theory.strongly_measurable.add MeasureTheory.StronglyMeasurable.add

@[to_additive (attr := measurability)]
theorem mul_const [Mul β] [ContinuousMul β] (hf : StronglyMeasurable f) (c : β) :
    StronglyMeasurable fun x => f x * c :=
  hf.mul stronglyMeasurable_const
#align measure_theory.strongly_measurable.mul_const MeasureTheory.StronglyMeasurable.mul_const
#align measure_theory.strongly_measurable.add_const MeasureTheory.StronglyMeasurable.add_const

@[to_additive (attr := measurability)]
theorem const_mul [Mul β] [ContinuousMul β] (hf : StronglyMeasurable f) (c : β) :
    StronglyMeasurable fun x => c * f x :=
  stronglyMeasurable_const.mul hf
#align measure_theory.strongly_measurable.const_mul MeasureTheory.StronglyMeasurable.const_mul
#align measure_theory.strongly_measurable.const_add MeasureTheory.StronglyMeasurable.const_add

@[to_additive (attr := aesop safe 20 apply (rule_sets := [Measurable])) const_nsmul]
protected theorem pow [Monoid β] [ContinuousMul β] (hf : StronglyMeasurable f) (n : ℕ) :
    StronglyMeasurable (f ^ n) :=
  ⟨fun k => hf.approx k ^ n, fun x => (hf.tendsto_approx x).pow n⟩

@[to_additive (attr := measurability)]
protected theorem inv [Inv β] [ContinuousInv β] (hf : StronglyMeasurable f) :
    StronglyMeasurable f⁻¹ :=
  ⟨fun n => (hf.approx n)⁻¹, fun x => (hf.tendsto_approx x).inv⟩
#align measure_theory.strongly_measurable.inv MeasureTheory.StronglyMeasurable.inv
#align measure_theory.strongly_measurable.neg MeasureTheory.StronglyMeasurable.neg

@[to_additive (attr := aesop safe 20 apply (rule_sets := [Measurable]))]
protected theorem div [Div β] [ContinuousDiv β] (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) : StronglyMeasurable (f / g) :=
  ⟨fun n => hf.approx n / hg.approx n, fun x => (hf.tendsto_approx x).div' (hg.tendsto_approx x)⟩
#align measure_theory.strongly_measurable.div MeasureTheory.StronglyMeasurable.div
#align measure_theory.strongly_measurable.sub MeasureTheory.StronglyMeasurable.sub

@[to_additive (attr := aesop safe 20 apply (rule_sets := [Measurable]))]
protected theorem smul {𝕜} [TopologicalSpace 𝕜] [SMul 𝕜 β] [ContinuousSMul 𝕜 β] {f : α → 𝕜}
    {g : α → β} (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    StronglyMeasurable fun x => f x • g x :=
  continuous_smul.comp_stronglyMeasurable (hf.prod_mk hg)
#align measure_theory.strongly_measurable.smul MeasureTheory.StronglyMeasurable.smul
#align measure_theory.strongly_measurable.vadd MeasureTheory.StronglyMeasurable.vadd

@[to_additive (attr := measurability)]
protected theorem const_smul {𝕜} [SMul 𝕜 β] [ContinuousConstSMul 𝕜 β] (hf : StronglyMeasurable f)
    (c : 𝕜) : StronglyMeasurable (c • f) :=
  ⟨fun n => c • hf.approx n, fun x => (hf.tendsto_approx x).const_smul c⟩
#align measure_theory.strongly_measurable.const_smul MeasureTheory.StronglyMeasurable.const_smul

@[to_additive (attr := measurability)]
protected theorem const_smul' {𝕜} [SMul 𝕜 β] [ContinuousConstSMul 𝕜 β] (hf : StronglyMeasurable f)
    (c : 𝕜) : StronglyMeasurable fun x => c • f x :=
  hf.const_smul c
#align measure_theory.strongly_measurable.const_smul' MeasureTheory.StronglyMeasurable.const_smul'

@[to_additive (attr := measurability)]
protected theorem smul_const {𝕜} [TopologicalSpace 𝕜] [SMul 𝕜 β] [ContinuousSMul 𝕜 β] {f : α → 𝕜}
    (hf : StronglyMeasurable f) (c : β) : StronglyMeasurable fun x => f x • c :=
  continuous_smul.comp_stronglyMeasurable (hf.prod_mk stronglyMeasurable_const)
#align measure_theory.strongly_measurable.smul_const MeasureTheory.StronglyMeasurable.smul_const
#align measure_theory.strongly_measurable.vadd_const MeasureTheory.StronglyMeasurable.vadd_const

/-- In a normed vector space, the addition of a measurable function and a strongly measurable
function is measurable. Note that this is not true without further second-countability assumptions
for the addition of two measurable functions. -/
theorem _root_.Measurable.add_stronglyMeasurable
    {α E : Type*} {_ : MeasurableSpace α} [AddGroup E] [TopologicalSpace E]
    [MeasurableSpace E] [BorelSpace E] [ContinuousAdd E] [PseudoMetrizableSpace E]
    {g f : α → E} (hg : Measurable g) (hf : StronglyMeasurable f) :
    Measurable (g + f) := by
  rcases hf with ⟨φ, hφ⟩
  have : Tendsto (fun n x ↦ g x + φ n x) atTop (𝓝 (g + f)) :=
    tendsto_pi_nhds.2 (fun x ↦ tendsto_const_nhds.add (hφ x))
  apply measurable_of_tendsto_metrizable (fun n ↦ ?_) this
  exact hg.add_simpleFunc _

/-- In a normed vector space, the subtraction of a measurable function and a strongly measurable
function is measurable. Note that this is not true without further second-countability assumptions
for the subtraction of two measurable functions. -/
theorem _root_.Measurable.sub_stronglyMeasurable
    {α E : Type*} {_ : MeasurableSpace α} [AddCommGroup E] [TopologicalSpace E]
    [MeasurableSpace E] [BorelSpace E] [ContinuousAdd E] [ContinuousNeg E] [PseudoMetrizableSpace E]
    {g f : α → E} (hg : Measurable g) (hf : StronglyMeasurable f) :
    Measurable (g - f) := by
  rw [sub_eq_add_neg]
  exact hg.add_stronglyMeasurable hf.neg

/-- In a normed vector space, the addition of a strongly measurable function and a measurable
function is measurable. Note that this is not true without further second-countability assumptions
for the addition of two measurable functions. -/
theorem _root_.Measurable.stronglyMeasurable_add
    {α E : Type*} {_ : MeasurableSpace α} [AddGroup E] [TopologicalSpace E]
    [MeasurableSpace E] [BorelSpace E] [ContinuousAdd E] [PseudoMetrizableSpace E]
    {g f : α → E} (hg : Measurable g) (hf : StronglyMeasurable f) :
    Measurable (f + g) := by
  rcases hf with ⟨φ, hφ⟩
  have : Tendsto (fun n x ↦ φ n x + g x) atTop (𝓝 (f + g)) :=
    tendsto_pi_nhds.2 (fun x ↦ (hφ x).add tendsto_const_nhds)
  apply measurable_of_tendsto_metrizable (fun n ↦ ?_) this
  exact hg.simpleFunc_add _

end Arithmetic

section MulAction

variable {M G G₀ : Type*}
variable [TopologicalSpace β]
variable [Monoid M] [MulAction M β] [ContinuousConstSMul M β]
variable [Group G] [MulAction G β] [ContinuousConstSMul G β]
variable [GroupWithZero G₀] [MulAction G₀ β] [ContinuousConstSMul G₀ β]

theorem _root_.stronglyMeasurable_const_smul_iff {m : MeasurableSpace α} (c : G) :
    (StronglyMeasurable fun x => c • f x) ↔ StronglyMeasurable f :=
  ⟨fun h => by simpa only [inv_smul_smul] using h.const_smul' c⁻¹, fun h => h.const_smul c⟩
#align strongly_measurable_const_smul_iff stronglyMeasurable_const_smul_iff

nonrec theorem _root_.IsUnit.stronglyMeasurable_const_smul_iff {_ : MeasurableSpace α} {c : M}
    (hc : IsUnit c) :
    (StronglyMeasurable fun x => c • f x) ↔ StronglyMeasurable f :=
  let ⟨u, hu⟩ := hc
  hu ▸ stronglyMeasurable_const_smul_iff u
#align is_unit.strongly_measurable_const_smul_iff IsUnit.stronglyMeasurable_const_smul_iff

theorem _root_.stronglyMeasurable_const_smul_iff₀ {_ : MeasurableSpace α} {c : G₀} (hc : c ≠ 0) :
    (StronglyMeasurable fun x => c • f x) ↔ StronglyMeasurable f :=
  (IsUnit.mk0 _ hc).stronglyMeasurable_const_smul_iff
#align strongly_measurable_const_smul_iff₀ stronglyMeasurable_const_smul_iff₀

end MulAction

section Order

variable [MeasurableSpace α] [TopologicalSpace β]

open Filter

open Filter

@[aesop safe 20 (rule_sets := [Measurable])]
protected theorem sup [Sup β] [ContinuousSup β] (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) : StronglyMeasurable (f ⊔ g) :=
  ⟨fun n => hf.approx n ⊔ hg.approx n, fun x =>
    (hf.tendsto_approx x).sup_nhds (hg.tendsto_approx x)⟩
#align measure_theory.strongly_measurable.sup MeasureTheory.StronglyMeasurable.sup

@[aesop safe 20 (rule_sets := [Measurable])]
protected theorem inf [Inf β] [ContinuousInf β] (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) : StronglyMeasurable (f ⊓ g) :=
  ⟨fun n => hf.approx n ⊓ hg.approx n, fun x =>
    (hf.tendsto_approx x).inf_nhds (hg.tendsto_approx x)⟩
#align measure_theory.strongly_measurable.inf MeasureTheory.StronglyMeasurable.inf

end Order

/-!
### Big operators: `∏` and `∑`
-/


section Monoid

variable {M : Type*} [Monoid M] [TopologicalSpace M] [ContinuousMul M] {m : MeasurableSpace α}

@[to_additive (attr := measurability)]
theorem _root_.List.stronglyMeasurable_prod' (l : List (α → M))
    (hl : ∀ f ∈ l, StronglyMeasurable f) : StronglyMeasurable l.prod := by
  induction' l with f l ihl; · exact stronglyMeasurable_one
  rw [List.forall_mem_cons] at hl
  rw [List.prod_cons]
  exact hl.1.mul (ihl hl.2)
#align list.strongly_measurable_prod' List.stronglyMeasurable_prod'
#align list.strongly_measurable_sum' List.stronglyMeasurable_sum'

@[to_additive (attr := measurability)]
theorem _root_.List.stronglyMeasurable_prod (l : List (α → M))
    (hl : ∀ f ∈ l, StronglyMeasurable f) :
    StronglyMeasurable fun x => (l.map fun f : α → M => f x).prod := by
  simpa only [← Pi.list_prod_apply] using l.stronglyMeasurable_prod' hl
#align list.strongly_measurable_prod List.stronglyMeasurable_prod
#align list.strongly_measurable_sum List.stronglyMeasurable_sum

end Monoid

section CommMonoid

variable {M : Type*} [CommMonoid M] [TopologicalSpace M] [ContinuousMul M] {m : MeasurableSpace α}

@[to_additive (attr := measurability)]
theorem _root_.Multiset.stronglyMeasurable_prod' (l : Multiset (α → M))
    (hl : ∀ f ∈ l, StronglyMeasurable f) : StronglyMeasurable l.prod := by
  rcases l with ⟨l⟩
  simpa using l.stronglyMeasurable_prod' (by simpa using hl)
#align multiset.strongly_measurable_prod' Multiset.stronglyMeasurable_prod'
#align multiset.strongly_measurable_sum' Multiset.stronglyMeasurable_sum'

@[to_additive (attr := measurability)]
theorem _root_.Multiset.stronglyMeasurable_prod (s : Multiset (α → M))
    (hs : ∀ f ∈ s, StronglyMeasurable f) :
    StronglyMeasurable fun x => (s.map fun f : α → M => f x).prod := by
  simpa only [← Pi.multiset_prod_apply] using s.stronglyMeasurable_prod' hs
#align multiset.strongly_measurable_prod Multiset.stronglyMeasurable_prod
#align multiset.strongly_measurable_sum Multiset.stronglyMeasurable_sum

@[to_additive (attr := measurability)]
theorem _root_.Finset.stronglyMeasurable_prod' {ι : Type*} {f : ι → α → M} (s : Finset ι)
    (hf : ∀ i ∈ s, StronglyMeasurable (f i)) : StronglyMeasurable (∏ i in s, f i) :=
  Finset.prod_induction _ _ (fun _a _b ha hb => ha.mul hb) (@stronglyMeasurable_one α M _ _ _) hf
#align finset.strongly_measurable_prod' Finset.stronglyMeasurable_prod'
#align finset.strongly_measurable_sum' Finset.stronglyMeasurable_sum'

@[to_additive (attr := measurability)]
theorem _root_.Finset.stronglyMeasurable_prod {ι : Type*} {f : ι → α → M} (s : Finset ι)
    (hf : ∀ i ∈ s, StronglyMeasurable (f i)) : StronglyMeasurable fun a => ∏ i in s, f i a := by
  simpa only [← Finset.prod_apply] using s.stronglyMeasurable_prod' hf
#align finset.strongly_measurable_prod Finset.stronglyMeasurable_prod
#align finset.strongly_measurable_sum Finset.stronglyMeasurable_sum

end CommMonoid

/-- The range of a strongly measurable function is separable. -/
protected theorem isSeparable_range {m : MeasurableSpace α} [TopologicalSpace β]
    (hf : StronglyMeasurable f) : TopologicalSpace.IsSeparable (range f) := by
  have : IsSeparable (closure (⋃ n, range (hf.approx n))) :=
    .closure <| .iUnion fun n => (hf.approx n).finite_range.isSeparable
  apply this.mono
  rintro _ ⟨x, rfl⟩
  apply mem_closure_of_tendsto (hf.tendsto_approx x)
  filter_upwards with n
  apply mem_iUnion_of_mem n
  exact mem_range_self _
#align measure_theory.strongly_measurable.is_separable_range MeasureTheory.StronglyMeasurable.isSeparable_range

theorem separableSpace_range_union_singleton {_ : MeasurableSpace α} [TopologicalSpace β]
    [PseudoMetrizableSpace β] (hf : StronglyMeasurable f) {b : β} :
    SeparableSpace (range f ∪ {b} : Set β) :=
  letI := pseudoMetrizableSpacePseudoMetric β
  (hf.isSeparable_range.union (finite_singleton _).isSeparable).separableSpace
#align measure_theory.strongly_measurable.separable_space_range_union_singleton MeasureTheory.StronglyMeasurable.separableSpace_range_union_singleton

section SecondCountableStronglyMeasurable

variable {mα : MeasurableSpace α} [MeasurableSpace β]

/-- In a space with second countable topology, measurable implies strongly measurable. -/
@[aesop 90% apply (rule_sets := [Measurable])]
theorem _root_.Measurable.stronglyMeasurable [TopologicalSpace β] [PseudoMetrizableSpace β]
    [SecondCountableTopology β] [OpensMeasurableSpace β] (hf : Measurable f) :
    StronglyMeasurable f := by
  letI := pseudoMetrizableSpacePseudoMetric β
  nontriviality β; inhabit β
  exact ⟨SimpleFunc.approxOn f hf Set.univ default (Set.mem_univ _), fun x ↦
    SimpleFunc.tendsto_approxOn hf (Set.mem_univ _) (by rw [closure_univ]; simp)⟩
#align measurable.strongly_measurable Measurable.stronglyMeasurable

/-- In a space with second countable topology, strongly measurable and measurable are equivalent. -/
theorem _root_.stronglyMeasurable_iff_measurable [TopologicalSpace β] [MetrizableSpace β]
    [BorelSpace β] [SecondCountableTopology β] : StronglyMeasurable f ↔ Measurable f :=
  ⟨fun h => h.measurable, fun h => Measurable.stronglyMeasurable h⟩
#align strongly_measurable_iff_measurable stronglyMeasurable_iff_measurable

@[measurability]
theorem _root_.stronglyMeasurable_id [TopologicalSpace α] [PseudoMetrizableSpace α]
    [OpensMeasurableSpace α] [SecondCountableTopology α] : StronglyMeasurable (id : α → α) :=
  measurable_id.stronglyMeasurable
#align strongly_measurable_id stronglyMeasurable_id

end SecondCountableStronglyMeasurable

/-- A function is strongly measurable if and only if it is measurable and has separable
range. -/
theorem _root_.stronglyMeasurable_iff_measurable_separable {m : MeasurableSpace α}
    [TopologicalSpace β] [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β] :
    StronglyMeasurable f ↔ Measurable f ∧ IsSeparable (range f) := by
  refine ⟨fun H ↦ ⟨H.measurable, H.isSeparable_range⟩, fun ⟨Hm, Hsep⟩  ↦ ?_⟩
  have := Hsep.secondCountableTopology
  have Hm' : StronglyMeasurable (rangeFactorization f) := Hm.subtype_mk.stronglyMeasurable
  exact continuous_subtype_val.comp_stronglyMeasurable Hm'
#align strongly_measurable_iff_measurable_separable stronglyMeasurable_iff_measurable_separable

/-- A continuous function is strongly measurable when either the source space or the target space
is second-countable. -/
theorem _root_.Continuous.stronglyMeasurable [MeasurableSpace α] [TopologicalSpace α]
    [OpensMeasurableSpace α] [TopologicalSpace β] [PseudoMetrizableSpace β]
    [h : SecondCountableTopologyEither α β] {f : α → β} (hf : Continuous f) :
    StronglyMeasurable f := by
  borelize β
  cases h.out
  · rw [stronglyMeasurable_iff_measurable_separable]
    refine' ⟨hf.measurable, _⟩
    exact isSeparable_range hf
  · exact hf.measurable.stronglyMeasurable
#align continuous.strongly_measurable Continuous.stronglyMeasurable

/-- A continuous function whose support is contained in a compact set is strongly measurable. -/
@[to_additive]
theorem _root_.Continuous.stronglyMeasurable_of_mulSupport_subset_isCompact
    [MeasurableSpace α] [TopologicalSpace α] [OpensMeasurableSpace α] [MeasurableSpace β]
    [TopologicalSpace β] [PseudoMetrizableSpace β] [BorelSpace β] [One β] {f : α → β}
    (hf : Continuous f) {k : Set α} (hk : IsCompact k)
    (h'f : mulSupport f ⊆ k) : StronglyMeasurable f := by
  letI : PseudoMetricSpace β := pseudoMetrizableSpacePseudoMetric β
  rw [stronglyMeasurable_iff_measurable_separable]
  exact ⟨hf.measurable, (isCompact_range_of_mulSupport_subset_isCompact hf hk h'f).isSeparable⟩

/-- A continuous function with compact support is strongly measurable. -/
@[to_additive]
theorem _root_.Continuous.stronglyMeasurable_of_hasCompactMulSupport
    [MeasurableSpace α] [TopologicalSpace α] [OpensMeasurableSpace α] [MeasurableSpace β]
    [TopologicalSpace β] [PseudoMetrizableSpace β] [BorelSpace β] [One β] {f : α → β}
    (hf : Continuous f) (h'f : HasCompactMulSupport f) : StronglyMeasurable f :=
  hf.stronglyMeasurable_of_mulSupport_subset_isCompact h'f (subset_mulTSupport f)

/-- A continuous function with compact support on a product space is strongly measurable for the
product sigma-algebra. The subtlety is that we do not assume that the spaces are separable, so the
product of the Borel sigma algebras might not contain all open sets, but still it contains enough
of them to approximate compactly supported continuous functions. -/
lemma _root_.HasCompactSupport.stronglyMeasurable_of_prod {X Y : Type*} [Zero α]
    [TopologicalSpace X] [TopologicalSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y] [TopologicalSpace α] [PseudoMetrizableSpace α]
    {f : X × Y → α} (hf : Continuous f) (h'f : HasCompactSupport f) :
    StronglyMeasurable f := by
  borelize α
  apply stronglyMeasurable_iff_measurable_separable.2 ⟨h'f.measurable_of_prod hf, ?_⟩
  letI : PseudoMetricSpace α := pseudoMetrizableSpacePseudoMetric α
  exact IsCompact.isSeparable (s := range f) (h'f.isCompact_range hf)

/-- If `g` is a topological embedding, then `f` is strongly measurable iff `g ∘ f` is. -/
theorem _root_.Embedding.comp_stronglyMeasurable_iff {m : MeasurableSpace α} [TopologicalSpace β]
    [PseudoMetrizableSpace β] [TopologicalSpace γ] [PseudoMetrizableSpace γ] {g : β → γ} {f : α → β}
    (hg : Embedding g) : (StronglyMeasurable fun x => g (f x)) ↔ StronglyMeasurable f := by
  letI := pseudoMetrizableSpacePseudoMetric γ
  borelize β γ
  refine'
    ⟨fun H => stronglyMeasurable_iff_measurable_separable.2 ⟨_, _⟩, fun H =>
      hg.continuous.comp_stronglyMeasurable H⟩
  · let G : β → range g := rangeFactorization g
    have hG : ClosedEmbedding G :=
      { hg.codRestrict _ _ with
        isClosed_range := by
          rw [surjective_onto_range.range_eq]
          exact isClosed_univ }
    have : Measurable (G ∘ f) := Measurable.subtype_mk H.measurable
    exact hG.measurableEmbedding.measurable_comp_iff.1 this
  · have : IsSeparable (g ⁻¹' range (g ∘ f)) := hg.isSeparable_preimage H.isSeparable_range
    rwa [range_comp, hg.inj.preimage_image] at this
#align embedding.comp_strongly_measurable_iff Embedding.comp_stronglyMeasurable_iff

/-- A sequential limit of strongly measurable functions is strongly measurable. -/
theorem _root_.stronglyMeasurable_of_tendsto {ι : Type*} {m : MeasurableSpace α}
    [TopologicalSpace β] [PseudoMetrizableSpace β] (u : Filter ι) [NeBot u] [IsCountablyGenerated u]
    {f : ι → α → β} {g : α → β} (hf : ∀ i, StronglyMeasurable (f i)) (lim : Tendsto f u (𝓝 g)) :
    StronglyMeasurable g := by
  borelize β
  refine' stronglyMeasurable_iff_measurable_separable.2 ⟨_, _⟩
  · exact measurable_of_tendsto_metrizable' u (fun i => (hf i).measurable) lim
  · rcases u.exists_seq_tendsto with ⟨v, hv⟩
    have : IsSeparable (closure (⋃ i, range (f (v i)))) :=
      .closure <| .iUnion fun i => (hf (v i)).isSeparable_range
    apply this.mono
    rintro _ ⟨x, rfl⟩
    rw [tendsto_pi_nhds] at lim
    apply mem_closure_of_tendsto ((lim x).comp hv)
    filter_upwards with n
    apply mem_iUnion_of_mem n
    exact mem_range_self _
#align strongly_measurable_of_tendsto stronglyMeasurable_of_tendsto

protected theorem piecewise {m : MeasurableSpace α} [TopologicalSpace β] {s : Set α}
    {_ : DecidablePred (· ∈ s)} (hs : MeasurableSet s) (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) : StronglyMeasurable (Set.piecewise s f g) := by
  refine' ⟨fun n => SimpleFunc.piecewise s hs (hf.approx n) (hg.approx n), fun x => _⟩
  by_cases hx : x ∈ s
  · simpa [@Set.piecewise_eq_of_mem _ _ _ _ _ (fun _ => Classical.propDecidable _) _ hx,
      hx] using hf.tendsto_approx x
  · simpa [@Set.piecewise_eq_of_not_mem _ _ _ _ _ (fun _ => Classical.propDecidable _) _ hx,
      hx] using hg.tendsto_approx x
#align measure_theory.strongly_measurable.piecewise MeasureTheory.StronglyMeasurable.piecewise

/-- this is slightly different from `StronglyMeasurable.piecewise`. It can be used to show
`StronglyMeasurable (ite (x=0) 0 1)` by
`exact StronglyMeasurable.ite (measurableSet_singleton 0) stronglyMeasurable_const
stronglyMeasurable_const`, but replacing `StronglyMeasurable.ite` by
`StronglyMeasurable.piecewise` in that example proof does not work. -/
protected theorem ite {_ : MeasurableSpace α} [TopologicalSpace β] {p : α → Prop}
    {_ : DecidablePred p} (hp : MeasurableSet { a : α | p a }) (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) : StronglyMeasurable fun x => ite (p x) (f x) (g x) :=
  StronglyMeasurable.piecewise hp hf hg
#align measure_theory.strongly_measurable.ite MeasureTheory.StronglyMeasurable.ite

@[measurability]
theorem _root_.MeasurableEmbedding.stronglyMeasurable_extend {f : α → β} {g : α → γ} {g' : γ → β}
    {mα : MeasurableSpace α} {mγ : MeasurableSpace γ} [TopologicalSpace β]
    (hg : MeasurableEmbedding g) (hf : StronglyMeasurable f) (hg' : StronglyMeasurable g') :
    StronglyMeasurable (Function.extend g f g') := by
  refine' ⟨fun n => SimpleFunc.extend (hf.approx n) g hg (hg'.approx n), _⟩
  intro x
  by_cases hx : ∃ y, g y = x
  · rcases hx with ⟨y, rfl⟩
    simpa only [SimpleFunc.extend_apply, hg.injective, Injective.extend_apply] using
      hf.tendsto_approx y
  · simpa only [hx, SimpleFunc.extend_apply', not_false_iff, extend_apply'] using
      hg'.tendsto_approx x
#align measurable_embedding.strongly_measurable_extend MeasurableEmbedding.stronglyMeasurable_extend

theorem _root_.MeasurableEmbedding.exists_stronglyMeasurable_extend {f : α → β} {g : α → γ}
    {_ : MeasurableSpace α} {_ : MeasurableSpace γ} [TopologicalSpace β]
    (hg : MeasurableEmbedding g) (hf : StronglyMeasurable f) (hne : γ → Nonempty β) :
    ∃ f' : γ → β, StronglyMeasurable f' ∧ f' ∘ g = f :=
  ⟨Function.extend g f fun x => Classical.choice (hne x),
    hg.stronglyMeasurable_extend hf (stronglyMeasurable_const' fun _ _ => rfl),
    funext fun _ => hg.injective.extend_apply _ _ _⟩
#align measurable_embedding.exists_strongly_measurable_extend MeasurableEmbedding.exists_stronglyMeasurable_extend

theorem _root_.stronglyMeasurable_of_stronglyMeasurable_union_cover {m : MeasurableSpace α}
    [TopologicalSpace β] {f : α → β} (s t : Set α) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (h : univ ⊆ s ∪ t) (hc : StronglyMeasurable fun a : s => f a)
    (hd : StronglyMeasurable fun a : t => f a) : StronglyMeasurable f := by
  nontriviality β; inhabit β
  suffices Function.extend Subtype.val (fun x : s ↦ f x)
      (Function.extend (↑) (fun x : t ↦ f x) fun _ ↦ default) = f from
    this ▸ (MeasurableEmbedding.subtype_coe hs).stronglyMeasurable_extend hc <|
      (MeasurableEmbedding.subtype_coe ht).stronglyMeasurable_extend hd stronglyMeasurable_const
  ext x
  by_cases hxs : x ∈ s
  · lift x to s using hxs
    simp [Subtype.coe_injective.extend_apply]
  · lift x to t using (h trivial).resolve_left hxs
    rw [extend_apply', Subtype.coe_injective.extend_apply]
    exact fun ⟨y, hy⟩ ↦ hxs <| hy ▸ y.2
#align strongly_measurable_of_strongly_measurable_union_cover stronglyMeasurable_of_stronglyMeasurable_union_cover

theorem _root_.stronglyMeasurable_of_restrict_of_restrict_compl {_ : MeasurableSpace α}
    [TopologicalSpace β] {f : α → β} {s : Set α} (hs : MeasurableSet s)
    (h₁ : StronglyMeasurable (s.restrict f)) (h₂ : StronglyMeasurable (sᶜ.restrict f)) :
    StronglyMeasurable f :=
  stronglyMeasurable_of_stronglyMeasurable_union_cover s sᶜ hs hs.compl (union_compl_self s).ge h₁
    h₂
#align strongly_measurable_of_restrict_of_restrict_compl stronglyMeasurable_of_restrict_of_restrict_compl

@[measurability]
protected theorem indicator {_ : MeasurableSpace α} [TopologicalSpace β] [Zero β]
    (hf : StronglyMeasurable f) {s : Set α} (hs : MeasurableSet s) :
    StronglyMeasurable (s.indicator f) :=
  hf.piecewise hs stronglyMeasurable_const
#align measure_theory.strongly_measurable.indicator MeasureTheory.StronglyMeasurable.indicator

@[aesop safe 20 apply (rule_sets := [Measurable])]
protected theorem dist {_ : MeasurableSpace α} {β : Type*} [PseudoMetricSpace β] {f g : α → β}
    (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    StronglyMeasurable fun x => dist (f x) (g x) :=
  continuous_dist.comp_stronglyMeasurable (hf.prod_mk hg)
#align measure_theory.strongly_measurable.dist MeasureTheory.StronglyMeasurable.dist

@[measurability]
protected theorem norm {_ : MeasurableSpace α} {β : Type*} [SeminormedAddCommGroup β] {f : α → β}
    (hf : StronglyMeasurable f) : StronglyMeasurable fun x => ‖f x‖ :=
  continuous_norm.comp_stronglyMeasurable hf
#align measure_theory.strongly_measurable.norm MeasureTheory.StronglyMeasurable.norm

@[measurability]
protected theorem nnnorm {_ : MeasurableSpace α} {β : Type*} [SeminormedAddCommGroup β] {f : α → β}
    (hf : StronglyMeasurable f) : StronglyMeasurable fun x => ‖f x‖₊ :=
  continuous_nnnorm.comp_stronglyMeasurable hf
#align measure_theory.strongly_measurable.nnnorm MeasureTheory.StronglyMeasurable.nnnorm

@[measurability]
protected theorem ennnorm {_ : MeasurableSpace α} {β : Type*} [SeminormedAddCommGroup β]
    {f : α → β} (hf : StronglyMeasurable f) : Measurable fun a => (‖f a‖₊ : ℝ≥0∞) :=
  (ENNReal.continuous_coe.comp_stronglyMeasurable hf.nnnorm).measurable
#align measure_theory.strongly_measurable.ennnorm MeasureTheory.StronglyMeasurable.ennnorm

@[measurability]
protected theorem real_toNNReal {_ : MeasurableSpace α} {f : α → ℝ} (hf : StronglyMeasurable f) :
    StronglyMeasurable fun x => (f x).toNNReal :=
  continuous_real_toNNReal.comp_stronglyMeasurable hf
#align measure_theory.strongly_measurable.real_to_nnreal MeasureTheory.StronglyMeasurable.real_toNNReal

theorem measurableSet_eq_fun {m : MeasurableSpace α} {E} [TopologicalSpace E] [MetrizableSpace E]
    {f g : α → E} (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    MeasurableSet { x | f x = g x } := by
  borelize (E × E)
  exact (hf.prod_mk hg).measurable isClosed_diagonal.measurableSet
#align measure_theory.strongly_measurable.measurable_set_eq_fun MeasureTheory.StronglyMeasurable.measurableSet_eq_fun

theorem measurableSet_lt {m : MeasurableSpace α} [TopologicalSpace β] [LinearOrder β]
    [OrderClosedTopology β] [PseudoMetrizableSpace β] {f g : α → β} (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) : MeasurableSet { a | f a < g a } := by
  borelize (β × β)
  exact (hf.prod_mk hg).measurable isOpen_lt_prod.measurableSet
#align measure_theory.strongly_measurable.measurable_set_lt MeasureTheory.StronglyMeasurable.measurableSet_lt

theorem measurableSet_le {m : MeasurableSpace α} [TopologicalSpace β] [Preorder β]
    [OrderClosedTopology β] [PseudoMetrizableSpace β] {f g : α → β} (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) : MeasurableSet { a | f a ≤ g a } := by
  borelize (β × β)
  exact (hf.prod_mk hg).measurable isClosed_le_prod.measurableSet
#align measure_theory.strongly_measurable.measurable_set_le MeasureTheory.StronglyMeasurable.measurableSet_le

theorem stronglyMeasurable_in_set {m : MeasurableSpace α} [TopologicalSpace β] [Zero β] {s : Set α}
    {f : α → β} (hs : MeasurableSet s) (hf : StronglyMeasurable f)
    (hf_zero : ∀ x, x ∉ s → f x = 0) :
    ∃ fs : ℕ → α →ₛ β,
      (∀ x, Tendsto (fun n => fs n x) atTop (𝓝 (f x))) ∧ ∀ x ∉ s, ∀ n, fs n x = 0 := by
  let g_seq_s : ℕ → @SimpleFunc α m β := fun n => (hf.approx n).restrict s
  have hg_eq : ∀ x ∈ s, ∀ n, g_seq_s n x = hf.approx n x := by
    intro x hx n
    rw [SimpleFunc.coe_restrict _ hs, Set.indicator_of_mem hx]
  have hg_zero : ∀ x ∉ s, ∀ n, g_seq_s n x = 0 := by
    intro x hx n
    rw [SimpleFunc.coe_restrict _ hs, Set.indicator_of_not_mem hx]
  refine' ⟨g_seq_s, fun x => _, hg_zero⟩
  by_cases hx : x ∈ s
  · simp_rw [hg_eq x hx]
    exact hf.tendsto_approx x
  · simp_rw [hg_zero x hx, hf_zero x hx]
    exact tendsto_const_nhds
#align measure_theory.strongly_measurable.strongly_measurable_in_set MeasureTheory.StronglyMeasurable.stronglyMeasurable_in_set

/-- If the restriction to a set `s` of a σ-algebra `m` is included in the restriction to `s` of
another σ-algebra `m₂` (hypothesis `hs`), the set `s` is `m` measurable and a function `f` supported
on `s` is `m`-strongly-measurable, then `f` is also `m₂`-strongly-measurable. -/
theorem stronglyMeasurable_of_measurableSpace_le_on {α E} {m m₂ : MeasurableSpace α}
    [TopologicalSpace E] [Zero E] {s : Set α} {f : α → E} (hs_m : MeasurableSet[m] s)
    (hs : ∀ t, MeasurableSet[m] (s ∩ t) → MeasurableSet[m₂] (s ∩ t))
    (hf : StronglyMeasurable[m] f) (hf_zero : ∀ x ∉ s, f x = 0) :
    StronglyMeasurable[m₂] f := by
  have hs_m₂ : MeasurableSet[m₂] s := by
    rw [← Set.inter_univ s]
    refine' hs Set.univ _
    rwa [Set.inter_univ]
  obtain ⟨g_seq_s, hg_seq_tendsto, hg_seq_zero⟩ := stronglyMeasurable_in_set hs_m hf hf_zero
  let g_seq_s₂ : ℕ → @SimpleFunc α m₂ E := fun n =>
    { toFun := g_seq_s n
      measurableSet_fiber' := fun x => by
        rw [← Set.inter_univ (g_seq_s n ⁻¹' {x}), ← Set.union_compl_self s,
          Set.inter_union_distrib_left, Set.inter_comm (g_seq_s n ⁻¹' {x})]
        refine' MeasurableSet.union (hs _ (hs_m.inter _)) _
        · exact @SimpleFunc.measurableSet_fiber _ _ m _ _
        by_cases hx : x = 0
        · suffices g_seq_s n ⁻¹' {x} ∩ sᶜ = sᶜ by
            rw [this]
            exact hs_m₂.compl
          ext1 y
          rw [hx, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
          exact ⟨fun h => h.2, fun h => ⟨hg_seq_zero y h n, h⟩⟩
        · suffices g_seq_s n ⁻¹' {x} ∩ sᶜ = ∅ by
            rw [this]
            exact MeasurableSet.empty
          ext1 y
          simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_compl_iff,
            mem_empty_iff_false, iff_false_iff, not_and, not_not_mem]
          refine' Function.mtr fun hys => _
          rw [hg_seq_zero y hys n]
          exact Ne.symm hx
      finite_range' := @SimpleFunc.finite_range _ _ m (g_seq_s n) }
  exact ⟨g_seq_s₂, hg_seq_tendsto⟩
#align measure_theory.strongly_measurable.strongly_measurable_of_measurable_space_le_on MeasureTheory.StronglyMeasurable.stronglyMeasurable_of_measurableSpace_le_on

/-- If a function `f` is strongly measurable w.r.t. a sub-σ-algebra `m` and the measure is σ-finite
on `m`, then there exists spanning measurable sets with finite measure on which `f` has bounded
norm. In particular, `f` is integrable on each of those sets. -/
theorem exists_spanning_measurableSet_norm_le [SeminormedAddCommGroup β] {m m0 : MeasurableSpace α}
    (hm : m ≤ m0) (hf : StronglyMeasurable[m] f) (μ : Measure α) [SigmaFinite (μ.trim hm)] :
    ∃ s : ℕ → Set α,
      (∀ n, MeasurableSet[m] (s n) ∧ μ (s n) < ∞ ∧ ∀ x ∈ s n, ‖f x‖ ≤ n) ∧
      ⋃ i, s i = Set.univ := by
  obtain ⟨s, hs, hs_univ⟩ := exists_spanning_measurableSet_le hf.nnnorm.measurable (μ.trim hm)
  refine ⟨s, fun n ↦ ⟨(hs n).1, (le_trim hm).trans_lt (hs n).2.1, fun x hx ↦ ?_⟩, hs_univ⟩
  have hx_nnnorm : ‖f x‖₊ ≤ n := (hs n).2.2 x hx
  rw [← coe_nnnorm]
  norm_cast
#align measure_theory.strongly_measurable.exists_spanning_measurable_set_norm_le MeasureTheory.StronglyMeasurable.exists_spanning_measurableSet_norm_le

end StronglyMeasurable

/-! ## Finitely strongly measurable functions -/


theorem finStronglyMeasurable_zero {α β} {m : MeasurableSpace α} {μ : Measure α} [Zero β]
    [TopologicalSpace β] : FinStronglyMeasurable (0 : α → β) μ :=
  ⟨0, by
    simp only [Pi.zero_apply, SimpleFunc.coe_zero, support_zero', measure_empty,
      zero_lt_top, forall_const],
    fun _ => tendsto_const_nhds⟩
#align measure_theory.fin_strongly_measurable_zero MeasureTheory.finStronglyMeasurable_zero

namespace FinStronglyMeasurable

variable {m0 : MeasurableSpace α} {μ : Measure α} {f g : α → β}

theorem aefinStronglyMeasurable [Zero β] [TopologicalSpace β] (hf : FinStronglyMeasurable f μ) :
    AEFinStronglyMeasurable f μ :=
  ⟨f, hf, ae_eq_refl f⟩
#align measure_theory.fin_strongly_measurable.ae_fin_strongly_measurable MeasureTheory.FinStronglyMeasurable.aefinStronglyMeasurable

section sequence

variable [Zero β] [TopologicalSpace β] (hf : FinStronglyMeasurable f μ)

/-- A sequence of simple functions such that `∀ x, Tendsto (fun n ↦ hf.approx n x) atTop (𝓝 (f x))`
and `∀ n, μ (support (hf.approx n)) < ∞`. These properties are given by
`FinStronglyMeasurable.tendsto_approx` and `FinStronglyMeasurable.fin_support_approx`. -/
protected noncomputable def approx : ℕ → α →ₛ β :=
  hf.choose
#align measure_theory.fin_strongly_measurable.approx MeasureTheory.FinStronglyMeasurable.approx

protected theorem fin_support_approx : ∀ n, μ (support (hf.approx n)) < ∞ :=
  hf.choose_spec.1
#align measure_theory.fin_strongly_measurable.fin_support_approx MeasureTheory.FinStronglyMeasurable.fin_support_approx

protected theorem tendsto_approx : ∀ x, Tendsto (fun n => hf.approx n x) atTop (𝓝 (f x)) :=
  hf.choose_spec.2
#align measure_theory.fin_strongly_measurable.tendsto_approx MeasureTheory.FinStronglyMeasurable.tendsto_approx

end sequence

/-- A finitely strongly measurable function is strongly measurable. -/
@[aesop 5% apply (rule_sets := [Measurable])]
protected theorem stronglyMeasurable [Zero β] [TopologicalSpace β]
    (hf : FinStronglyMeasurable f μ) : StronglyMeasurable f :=
  ⟨hf.approx, hf.tendsto_approx⟩
#align measure_theory.fin_strongly_measurable.strongly_measurable MeasureTheory.FinStronglyMeasurable.stronglyMeasurable

theorem exists_set_sigmaFinite [Zero β] [TopologicalSpace β] [T2Space β]
    (hf : FinStronglyMeasurable f μ) :
    ∃ t, MeasurableSet t ∧ (∀ x ∈ tᶜ, f x = 0) ∧ SigmaFinite (μ.restrict t) := by
  rcases hf with ⟨fs, hT_lt_top, h_approx⟩
  let T n := support (fs n)
  have hT_meas : ∀ n, MeasurableSet (T n) := fun n => SimpleFunc.measurableSet_support (fs n)
  let t := ⋃ n, T n
  refine' ⟨t, MeasurableSet.iUnion hT_meas, _, _⟩
  · have h_fs_zero : ∀ n, ∀ x ∈ tᶜ, fs n x = 0 := by
      intro n x hxt
      rw [Set.mem_compl_iff, Set.mem_iUnion, not_exists] at hxt
      simpa [T] using hxt n
    refine' fun x hxt => tendsto_nhds_unique (h_approx x) _
    rw [funext fun n => h_fs_zero n x hxt]
    exact tendsto_const_nhds
  · refine' ⟨⟨⟨fun n => tᶜ ∪ T n, fun _ => trivial, fun n => _, _⟩⟩⟩
    · rw [Measure.restrict_apply' (MeasurableSet.iUnion hT_meas), Set.union_inter_distrib_right,
        Set.compl_inter_self t, Set.empty_union]
      exact (measure_mono (Set.inter_subset_left _ _)).trans_lt (hT_lt_top n)
    · rw [← Set.union_iUnion tᶜ T]
      exact Set.compl_union_self _
#align measure_theory.fin_strongly_measurable.exists_set_sigma_finite MeasureTheory.FinStronglyMeasurable.exists_set_sigmaFinite

/-- A finitely strongly measurable function is measurable. -/
protected theorem measurable [Zero β] [TopologicalSpace β] [PseudoMetrizableSpace β]
    [MeasurableSpace β] [BorelSpace β] (hf : FinStronglyMeasurable f μ) : Measurable f :=
  hf.stronglyMeasurable.measurable
#align measure_theory.fin_strongly_measurable.measurable MeasureTheory.FinStronglyMeasurable.measurable

section Arithmetic

variable [TopologicalSpace β]

@[aesop safe 20 (rule_sets := [Measurable])]
protected theorem mul [MonoidWithZero β] [ContinuousMul β] (hf : FinStronglyMeasurable f μ)
    (hg : FinStronglyMeasurable g μ) : FinStronglyMeasurable (f * g) μ := by
  refine'
    ⟨fun n => hf.approx n * hg.approx n, _, fun x =>
      (hf.tendsto_approx x).mul (hg.tendsto_approx x)⟩
  intro n
  exact (measure_mono (support_mul_subset_left _ _)).trans_lt (hf.fin_support_approx n)
#align measure_theory.fin_strongly_measurable.mul MeasureTheory.FinStronglyMeasurable.mul

@[aesop safe 20 (rule_sets := [Measurable])]
protected theorem add [AddMonoid β] [ContinuousAdd β] (hf : FinStronglyMeasurable f μ)
    (hg : FinStronglyMeasurable g μ) : FinStronglyMeasurable (f + g) μ :=
  ⟨fun n => hf.approx n + hg.approx n, fun n =>
    (measure_mono (Function.support_add _ _)).trans_lt
      ((measure_union_le _ _).trans_lt
        (ENNReal.add_lt_top.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩)),
    fun x => (hf.tendsto_approx x).add (hg.tendsto_approx x)⟩
#align measure_theory.fin_strongly_measurable.add MeasureTheory.FinStronglyMeasurable.add

@[measurability]
protected theorem neg [AddGroup β] [TopologicalAddGroup β] (hf : FinStronglyMeasurable f μ) :
    FinStronglyMeasurable (-f) μ := by
  refine' ⟨fun n => -hf.approx n, fun n => _, fun x => (hf.tendsto_approx x).neg⟩
  suffices μ (Function.support fun x => -(hf.approx n) x) < ∞ by convert this
  rw [Function.support_neg (hf.approx n)]
  exact hf.fin_support_approx n
#align measure_theory.fin_strongly_measurable.neg MeasureTheory.FinStronglyMeasurable.neg

@[measurability]
protected theorem sub [AddGroup β] [ContinuousSub β] (hf : FinStronglyMeasurable f μ)
    (hg : FinStronglyMeasurable g μ) : FinStronglyMeasurable (f - g) μ :=
  ⟨fun n => hf.approx n - hg.approx n, fun n =>
    (measure_mono (Function.support_sub _ _)).trans_lt
      ((measure_union_le _ _).trans_lt
        (ENNReal.add_lt_top.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩)),
    fun x => (hf.tendsto_approx x).sub (hg.tendsto_approx x)⟩
#align measure_theory.fin_strongly_measurable.sub MeasureTheory.FinStronglyMeasurable.sub

@[measurability]
protected theorem const_smul {𝕜} [TopologicalSpace 𝕜] [AddMonoid β] [Monoid 𝕜]
    [DistribMulAction 𝕜 β] [ContinuousSMul 𝕜 β] (hf : FinStronglyMeasurable f μ) (c : 𝕜) :
    FinStronglyMeasurable (c • f) μ := by
  refine' ⟨fun n => c • hf.approx n, fun n => _, fun x => (hf.tendsto_approx x).const_smul c⟩
  rw [SimpleFunc.coe_smul]
  exact (measure_mono (support_const_smul_subset c _)).trans_lt (hf.fin_support_approx n)
#align measure_theory.fin_strongly_measurable.const_smul MeasureTheory.FinStronglyMeasurable.const_smul

end Arithmetic

section Order

variable [TopologicalSpace β] [Zero β]

@[aesop safe 20 (rule_sets := [Measurable])]
protected theorem sup [SemilatticeSup β] [ContinuousSup β] (hf : FinStronglyMeasurable f μ)
    (hg : FinStronglyMeasurable g μ) : FinStronglyMeasurable (f ⊔ g) μ := by
  refine'
    ⟨fun n => hf.approx n ⊔ hg.approx n, fun n => _, fun x =>
      (hf.tendsto_approx x).sup_nhds (hg.tendsto_approx x)⟩
  refine' (measure_mono (support_sup _ _)).trans_lt _
  exact measure_union_lt_top_iff.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩
#align measure_theory.fin_strongly_measurable.sup MeasureTheory.FinStronglyMeasurable.sup

@[aesop safe 20 (rule_sets := [Measurable])]
protected theorem inf [SemilatticeInf β] [ContinuousInf β] (hf : FinStronglyMeasurable f μ)
    (hg : FinStronglyMeasurable g μ) : FinStronglyMeasurable (f ⊓ g) μ := by
  refine'
    ⟨fun n => hf.approx n ⊓ hg.approx n, fun n => _, fun x =>
      (hf.tendsto_approx x).inf_nhds (hg.tendsto_approx x)⟩
  refine' (measure_mono (support_inf _ _)).trans_lt _
  exact measure_union_lt_top_iff.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩
#align measure_theory.fin_strongly_measurable.inf MeasureTheory.FinStronglyMeasurable.inf

end Order

end FinStronglyMeasurable

theorem finStronglyMeasurable_iff_stronglyMeasurable_and_exists_set_sigmaFinite {α β} {f : α → β}
    [TopologicalSpace β] [T2Space β] [Zero β] {_ : MeasurableSpace α} {μ : Measure α} :
    FinStronglyMeasurable f μ ↔
      StronglyMeasurable f ∧
        ∃ t, MeasurableSet t ∧ (∀ x ∈ tᶜ, f x = 0) ∧ SigmaFinite (μ.restrict t) :=
  ⟨fun hf => ⟨hf.stronglyMeasurable, hf.exists_set_sigmaFinite⟩, fun hf =>
    hf.1.finStronglyMeasurable_of_set_sigmaFinite hf.2.choose_spec.1 hf.2.choose_spec.2.1
      hf.2.choose_spec.2.2⟩
#align measure_theory.fin_strongly_measurable_iff_strongly_measurable_and_exists_set_sigma_finite MeasureTheory.finStronglyMeasurable_iff_stronglyMeasurable_and_exists_set_sigmaFinite

theorem aefinStronglyMeasurable_zero {α β} {_ : MeasurableSpace α} (μ : Measure α) [Zero β]
    [TopologicalSpace β] : AEFinStronglyMeasurable (0 : α → β) μ :=
  ⟨0, finStronglyMeasurable_zero, EventuallyEq.rfl⟩
#align measure_theory.ae_fin_strongly_measurable_zero MeasureTheory.aefinStronglyMeasurable_zero

/-! ## Almost everywhere strongly measurable functions -/

@[measurability]
theorem aestronglyMeasurable_const {α β} {_ : MeasurableSpace α} {μ : Measure α}
    [TopologicalSpace β] {b : β} : AEStronglyMeasurable (fun _ : α => b) μ :=
  stronglyMeasurable_const.aestronglyMeasurable
#align measure_theory.ae_strongly_measurable_const MeasureTheory.aestronglyMeasurable_const

@[to_additive (attr := measurability)]
theorem aestronglyMeasurable_one {α β} {_ : MeasurableSpace α} {μ : Measure α} [TopologicalSpace β]
    [One β] : AEStronglyMeasurable (1 : α → β) μ :=
  stronglyMeasurable_one.aestronglyMeasurable
#align measure_theory.ae_strongly_measurable_one MeasureTheory.aestronglyMeasurable_one
#align measure_theory.ae_strongly_measurable_zero MeasureTheory.aestronglyMeasurable_zero

@[simp]
theorem Subsingleton.aestronglyMeasurable {_ : MeasurableSpace α} [TopologicalSpace β]
    [Subsingleton β] {μ : Measure α} (f : α → β) : AEStronglyMeasurable f μ :=
  (Subsingleton.stronglyMeasurable f).aestronglyMeasurable
#align measure_theory.subsingleton.ae_strongly_measurable MeasureTheory.Subsingleton.aestronglyMeasurable

@[simp]
theorem Subsingleton.aestronglyMeasurable' {_ : MeasurableSpace α} [TopologicalSpace β]
    [Subsingleton α] {μ : Measure α} (f : α → β) : AEStronglyMeasurable f μ :=
  (Subsingleton.stronglyMeasurable' f).aestronglyMeasurable
#align measure_theory.subsingleton.ae_strongly_measurable' MeasureTheory.Subsingleton.aestronglyMeasurable'

@[simp]
theorem aestronglyMeasurable_zero_measure [MeasurableSpace α] [TopologicalSpace β] (f : α → β) :
    AEStronglyMeasurable f (0 : Measure α) := by
  nontriviality α
  inhabit α
  exact ⟨fun _ => f default, stronglyMeasurable_const, rfl⟩
#align measure_theory.ae_strongly_measurable_zero_measure MeasureTheory.aestronglyMeasurable_zero_measure

@[measurability]
theorem SimpleFunc.aestronglyMeasurable {_ : MeasurableSpace α} {μ : Measure α} [TopologicalSpace β]
    (f : α →ₛ β) : AEStronglyMeasurable f μ :=
  f.stronglyMeasurable.aestronglyMeasurable
#align measure_theory.simple_func.ae_strongly_measurable MeasureTheory.SimpleFunc.aestronglyMeasurable

namespace AEStronglyMeasurable

variable {m : MeasurableSpace α} {μ ν : Measure α} [TopologicalSpace β] [TopologicalSpace γ]
  {f g : α → β}

section Mk

/-- A `StronglyMeasurable` function such that `f =ᵐ[μ] hf.mk f`. See lemmas
`stronglyMeasurable_mk` and `ae_eq_mk`. -/
protected noncomputable def mk (f : α → β) (hf : AEStronglyMeasurable f μ) : α → β :=
  hf.choose
#align measure_theory.ae_strongly_measurable.mk MeasureTheory.AEStronglyMeasurable.mk

theorem stronglyMeasurable_mk (hf : AEStronglyMeasurable f μ) : StronglyMeasurable (hf.mk f) :=
  hf.choose_spec.1
#align measure_theory.ae_strongly_measurable.strongly_measurable_mk MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk

theorem measurable_mk [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
    (hf : AEStronglyMeasurable f μ) : Measurable (hf.mk f) :=
  hf.stronglyMeasurable_mk.measurable
#align measure_theory.ae_strongly_measurable.measurable_mk MeasureTheory.AEStronglyMeasurable.measurable_mk

theorem ae_eq_mk (hf : AEStronglyMeasurable f μ) : f =ᵐ[μ] hf.mk f :=
  hf.choose_spec.2
#align measure_theory.ae_strongly_measurable.ae_eq_mk MeasureTheory.AEStronglyMeasurable.ae_eq_mk

@[aesop 5% apply (rule_sets := [Measurable])]
protected theorem aemeasurable {β} [MeasurableSpace β] [TopologicalSpace β]
    [PseudoMetrizableSpace β] [BorelSpace β] {f : α → β} (hf : AEStronglyMeasurable f μ) :
    AEMeasurable f μ :=
  ⟨hf.mk f, hf.stronglyMeasurable_mk.measurable, hf.ae_eq_mk⟩
#align measure_theory.ae_strongly_measurable.ae_measurable MeasureTheory.AEStronglyMeasurable.aemeasurable

end Mk

theorem congr (hf : AEStronglyMeasurable f μ) (h : f =ᵐ[μ] g) : AEStronglyMeasurable g μ :=
  ⟨hf.mk f, hf.stronglyMeasurable_mk, h.symm.trans hf.ae_eq_mk⟩
#align measure_theory.ae_strongly_measurable.congr MeasureTheory.AEStronglyMeasurable.congr

theorem _root_.aestronglyMeasurable_congr (h : f =ᵐ[μ] g) :
    AEStronglyMeasurable f μ ↔ AEStronglyMeasurable g μ :=
  ⟨fun hf => hf.congr h, fun hg => hg.congr h.symm⟩
#align ae_strongly_measurable_congr aestronglyMeasurable_congr

theorem mono_measure {ν : Measure α} (hf : AEStronglyMeasurable f μ) (h : ν ≤ μ) :
    AEStronglyMeasurable f ν :=
  ⟨hf.mk f, hf.stronglyMeasurable_mk, Eventually.filter_mono (ae_mono h) hf.ae_eq_mk⟩
#align measure_theory.ae_strongly_measurable.mono_measure MeasureTheory.AEStronglyMeasurable.mono_measure

protected lemma mono_ac (h : ν ≪ μ) (hμ : AEStronglyMeasurable f μ) : AEStronglyMeasurable f ν :=
  let ⟨g, hg, hg'⟩ := hμ; ⟨g, hg, h.ae_eq hg'⟩
#align measure_theory.ae_strongly_measurable.mono' MeasureTheory.AEStronglyMeasurable.mono_ac
#align measure_theory.ae_strongly_measurable_of_absolutely_continuous MeasureTheory.AEStronglyMeasurable.mono_ac

@[deprecated] protected alias mono' := AEStronglyMeasurable.mono_ac

theorem mono_set {s t} (h : s ⊆ t) (ht : AEStronglyMeasurable f (μ.restrict t)) :
    AEStronglyMeasurable f (μ.restrict s) :=
  ht.mono_measure (restrict_mono h le_rfl)
#align measure_theory.ae_strongly_measurable.mono_set MeasureTheory.AEStronglyMeasurable.mono_set

protected theorem restrict (hfm : AEStronglyMeasurable f μ) {s} :
    AEStronglyMeasurable f (μ.restrict s) :=
  hfm.mono_measure Measure.restrict_le_self
#align measure_theory.ae_strongly_measurable.restrict MeasureTheory.AEStronglyMeasurable.restrict

theorem ae_mem_imp_eq_mk {s} (h : AEStronglyMeasurable f (μ.restrict s)) :
    ∀ᵐ x ∂μ, x ∈ s → f x = h.mk f x :=
  ae_imp_of_ae_restrict h.ae_eq_mk
#align measure_theory.ae_strongly_measurable.ae_mem_imp_eq_mk MeasureTheory.AEStronglyMeasurable.ae_mem_imp_eq_mk

/-- The composition of a continuous function and an ae strongly measurable function is ae strongly
measurable. -/
theorem _root_.Continuous.comp_aestronglyMeasurable {g : β → γ} {f : α → β} (hg : Continuous g)
    (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurable (fun x => g (f x)) μ :=
  ⟨_, hg.comp_stronglyMeasurable hf.stronglyMeasurable_mk, EventuallyEq.fun_comp hf.ae_eq_mk g⟩
#align continuous.comp_ae_strongly_measurable Continuous.comp_aestronglyMeasurable

/-- A continuous function from `α` to `β` is ae strongly measurable when one of the two spaces is
second countable. -/
theorem _root_.Continuous.aestronglyMeasurable [TopologicalSpace α] [OpensMeasurableSpace α]
    [PseudoMetrizableSpace β] [SecondCountableTopologyEither α β] (hf : Continuous f) :
    AEStronglyMeasurable f μ :=
  hf.stronglyMeasurable.aestronglyMeasurable
#align continuous.ae_strongly_measurable Continuous.aestronglyMeasurable

protected theorem prod_mk {f : α → β} {g : α → γ} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) : AEStronglyMeasurable (fun x => (f x, g x)) μ :=
  ⟨fun x => (hf.mk f x, hg.mk g x), hf.stronglyMeasurable_mk.prod_mk hg.stronglyMeasurable_mk,
    hf.ae_eq_mk.prod_mk hg.ae_eq_mk⟩
#align measure_theory.ae_strongly_measurable.prod_mk MeasureTheory.AEStronglyMeasurable.prod_mk

/-- In a space with second countable topology, measurable implies ae strongly measurable. -/
@[aesop unsafe 30% apply (rule_sets := [Measurable])]
theorem _root_.Measurable.aestronglyMeasurable {_ : MeasurableSpace α} {μ : Measure α}
    [MeasurableSpace β] [PseudoMetrizableSpace β] [SecondCountableTopology β]
    [OpensMeasurableSpace β] (hf : Measurable f) : AEStronglyMeasurable f μ :=
  hf.stronglyMeasurable.aestronglyMeasurable
#align measurable.ae_strongly_measurable Measurable.aestronglyMeasurable

section Arithmetic

@[to_additive (attr := aesop safe 20 apply (rule_sets := [Measurable]))]
protected theorem mul [Mul β] [ContinuousMul β] (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) : AEStronglyMeasurable (f * g) μ :=
  ⟨hf.mk f * hg.mk g, hf.stronglyMeasurable_mk.mul hg.stronglyMeasurable_mk,
    hf.ae_eq_mk.mul hg.ae_eq_mk⟩
#align measure_theory.ae_strongly_measurable.mul MeasureTheory.AEStronglyMeasurable.mul
#align measure_theory.ae_strongly_measurable.add MeasureTheory.AEStronglyMeasurable.add

@[to_additive (attr := measurability)]
protected theorem mul_const [Mul β] [ContinuousMul β] (hf : AEStronglyMeasurable f μ) (c : β) :
    AEStronglyMeasurable (fun x => f x * c) μ :=
  hf.mul aestronglyMeasurable_const
#align measure_theory.ae_strongly_measurable.mul_const MeasureTheory.AEStronglyMeasurable.mul_const
#align measure_theory.ae_strongly_measurable.add_const MeasureTheory.AEStronglyMeasurable.add_const

@[to_additive (attr := measurability)]
protected theorem const_mul [Mul β] [ContinuousMul β] (hf : AEStronglyMeasurable f μ) (c : β) :
    AEStronglyMeasurable (fun x => c * f x) μ :=
  aestronglyMeasurable_const.mul hf
#align measure_theory.ae_strongly_measurable.const_mul MeasureTheory.AEStronglyMeasurable.const_mul
#align measure_theory.ae_strongly_measurable.const_add MeasureTheory.AEStronglyMeasurable.const_add

@[to_additive (attr := measurability)]
protected theorem inv [Inv β] [ContinuousInv β] (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable f⁻¹ μ :=
  ⟨(hf.mk f)⁻¹, hf.stronglyMeasurable_mk.inv, hf.ae_eq_mk.inv⟩
#align measure_theory.ae_strongly_measurable.inv MeasureTheory.AEStronglyMeasurable.inv
#align measure_theory.ae_strongly_measurable.neg MeasureTheory.AEStronglyMeasurable.neg

@[to_additive (attr := aesop safe 20 apply (rule_sets := [Measurable]))]
protected theorem div [Group β] [TopologicalGroup β] (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) : AEStronglyMeasurable (f / g) μ :=
  ⟨hf.mk f / hg.mk g, hf.stronglyMeasurable_mk.div hg.stronglyMeasurable_mk,
    hf.ae_eq_mk.div hg.ae_eq_mk⟩
#align measure_theory.ae_strongly_measurable.div MeasureTheory.AEStronglyMeasurable.div
#align measure_theory.ae_strongly_measurable.sub MeasureTheory.AEStronglyMeasurable.sub

@[to_additive (attr := aesop safe 20 apply (rule_sets := [Measurable]))]
protected theorem smul {𝕜} [TopologicalSpace 𝕜] [SMul 𝕜 β] [ContinuousSMul 𝕜 β] {f : α → 𝕜}
    {g : α → β} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun x => f x • g x) μ :=
  continuous_smul.comp_aestronglyMeasurable (hf.prod_mk hg)
#align measure_theory.ae_strongly_measurable.smul MeasureTheory.AEStronglyMeasurable.smul
#align measure_theory.ae_strongly_measurable.vadd MeasureTheory.AEStronglyMeasurable.vadd

@[to_additive (attr := aesop safe 20 apply (rule_sets := [Measurable])) const_nsmul]
protected theorem pow [Monoid β] [ContinuousMul β] (hf : AEStronglyMeasurable f μ) (n : ℕ) :
    AEStronglyMeasurable (f ^ n) μ :=
  ⟨hf.mk f ^ n, hf.stronglyMeasurable_mk.pow _, hf.ae_eq_mk.pow_const _⟩

@[to_additive (attr := measurability)]
protected theorem const_smul {𝕜} [SMul 𝕜 β] [ContinuousConstSMul 𝕜 β]
    (hf : AEStronglyMeasurable f μ) (c : 𝕜) : AEStronglyMeasurable (c • f) μ :=
  ⟨c • hf.mk f, hf.stronglyMeasurable_mk.const_smul c, hf.ae_eq_mk.const_smul c⟩
#align measure_theory.ae_strongly_measurable.const_smul MeasureTheory.AEStronglyMeasurable.const_smul

@[to_additive (attr := measurability)]
protected theorem const_smul' {𝕜} [SMul 𝕜 β] [ContinuousConstSMul 𝕜 β]
    (hf : AEStronglyMeasurable f μ) (c : 𝕜) : AEStronglyMeasurable (fun x => c • f x) μ :=
  hf.const_smul c
#align measure_theory.ae_strongly_measurable.const_smul' MeasureTheory.AEStronglyMeasurable.const_smul'

@[to_additive (attr := measurability)]
protected theorem smul_const {𝕜} [TopologicalSpace 𝕜] [SMul 𝕜 β] [ContinuousSMul 𝕜 β] {f : α → 𝕜}
    (hf : AEStronglyMeasurable f μ) (c : β) : AEStronglyMeasurable (fun x => f x • c) μ :=
  continuous_smul.comp_aestronglyMeasurable (hf.prod_mk aestronglyMeasurable_const)
#align measure_theory.ae_strongly_measurable.smul_const MeasureTheory.AEStronglyMeasurable.smul_const
#align measure_theory.ae_strongly_measurable.vadd_const MeasureTheory.AEStronglyMeasurable.vadd_const

end Arithmetic

section Order

@[aesop safe 20 apply (rule_sets := [Measurable])]
protected theorem sup [SemilatticeSup β] [ContinuousSup β] (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) : AEStronglyMeasurable (f ⊔ g) μ :=
  ⟨hf.mk f ⊔ hg.mk g, hf.stronglyMeasurable_mk.sup hg.stronglyMeasurable_mk,
    hf.ae_eq_mk.sup hg.ae_eq_mk⟩
#align measure_theory.ae_strongly_measurable.sup MeasureTheory.AEStronglyMeasurable.sup

@[aesop safe 20 apply (rule_sets := [Measurable])]
protected theorem inf [SemilatticeInf β] [ContinuousInf β] (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) : AEStronglyMeasurable (f ⊓ g) μ :=
  ⟨hf.mk f ⊓ hg.mk g, hf.stronglyMeasurable_mk.inf hg.stronglyMeasurable_mk,
    hf.ae_eq_mk.inf hg.ae_eq_mk⟩
#align measure_theory.ae_strongly_measurable.inf MeasureTheory.AEStronglyMeasurable.inf

end Order

/-!
### Big operators: `∏` and `∑`
-/


section Monoid

variable {M : Type*} [Monoid M] [TopologicalSpace M] [ContinuousMul M]

@[to_additive (attr := measurability)]
theorem _root_.List.aestronglyMeasurable_prod' (l : List (α → M))
    (hl : ∀ f ∈ l, AEStronglyMeasurable f μ) : AEStronglyMeasurable l.prod μ := by
  induction' l with f l ihl; · exact aestronglyMeasurable_one
  rw [List.forall_mem_cons] at hl
  rw [List.prod_cons]
  exact hl.1.mul (ihl hl.2)
#align list.ae_strongly_measurable_prod' List.aestronglyMeasurable_prod'
#align list.ae_strongly_measurable_sum' List.aestronglyMeasurable_sum'

@[to_additive (attr := measurability)]
theorem _root_.List.aestronglyMeasurable_prod
    (l : List (α → M)) (hl : ∀ f ∈ l, AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => (l.map fun f : α → M => f x).prod) μ := by
  simpa only [← Pi.list_prod_apply] using l.aestronglyMeasurable_prod' hl
#align list.ae_strongly_measurable_prod List.aestronglyMeasurable_prod
#align list.ae_strongly_measurable_sum List.aestronglyMeasurable_sum

end Monoid

section CommMonoid

variable {M : Type*} [CommMonoid M] [TopologicalSpace M] [ContinuousMul M]

@[to_additive (attr := measurability)]
theorem _root_.Multiset.aestronglyMeasurable_prod' (l : Multiset (α → M))
    (hl : ∀ f ∈ l, AEStronglyMeasurable f μ) : AEStronglyMeasurable l.prod μ := by
  rcases l with ⟨l⟩
  simpa using l.aestronglyMeasurable_prod' (by simpa using hl)
#align multiset.ae_strongly_measurable_prod' Multiset.aestronglyMeasurable_prod'
#align multiset.ae_strongly_measurable_sum' Multiset.aestronglyMeasurable_sum'

@[to_additive (attr := measurability)]
theorem _root_.Multiset.aestronglyMeasurable_prod (s : Multiset (α → M))
    (hs : ∀ f ∈ s, AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => (s.map fun f : α → M => f x).prod) μ := by
  simpa only [← Pi.multiset_prod_apply] using s.aestronglyMeasurable_prod' hs
#align multiset.ae_strongly_measurable_prod Multiset.aestronglyMeasurable_prod
#align multiset.ae_strongly_measurable_sum Multiset.aestronglyMeasurable_sum

@[to_additive (attr := measurability)]
theorem _root_.Finset.aestronglyMeasurable_prod' {ι : Type*} {f : ι → α → M} (s : Finset ι)
    (hf : ∀ i ∈ s, AEStronglyMeasurable (f i) μ) : AEStronglyMeasurable (∏ i in s, f i) μ :=
  Multiset.aestronglyMeasurable_prod' _ fun _g hg =>
    let ⟨_i, hi, hg⟩ := Multiset.mem_map.1 hg
    hg ▸ hf _ hi
#align finset.ae_strongly_measurable_prod' Finset.aestronglyMeasurable_prod'
#align finset.ae_strongly_measurable_sum' Finset.aestronglyMeasurable_sum'

@[to_additive (attr := measurability)]
theorem _root_.Finset.aestronglyMeasurable_prod {ι : Type*} {f : ι → α → M} (s : Finset ι)
    (hf : ∀ i ∈ s, AEStronglyMeasurable (f i) μ) :
    AEStronglyMeasurable (fun a => ∏ i in s, f i a) μ := by
  simpa only [← Finset.prod_apply] using s.aestronglyMeasurable_prod' hf
#align finset.ae_strongly_measurable_prod Finset.aestronglyMeasurable_prod
#align finset.ae_strongly_measurable_sum Finset.aestronglyMeasurable_sum

end CommMonoid

section SecondCountableAEStronglyMeasurable

variable [MeasurableSpace β]

/-- In a space with second countable topology, measurable implies strongly measurable. -/
@[aesop 90% apply (rule_sets := [Measurable])]
theorem _root_.AEMeasurable.aestronglyMeasurable [PseudoMetrizableSpace β] [OpensMeasurableSpace β]
    [SecondCountableTopology β] (hf : AEMeasurable f μ) : AEStronglyMeasurable f μ :=
  ⟨hf.mk f, hf.measurable_mk.stronglyMeasurable, hf.ae_eq_mk⟩
#align ae_measurable.ae_strongly_measurable AEMeasurable.aestronglyMeasurable

@[measurability]
theorem _root_.aestronglyMeasurable_id {α : Type*} [TopologicalSpace α] [PseudoMetrizableSpace α]
    {_ : MeasurableSpace α} [OpensMeasurableSpace α] [SecondCountableTopology α] {μ : Measure α} :
    AEStronglyMeasurable (id : α → α) μ :=
  aemeasurable_id.aestronglyMeasurable
#align ae_strongly_measurable_id aestronglyMeasurable_id

/-- In a space with second countable topology, strongly measurable and measurable are equivalent. -/
theorem _root_.aestronglyMeasurable_iff_aemeasurable [PseudoMetrizableSpace β] [BorelSpace β]
    [SecondCountableTopology β] : AEStronglyMeasurable f μ ↔ AEMeasurable f μ :=
  ⟨fun h => h.aemeasurable, fun h => h.aestronglyMeasurable⟩
#align ae_strongly_measurable_iff_ae_measurable aestronglyMeasurable_iff_aemeasurable

end SecondCountableAEStronglyMeasurable

@[aesop safe 20 apply (rule_sets := [Measurable])]
protected theorem dist {β : Type*} [PseudoMetricSpace β] {f g : α → β}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun x => dist (f x) (g x)) μ :=
  continuous_dist.comp_aestronglyMeasurable (hf.prod_mk hg)
#align measure_theory.ae_strongly_measurable.dist MeasureTheory.AEStronglyMeasurable.dist

@[measurability]
protected theorem norm {β : Type*} [SeminormedAddCommGroup β] {f : α → β}
    (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurable (fun x => ‖f x‖) μ :=
  continuous_norm.comp_aestronglyMeasurable hf
#align measure_theory.ae_strongly_measurable.norm MeasureTheory.AEStronglyMeasurable.norm

@[measurability]
protected theorem nnnorm {β : Type*} [SeminormedAddCommGroup β] {f : α → β}
    (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurable (fun x => ‖f x‖₊) μ :=
  continuous_nnnorm.comp_aestronglyMeasurable hf
#align measure_theory.ae_strongly_measurable.nnnorm MeasureTheory.AEStronglyMeasurable.nnnorm

@[measurability]
protected theorem ennnorm {β : Type*} [SeminormedAddCommGroup β] {f : α → β}
    (hf : AEStronglyMeasurable f μ) : AEMeasurable (fun a => (‖f a‖₊ : ℝ≥0∞)) μ :=
  (ENNReal.continuous_coe.comp_aestronglyMeasurable hf.nnnorm).aemeasurable
#align measure_theory.ae_strongly_measurable.ennnorm MeasureTheory.AEStronglyMeasurable.ennnorm

@[aesop safe 20 apply (rule_sets := [Measurable])]
protected theorem edist {β : Type*} [SeminormedAddCommGroup β] {f g : α → β}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    AEMeasurable (fun a => edist (f a) (g a)) μ :=
  (continuous_edist.comp_aestronglyMeasurable (hf.prod_mk hg)).aemeasurable
#align measure_theory.ae_strongly_measurable.edist MeasureTheory.AEStronglyMeasurable.edist

@[measurability]
protected theorem real_toNNReal {f : α → ℝ} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => (f x).toNNReal) μ :=
  continuous_real_toNNReal.comp_aestronglyMeasurable hf
#align measure_theory.ae_strongly_measurable.real_to_nnreal MeasureTheory.AEStronglyMeasurable.real_toNNReal

theorem _root_.aestronglyMeasurable_indicator_iff [Zero β] {s : Set α} (hs : MeasurableSet s) :
    AEStronglyMeasurable (indicator s f) μ ↔ AEStronglyMeasurable f (μ.restrict s) := by
  constructor
  · intro h
    exact (h.mono_measure Measure.restrict_le_self).congr (indicator_ae_eq_restrict hs)
  · intro h
    refine' ⟨indicator s (h.mk f), h.stronglyMeasurable_mk.indicator hs, _⟩
    have A : s.indicator f =ᵐ[μ.restrict s] s.indicator (h.mk f) :=
      (indicator_ae_eq_restrict hs).trans (h.ae_eq_mk.trans <| (indicator_ae_eq_restrict hs).symm)
    have B : s.indicator f =ᵐ[μ.restrict sᶜ] s.indicator (h.mk f) :=
      (indicator_ae_eq_restrict_compl hs).trans (indicator_ae_eq_restrict_compl hs).symm
    exact ae_of_ae_restrict_of_ae_restrict_compl _ A B
#align ae_strongly_measurable_indicator_iff aestronglyMeasurable_indicator_iff

@[measurability]
protected theorem indicator [Zero β] (hfm : AEStronglyMeasurable f μ) {s : Set α}
    (hs : MeasurableSet s) : AEStronglyMeasurable (s.indicator f) μ :=
  (aestronglyMeasurable_indicator_iff hs).mpr hfm.restrict
#align measure_theory.ae_strongly_measurable.indicator MeasureTheory.AEStronglyMeasurable.indicator

theorem nullMeasurableSet_eq_fun {E} [TopologicalSpace E] [MetrizableSpace E] {f g : α → E}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    NullMeasurableSet { x | f x = g x } μ := by
  apply
    (hf.stronglyMeasurable_mk.measurableSet_eq_fun
          hg.stronglyMeasurable_mk).nullMeasurableSet.congr
  filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with x hfx hgx
  change (hf.mk f x = hg.mk g x) = (f x = g x)
  simp only [hfx, hgx]
#align measure_theory.ae_strongly_measurable.null_measurable_set_eq_fun MeasureTheory.AEStronglyMeasurable.nullMeasurableSet_eq_fun

@[to_additive]
lemma nullMeasurableSet_mulSupport {E} [TopologicalSpace E] [MetrizableSpace E] [One E] {f : α → E}
    (hf : AEStronglyMeasurable f μ) : NullMeasurableSet (mulSupport f) μ :=
  (hf.nullMeasurableSet_eq_fun stronglyMeasurable_const.aestronglyMeasurable).compl

theorem nullMeasurableSet_lt [LinearOrder β] [OrderClosedTopology β] [PseudoMetrizableSpace β]
    {f g : α → β} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    NullMeasurableSet { a | f a < g a } μ := by
  apply
    (hf.stronglyMeasurable_mk.measurableSet_lt hg.stronglyMeasurable_mk).nullMeasurableSet.congr
  filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with x hfx hgx
  change (hf.mk f x < hg.mk g x) = (f x < g x)
  simp only [hfx, hgx]
#align measure_theory.ae_strongly_measurable.null_measurable_set_lt MeasureTheory.AEStronglyMeasurable.nullMeasurableSet_lt

theorem nullMeasurableSet_le [Preorder β] [OrderClosedTopology β] [PseudoMetrizableSpace β]
    {f g : α → β} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    NullMeasurableSet { a | f a ≤ g a } μ := by
  apply
    (hf.stronglyMeasurable_mk.measurableSet_le hg.stronglyMeasurable_mk).nullMeasurableSet.congr
  filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with x hfx hgx
  change (hf.mk f x ≤ hg.mk g x) = (f x ≤ g x)
  simp only [hfx, hgx]
#align measure_theory.ae_strongly_measurable.null_measurable_set_le MeasureTheory.AEStronglyMeasurable.nullMeasurableSet_le

theorem _root_.aestronglyMeasurable_of_aestronglyMeasurable_trim {α} {m m0 : MeasurableSpace α}
    {μ : Measure α} (hm : m ≤ m0) {f : α → β} (hf : AEStronglyMeasurable f (μ.trim hm)) :
    AEStronglyMeasurable f μ :=
  ⟨hf.mk f, StronglyMeasurable.mono hf.stronglyMeasurable_mk hm, ae_eq_of_ae_eq_trim hf.ae_eq_mk⟩
#align ae_strongly_measurable_of_ae_strongly_measurable_trim aestronglyMeasurable_of_aestronglyMeasurable_trim

theorem comp_aemeasurable {γ : Type*} {_ : MeasurableSpace γ} {_ : MeasurableSpace α} {f : γ → α}
    {μ : Measure γ} (hg : AEStronglyMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) :
    AEStronglyMeasurable (g ∘ f) μ :=
  ⟨hg.mk g ∘ hf.mk f, hg.stronglyMeasurable_mk.comp_measurable hf.measurable_mk,
    (ae_eq_comp hf hg.ae_eq_mk).trans (hf.ae_eq_mk.fun_comp (hg.mk g))⟩
#align measure_theory.ae_strongly_measurable.comp_ae_measurable MeasureTheory.AEStronglyMeasurable.comp_aemeasurable

theorem comp_measurable {γ : Type*} {_ : MeasurableSpace γ} {_ : MeasurableSpace α} {f : γ → α}
    {μ : Measure γ} (hg : AEStronglyMeasurable g (Measure.map f μ)) (hf : Measurable f) :
    AEStronglyMeasurable (g ∘ f) μ :=
  hg.comp_aemeasurable hf.aemeasurable
#align measure_theory.ae_strongly_measurable.comp_measurable MeasureTheory.AEStronglyMeasurable.comp_measurable

theorem comp_quasiMeasurePreserving {γ : Type*} {_ : MeasurableSpace γ} {_ : MeasurableSpace α}
    {f : γ → α} {μ : Measure γ} {ν : Measure α} (hg : AEStronglyMeasurable g ν)
    (hf : QuasiMeasurePreserving f μ ν) : AEStronglyMeasurable (g ∘ f) μ :=
  (hg.mono' hf.absolutelyContinuous).comp_measurable hf.measurable
#align measure_theory.ae_strongly_measurable.comp_quasi_measure_preserving MeasureTheory.AEStronglyMeasurable.comp_quasiMeasurePreserving

theorem comp_measurePreserving {γ : Type*} {_ : MeasurableSpace γ} {_ : MeasurableSpace α}
    {f : γ → α} {μ : Measure γ} {ν : Measure α} (hg : AEStronglyMeasurable g ν)
    (hf : MeasurePreserving f μ ν) : AEStronglyMeasurable (g ∘ f) μ :=
  hg.comp_quasiMeasurePreserving hf.quasiMeasurePreserving

theorem isSeparable_ae_range (hf : AEStronglyMeasurable f μ) :
    ∃ t : Set β, IsSeparable t ∧ ∀ᵐ x ∂μ, f x ∈ t := by
  refine' ⟨range (hf.mk f), hf.stronglyMeasurable_mk.isSeparable_range, _⟩
  filter_upwards [hf.ae_eq_mk] with x hx
  simp [hx]
#align measure_theory.ae_strongly_measurable.is_separable_ae_range MeasureTheory.AEStronglyMeasurable.isSeparable_ae_range

/-- A function is almost everywhere strongly measurable if and only if it is almost everywhere
measurable, and up to a zero measure set its range is contained in a separable set. -/
theorem _root_.aestronglyMeasurable_iff_aemeasurable_separable [PseudoMetrizableSpace β]
    [MeasurableSpace β] [BorelSpace β] :
    AEStronglyMeasurable f μ ↔
      AEMeasurable f μ ∧ ∃ t : Set β, IsSeparable t ∧ ∀ᵐ x ∂μ, f x ∈ t := by
  refine' ⟨fun H => ⟨H.aemeasurable, H.isSeparable_ae_range⟩, _⟩
  rintro ⟨H, ⟨t, t_sep, ht⟩⟩
  rcases eq_empty_or_nonempty t with (rfl | h₀)
  · simp only [mem_empty_iff_false, eventually_false_iff_eq_bot, ae_eq_bot] at ht
    rw [ht]
    exact aestronglyMeasurable_zero_measure f
  · obtain ⟨g, g_meas, gt, fg⟩ : ∃ g : α → β, Measurable g ∧ range g ⊆ t ∧ f =ᵐ[μ] g :=
      H.exists_ae_eq_range_subset ht h₀
    refine' ⟨g, _, fg⟩
    exact stronglyMeasurable_iff_measurable_separable.2 ⟨g_meas, t_sep.mono gt⟩
#align ae_strongly_measurable_iff_ae_measurable_separable aestronglyMeasurable_iff_aemeasurable_separable

theorem _root_.aestronglyMeasurable_iff_nullMeasurable_separable [PseudoMetrizableSpace β]
    [MeasurableSpace β] [BorelSpace β] :
    AEStronglyMeasurable f μ ↔
      NullMeasurable f μ ∧ ∃ t : Set β, IsSeparable t ∧ ∀ᵐ x ∂μ, f x ∈ t :=
  aestronglyMeasurable_iff_aemeasurable_separable.trans <| and_congr_left fun ⟨_, hsep, h⟩ ↦
    have := hsep.secondCountableTopology
    ⟨AEMeasurable.nullMeasurable, fun hf ↦ hf.aemeasurable_of_aerange h⟩

theorem _root_.MeasurableEmbedding.aestronglyMeasurable_map_iff {γ : Type*}
    {mγ : MeasurableSpace γ} {mα : MeasurableSpace α} {f : γ → α} {μ : Measure γ}
    (hf : MeasurableEmbedding f) {g : α → β} :
    AEStronglyMeasurable g (Measure.map f μ) ↔ AEStronglyMeasurable (g ∘ f) μ := by
  refine' ⟨fun H => H.comp_measurable hf.measurable, _⟩
  rintro ⟨g₁, hgm₁, heq⟩
  rcases hf.exists_stronglyMeasurable_extend hgm₁ fun x => ⟨g x⟩ with ⟨g₂, hgm₂, rfl⟩
  exact ⟨g₂, hgm₂, hf.ae_map_iff.2 heq⟩
#align measurable_embedding.ae_strongly_measurable_map_iff MeasurableEmbedding.aestronglyMeasurable_map_iff

theorem _root_.Embedding.aestronglyMeasurable_comp_iff [PseudoMetrizableSpace β]
    [PseudoMetrizableSpace γ] {g : β → γ} {f : α → β} (hg : Embedding g) :
    AEStronglyMeasurable (fun x => g (f x)) μ ↔ AEStronglyMeasurable f μ := by
  letI := pseudoMetrizableSpacePseudoMetric γ
  borelize β γ
  refine'
    ⟨fun H => aestronglyMeasurable_iff_aemeasurable_separable.2 ⟨_, _⟩, fun H =>
      hg.continuous.comp_aestronglyMeasurable H⟩
  · let G : β → range g := rangeFactorization g
    have hG : ClosedEmbedding G :=
      { hg.codRestrict _ _ with
        isClosed_range := by rw [surjective_onto_range.range_eq]; exact isClosed_univ }
    have : AEMeasurable (G ∘ f) μ := AEMeasurable.subtype_mk H.aemeasurable
    exact hG.measurableEmbedding.aemeasurable_comp_iff.1 this
  · rcases (aestronglyMeasurable_iff_aemeasurable_separable.1 H).2 with ⟨t, ht, h't⟩
    exact ⟨g ⁻¹' t, hg.isSeparable_preimage ht, h't⟩
#align embedding.ae_strongly_measurable_comp_iff Embedding.aestronglyMeasurable_comp_iff

theorem _root_.MeasureTheory.MeasurePreserving.aestronglyMeasurable_comp_iff {β : Type*}
    {f : α → β} {mα : MeasurableSpace α} {μa : Measure α} {mβ : MeasurableSpace β} {μb : Measure β}
    (hf : MeasurePreserving f μa μb) (h₂ : MeasurableEmbedding f) {g : β → γ} :
    AEStronglyMeasurable (g ∘ f) μa ↔ AEStronglyMeasurable g μb := by
  rw [← hf.map_eq, h₂.aestronglyMeasurable_map_iff]
#align measure_theory.measure_preserving.ae_strongly_measurable_comp_iff MeasureTheory.MeasurePreserving.aestronglyMeasurable_comp_iff

/-- An almost everywhere sequential limit of almost everywhere strongly measurable functions is
almost everywhere strongly measurable. -/
theorem _root_.aestronglyMeasurable_of_tendsto_ae {ι : Type*} [PseudoMetrizableSpace β]
    (u : Filter ι) [NeBot u] [IsCountablyGenerated u] {f : ι → α → β} {g : α → β}
    (hf : ∀ i, AEStronglyMeasurable (f i) μ) (lim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) u (𝓝 (g x))) :
    AEStronglyMeasurable g μ := by
  borelize β
  refine' aestronglyMeasurable_iff_aemeasurable_separable.2 ⟨_, _⟩
  · exact aemeasurable_of_tendsto_metrizable_ae _ (fun n => (hf n).aemeasurable) lim
  · rcases u.exists_seq_tendsto with ⟨v, hv⟩
    have : ∀ n : ℕ, ∃ t : Set β, IsSeparable t ∧ f (v n) ⁻¹' t ∈ μ.ae := fun n =>
      (aestronglyMeasurable_iff_aemeasurable_separable.1 (hf (v n))).2
    choose t t_sep ht using this
    refine ⟨closure (⋃ i, t i), .closure <| .iUnion t_sep, ?_⟩
    filter_upwards [ae_all_iff.2 ht, lim] with x hx h'x
    apply mem_closure_of_tendsto (h'x.comp hv)
    filter_upwards with n using mem_iUnion_of_mem n (hx n)
#align ae_strongly_measurable_of_tendsto_ae aestronglyMeasurable_of_tendsto_ae

/-- If a sequence of almost everywhere strongly measurable functions converges almost everywhere,
one can select a strongly measurable function as the almost everywhere limit. -/
theorem _root_.exists_stronglyMeasurable_limit_of_tendsto_ae [PseudoMetrizableSpace β]
    {f : ℕ → α → β} (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (h_ae_tendsto : ∀ᵐ x ∂μ, ∃ l : β, Tendsto (fun n => f n x) atTop (𝓝 l)) :
    ∃ f_lim : α → β, StronglyMeasurable f_lim ∧
      ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x)) := by
  borelize β
  obtain ⟨g, _, hg⟩ :
    ∃ g : α → β, Measurable g ∧ ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)) :=
    measurable_limit_of_tendsto_metrizable_ae (fun n => (hf n).aemeasurable) h_ae_tendsto
  have Hg : AEStronglyMeasurable g μ := aestronglyMeasurable_of_tendsto_ae _ hf hg
  refine' ⟨Hg.mk g, Hg.stronglyMeasurable_mk, _⟩
  filter_upwards [hg, Hg.ae_eq_mk] with x hx h'x
  rwa [h'x] at hx
#align exists_strongly_measurable_limit_of_tendsto_ae exists_stronglyMeasurable_limit_of_tendsto_ae

theorem piecewise {s : Set α} [DecidablePred (· ∈ s)]
    (hs : MeasurableSet s) (hf : AEStronglyMeasurable f (μ.restrict s))
    (hg : AEStronglyMeasurable g (μ.restrict sᶜ)) :
    AEStronglyMeasurable (s.piecewise f g) μ := by
  refine ⟨s.piecewise (hf.mk f) (hg.mk g),
    StronglyMeasurable.piecewise hs hf.stronglyMeasurable_mk hg.stronglyMeasurable_mk, ?_⟩
  refine ae_of_ae_restrict_of_ae_restrict_compl s ?_ ?_
  · have h := hf.ae_eq_mk
    rw [Filter.EventuallyEq, ae_restrict_iff' hs] at h
    rw [ae_restrict_iff' hs]
    filter_upwards [h] with x hx
    intro hx_mem
    simp only [hx_mem, Set.piecewise_eq_of_mem, hx hx_mem]
  · have h := hg.ae_eq_mk
    rw [Filter.EventuallyEq, ae_restrict_iff' hs.compl] at h
    rw [ae_restrict_iff' hs.compl]
    filter_upwards [h] with x hx
    intro hx_mem
    rw [Set.mem_compl_iff] at hx_mem
    simp only [hx_mem, not_false_eq_true, Set.piecewise_eq_of_not_mem, hx hx_mem]

theorem sum_measure [PseudoMetrizableSpace β] {m : MeasurableSpace α} {μ : ι → Measure α}
    (h : ∀ i, AEStronglyMeasurable f (μ i)) : AEStronglyMeasurable f (Measure.sum μ) := by
  borelize β
  refine'
    aestronglyMeasurable_iff_aemeasurable_separable.2
      ⟨AEMeasurable.sum_measure fun i => (h i).aemeasurable, _⟩
  have A : ∀ i : ι, ∃ t : Set β, IsSeparable t ∧ f ⁻¹' t ∈ (μ i).ae := fun i =>
    (aestronglyMeasurable_iff_aemeasurable_separable.1 (h i)).2
  choose t t_sep ht using A
  refine ⟨⋃ i, t i, .iUnion t_sep, ?_⟩
  simp only [Measure.ae_sum_eq, mem_iUnion, eventually_iSup]
  intro i
  filter_upwards [ht i] with x hx
  exact ⟨i, hx⟩
#align measure_theory.ae_strongly_measurable.sum_measure MeasureTheory.AEStronglyMeasurable.sum_measure

@[simp]
theorem _root_.aestronglyMeasurable_sum_measure_iff [PseudoMetrizableSpace β]
    {_m : MeasurableSpace α} {μ : ι → Measure α} :
    AEStronglyMeasurable f (sum μ) ↔ ∀ i, AEStronglyMeasurable f (μ i) :=
  ⟨fun h _ => h.mono_measure (Measure.le_sum _ _), sum_measure⟩
#align ae_strongly_measurable_sum_measure_iff aestronglyMeasurable_sum_measure_iff

@[simp]
theorem _root_.aestronglyMeasurable_add_measure_iff [PseudoMetrizableSpace β] {ν : Measure α} :
    AEStronglyMeasurable f (μ + ν) ↔ AEStronglyMeasurable f μ ∧ AEStronglyMeasurable f ν := by
  rw [← sum_cond, aestronglyMeasurable_sum_measure_iff, Bool.forall_bool, and_comm]
  rfl
#align ae_strongly_measurable_add_measure_iff aestronglyMeasurable_add_measure_iff

@[measurability]
theorem add_measure [PseudoMetrizableSpace β] {ν : Measure α} {f : α → β}
    (hμ : AEStronglyMeasurable f μ) (hν : AEStronglyMeasurable f ν) :
    AEStronglyMeasurable f (μ + ν) :=
  aestronglyMeasurable_add_measure_iff.2 ⟨hμ, hν⟩
#align measure_theory.ae_strongly_measurable.add_measure MeasureTheory.AEStronglyMeasurable.add_measure

@[measurability]
protected theorem iUnion [PseudoMetrizableSpace β] {s : ι → Set α}
    (h : ∀ i, AEStronglyMeasurable f (μ.restrict (s i))) :
    AEStronglyMeasurable f (μ.restrict (⋃ i, s i)) :=
  (sum_measure h).mono_measure <| restrict_iUnion_le
#align measure_theory.ae_strongly_measurable.Union MeasureTheory.AEStronglyMeasurable.iUnion

@[simp]
theorem _root_.aestronglyMeasurable_iUnion_iff [PseudoMetrizableSpace β] {s : ι → Set α} :
    AEStronglyMeasurable f (μ.restrict (⋃ i, s i)) ↔
      ∀ i, AEStronglyMeasurable f (μ.restrict (s i)) :=
  ⟨fun h _ => h.mono_measure <| restrict_mono (subset_iUnion _ _) le_rfl,
    AEStronglyMeasurable.iUnion⟩
#align ae_strongly_measurable_Union_iff aestronglyMeasurable_iUnion_iff

@[simp]
theorem _root_.aestronglyMeasurable_union_iff [PseudoMetrizableSpace β] {s t : Set α} :
    AEStronglyMeasurable f (μ.restrict (s ∪ t)) ↔
      AEStronglyMeasurable f (μ.restrict s) ∧ AEStronglyMeasurable f (μ.restrict t) :=
  by simp only [union_eq_iUnion, aestronglyMeasurable_iUnion_iff, Bool.forall_bool, cond, and_comm]
#align ae_strongly_measurable_union_iff aestronglyMeasurable_union_iff

theorem aestronglyMeasurable_uIoc_iff [LinearOrder α] [PseudoMetrizableSpace β] {f : α → β}
    {a b : α} :
    AEStronglyMeasurable f (μ.restrict <| uIoc a b) ↔
      AEStronglyMeasurable f (μ.restrict <| Ioc a b) ∧
        AEStronglyMeasurable f (μ.restrict <| Ioc b a) :=
  by rw [uIoc_eq_union, aestronglyMeasurable_union_iff]
#align measure_theory.ae_strongly_measurable.ae_strongly_measurable_uIoc_iff MeasureTheory.AEStronglyMeasurable.aestronglyMeasurable_uIoc_iff

@[measurability]
theorem smul_measure {R : Type*} [Monoid R] [DistribMulAction R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    (h : AEStronglyMeasurable f μ) (c : R) : AEStronglyMeasurable f (c • μ) :=
  ⟨h.mk f, h.stronglyMeasurable_mk, ae_smul_measure h.ae_eq_mk c⟩
#align measure_theory.ae_strongly_measurable.smul_measure MeasureTheory.AEStronglyMeasurable.smul_measure

section NormedSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem _root_.aestronglyMeasurable_smul_const_iff {f : α → 𝕜} {c : E} (hc : c ≠ 0) :
    AEStronglyMeasurable (fun x => f x • c) μ ↔ AEStronglyMeasurable f μ :=
  (closedEmbedding_smul_left hc).toEmbedding.aestronglyMeasurable_comp_iff
#align ae_strongly_measurable_smul_const_iff aestronglyMeasurable_smul_const_iff

end NormedSpace

section MulAction

variable {M G G₀ : Type*}
variable [Monoid M] [MulAction M β] [ContinuousConstSMul M β]
variable [Group G] [MulAction G β] [ContinuousConstSMul G β]
variable [GroupWithZero G₀] [MulAction G₀ β] [ContinuousConstSMul G₀ β]

theorem _root_.aestronglyMeasurable_const_smul_iff (c : G) :
    AEStronglyMeasurable (fun x => c • f x) μ ↔ AEStronglyMeasurable f μ :=
  ⟨fun h => by simpa only [inv_smul_smul] using h.const_smul' c⁻¹, fun h => h.const_smul c⟩
#align ae_strongly_measurable_const_smul_iff aestronglyMeasurable_const_smul_iff

nonrec theorem _root_.IsUnit.aestronglyMeasurable_const_smul_iff {c : M} (hc : IsUnit c) :
    AEStronglyMeasurable (fun x => c • f x) μ ↔ AEStronglyMeasurable f μ :=
  let ⟨u, hu⟩ := hc
  hu ▸ aestronglyMeasurable_const_smul_iff u
#align is_unit.ae_strongly_measurable_const_smul_iff IsUnit.aestronglyMeasurable_const_smul_iff

theorem _root_.aestronglyMeasurable_const_smul_iff₀ {c : G₀} (hc : c ≠ 0) :
    AEStronglyMeasurable (fun x => c • f x) μ ↔ AEStronglyMeasurable f μ :=
  (IsUnit.mk0 _ hc).aestronglyMeasurable_const_smul_iff
#align ae_strongly_measurable_const_smul_iff₀ aestronglyMeasurable_const_smul_iff₀

end MulAction

section ContinuousLinearMapNontriviallyNormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

theorem _root_.StronglyMeasurable.apply_continuousLinearMap {_m : MeasurableSpace α}
    {φ : α → F →L[𝕜] E}
    (hφ : StronglyMeasurable φ) (v : F) : StronglyMeasurable fun a => φ a v :=
  (ContinuousLinearMap.apply 𝕜 E v).continuous.comp_stronglyMeasurable hφ
#align strongly_measurable.apply_continuous_linear_map StronglyMeasurable.apply_continuousLinearMap

@[measurability]
theorem apply_continuousLinearMap {φ : α → F →L[𝕜] E} (hφ : AEStronglyMeasurable φ μ) (v : F) :
    AEStronglyMeasurable (fun a => φ a v) μ :=
  (ContinuousLinearMap.apply 𝕜 E v).continuous.comp_aestronglyMeasurable hφ
#align measure_theory.ae_strongly_measurable.apply_continuous_linear_map MeasureTheory.AEStronglyMeasurable.apply_continuousLinearMap

theorem _root_.ContinuousLinearMap.aestronglyMeasurable_comp₂ (L : E →L[𝕜] F →L[𝕜] G) {f : α → E}
    {g : α → F} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun x => L (f x) (g x)) μ :=
  L.continuous₂.comp_aestronglyMeasurable <| hf.prod_mk hg
#align continuous_linear_map.ae_strongly_measurable_comp₂ ContinuousLinearMap.aestronglyMeasurable_comp₂

end ContinuousLinearMapNontriviallyNormedField

theorem _root_.aestronglyMeasurable_withDensity_iff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : α → ℝ≥0} (hf : Measurable f) {g : α → E} :
    AEStronglyMeasurable g (μ.withDensity fun x => (f x : ℝ≥0∞)) ↔
      AEStronglyMeasurable (fun x => (f x : ℝ) • g x) μ := by
  constructor
  · rintro ⟨g', g'meas, hg'⟩
    have A : MeasurableSet { x : α | f x ≠ 0 } := (hf (measurableSet_singleton 0)).compl
    refine' ⟨fun x => (f x : ℝ) • g' x, hf.coe_nnreal_real.stronglyMeasurable.smul g'meas, _⟩
    apply @ae_of_ae_restrict_of_ae_restrict_compl _ _ _ { x | f x ≠ 0 }
    · rw [EventuallyEq, ae_withDensity_iff hf.coe_nnreal_ennreal] at hg'
      rw [ae_restrict_iff' A]
      filter_upwards [hg'] with a ha h'a
      have : (f a : ℝ≥0∞) ≠ 0 := by simpa only [Ne.def, ENNReal.coe_eq_zero] using h'a
      rw [ha this]
    · filter_upwards [ae_restrict_mem A.compl] with x hx
      simp only [Classical.not_not, mem_setOf_eq, mem_compl_iff] at hx
      simp [hx]
  · rintro ⟨g', g'meas, hg'⟩
    refine' ⟨fun x => (f x : ℝ)⁻¹ • g' x, hf.coe_nnreal_real.inv.stronglyMeasurable.smul g'meas, _⟩
    rw [EventuallyEq, ae_withDensity_iff hf.coe_nnreal_ennreal]
    filter_upwards [hg'] with x hx h'x
    rw [← hx, smul_smul, _root_.inv_mul_cancel, one_smul]
    simp only [Ne.def, ENNReal.coe_eq_zero] at h'x
    simpa only [NNReal.coe_eq_zero, Ne.def] using h'x
#align ae_strongly_measurable_with_density_iff aestronglyMeasurable_withDensity_iff

end AEStronglyMeasurable

/-! ## Almost everywhere finitely strongly measurable functions -/


namespace AEFinStronglyMeasurable

variable {m : MeasurableSpace α} {μ : Measure α} [TopologicalSpace β] {f g : α → β}

section Mk

variable [Zero β]

/-- A `fin_strongly_measurable` function such that `f =ᵐ[μ] hf.mk f`. See lemmas
`fin_strongly_measurable_mk` and `ae_eq_mk`. -/
protected noncomputable def mk (f : α → β) (hf : AEFinStronglyMeasurable f μ) : α → β :=
  hf.choose
#align measure_theory.ae_fin_strongly_measurable.mk MeasureTheory.AEFinStronglyMeasurable.mk

theorem finStronglyMeasurable_mk (hf : AEFinStronglyMeasurable f μ) :
    FinStronglyMeasurable (hf.mk f) μ :=
  hf.choose_spec.1
#align measure_theory.ae_fin_strongly_measurable.fin_strongly_measurable_mk MeasureTheory.AEFinStronglyMeasurable.finStronglyMeasurable_mk

theorem ae_eq_mk (hf : AEFinStronglyMeasurable f μ) : f =ᵐ[μ] hf.mk f :=
  hf.choose_spec.2
#align measure_theory.ae_fin_strongly_measurable.ae_eq_mk MeasureTheory.AEFinStronglyMeasurable.ae_eq_mk

@[aesop 10% apply (rule_sets := [Measurable])]
protected theorem aemeasurable {β} [Zero β] [MeasurableSpace β] [TopologicalSpace β]
    [PseudoMetrizableSpace β] [BorelSpace β] {f : α → β} (hf : AEFinStronglyMeasurable f μ) :
    AEMeasurable f μ :=
  ⟨hf.mk f, hf.finStronglyMeasurable_mk.measurable, hf.ae_eq_mk⟩
#align measure_theory.ae_fin_strongly_measurable.ae_measurable MeasureTheory.AEFinStronglyMeasurable.aemeasurable

end Mk

section Arithmetic

@[aesop safe 20 (rule_sets := [Measurable])]
protected theorem mul [MonoidWithZero β] [ContinuousMul β] (hf : AEFinStronglyMeasurable f μ)
    (hg : AEFinStronglyMeasurable g μ) : AEFinStronglyMeasurable (f * g) μ :=
  ⟨hf.mk f * hg.mk g, hf.finStronglyMeasurable_mk.mul hg.finStronglyMeasurable_mk,
    hf.ae_eq_mk.mul hg.ae_eq_mk⟩
#align measure_theory.ae_fin_strongly_measurable.mul MeasureTheory.AEFinStronglyMeasurable.mul

@[aesop safe 20 (rule_sets := [Measurable])]
protected theorem add [AddMonoid β] [ContinuousAdd β] (hf : AEFinStronglyMeasurable f μ)
    (hg : AEFinStronglyMeasurable g μ) : AEFinStronglyMeasurable (f + g) μ :=
  ⟨hf.mk f + hg.mk g, hf.finStronglyMeasurable_mk.add hg.finStronglyMeasurable_mk,
    hf.ae_eq_mk.add hg.ae_eq_mk⟩
#align measure_theory.ae_fin_strongly_measurable.add MeasureTheory.AEFinStronglyMeasurable.add

@[measurability]
protected theorem neg [AddGroup β] [TopologicalAddGroup β] (hf : AEFinStronglyMeasurable f μ) :
    AEFinStronglyMeasurable (-f) μ :=
  ⟨-hf.mk f, hf.finStronglyMeasurable_mk.neg, hf.ae_eq_mk.neg⟩
#align measure_theory.ae_fin_strongly_measurable.neg MeasureTheory.AEFinStronglyMeasurable.neg

@[measurability]
protected theorem sub [AddGroup β] [ContinuousSub β] (hf : AEFinStronglyMeasurable f μ)
    (hg : AEFinStronglyMeasurable g μ) : AEFinStronglyMeasurable (f - g) μ :=
  ⟨hf.mk f - hg.mk g, hf.finStronglyMeasurable_mk.sub hg.finStronglyMeasurable_mk,
    hf.ae_eq_mk.sub hg.ae_eq_mk⟩
#align measure_theory.ae_fin_strongly_measurable.sub MeasureTheory.AEFinStronglyMeasurable.sub

@[measurability]
protected theorem const_smul {𝕜} [TopologicalSpace 𝕜] [AddMonoid β] [Monoid 𝕜]
    [DistribMulAction 𝕜 β] [ContinuousSMul 𝕜 β] (hf : AEFinStronglyMeasurable f μ) (c : 𝕜) :
    AEFinStronglyMeasurable (c • f) μ :=
  ⟨c • hf.mk f, hf.finStronglyMeasurable_mk.const_smul c, hf.ae_eq_mk.const_smul c⟩
#align measure_theory.ae_fin_strongly_measurable.const_smul MeasureTheory.AEFinStronglyMeasurable.const_smul

end Arithmetic

section Order

variable [Zero β]

@[aesop safe 20 (rule_sets := [Measurable])]
protected theorem sup [SemilatticeSup β] [ContinuousSup β] (hf : AEFinStronglyMeasurable f μ)
    (hg : AEFinStronglyMeasurable g μ) : AEFinStronglyMeasurable (f ⊔ g) μ :=
  ⟨hf.mk f ⊔ hg.mk g, hf.finStronglyMeasurable_mk.sup hg.finStronglyMeasurable_mk,
    hf.ae_eq_mk.sup hg.ae_eq_mk⟩
#align measure_theory.ae_fin_strongly_measurable.sup MeasureTheory.AEFinStronglyMeasurable.sup

@[aesop safe 20 (rule_sets := [Measurable])]
protected theorem inf [SemilatticeInf β] [ContinuousInf β] (hf : AEFinStronglyMeasurable f μ)
    (hg : AEFinStronglyMeasurable g μ) : AEFinStronglyMeasurable (f ⊓ g) μ :=
  ⟨hf.mk f ⊓ hg.mk g, hf.finStronglyMeasurable_mk.inf hg.finStronglyMeasurable_mk,
    hf.ae_eq_mk.inf hg.ae_eq_mk⟩
#align measure_theory.ae_fin_strongly_measurable.inf MeasureTheory.AEFinStronglyMeasurable.inf

end Order

variable [Zero β] [T2Space β]

theorem exists_set_sigmaFinite (hf : AEFinStronglyMeasurable f μ) :
    ∃ t, MeasurableSet t ∧ f =ᵐ[μ.restrict tᶜ] 0 ∧ SigmaFinite (μ.restrict t) := by
  rcases hf with ⟨g, hg, hfg⟩
  obtain ⟨t, ht, hgt_zero, htμ⟩ := hg.exists_set_sigmaFinite
  refine' ⟨t, ht, _, htμ⟩
  refine' EventuallyEq.trans (ae_restrict_of_ae hfg) _
  rw [EventuallyEq, ae_restrict_iff' ht.compl]
  exact eventually_of_forall hgt_zero
#align measure_theory.ae_fin_strongly_measurable.exists_set_sigma_finite MeasureTheory.AEFinStronglyMeasurable.exists_set_sigmaFinite

/-- A measurable set `t` such that `f =ᵐ[μ.restrict tᶜ] 0` and `sigma_finite (μ.restrict t)`. -/
def sigmaFiniteSet (hf : AEFinStronglyMeasurable f μ) : Set α :=
  hf.exists_set_sigmaFinite.choose
#align measure_theory.ae_fin_strongly_measurable.sigma_finite_set MeasureTheory.AEFinStronglyMeasurable.sigmaFiniteSet

protected theorem measurableSet (hf : AEFinStronglyMeasurable f μ) :
    MeasurableSet hf.sigmaFiniteSet :=
  hf.exists_set_sigmaFinite.choose_spec.1
#align measure_theory.ae_fin_strongly_measurable.measurable_set MeasureTheory.AEFinStronglyMeasurable.measurableSet

theorem ae_eq_zero_compl (hf : AEFinStronglyMeasurable f μ) :
    f =ᵐ[μ.restrict hf.sigmaFiniteSetᶜ] 0 :=
  hf.exists_set_sigmaFinite.choose_spec.2.1
#align measure_theory.ae_fin_strongly_measurable.ae_eq_zero_compl MeasureTheory.AEFinStronglyMeasurable.ae_eq_zero_compl

instance sigmaFinite_restrict (hf : AEFinStronglyMeasurable f μ) :
    SigmaFinite (μ.restrict hf.sigmaFiniteSet) :=
  hf.exists_set_sigmaFinite.choose_spec.2.2
#align measure_theory.ae_fin_strongly_measurable.sigma_finite_restrict MeasureTheory.AEFinStronglyMeasurable.sigmaFinite_restrict

end AEFinStronglyMeasurable

section SecondCountableTopology

variable {G : Type*} {p : ℝ≥0∞} {m m0 : MeasurableSpace α} {μ : Measure α}
  [SeminormedAddCommGroup G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  {f : α → G}

/-- In a space with second countable topology and a sigma-finite measure, `FinStronglyMeasurable`
  and `Measurable` are equivalent. -/
theorem finStronglyMeasurable_iff_measurable {_m0 : MeasurableSpace α} (μ : Measure α)
    [SigmaFinite μ] : FinStronglyMeasurable f μ ↔ Measurable f :=
  ⟨fun h => h.measurable, fun h => (Measurable.stronglyMeasurable h).finStronglyMeasurable μ⟩
#align measure_theory.fin_strongly_measurable_iff_measurable MeasureTheory.finStronglyMeasurable_iff_measurable

/-- In a space with second countable topology and a sigma-finite measure, a measurable function
is `FinStronglyMeasurable`. -/
@[aesop 90% apply (rule_sets := [Measurable])]
theorem finStronglyMeasurable_of_measurable {_m0 : MeasurableSpace α} (μ : Measure α)
    [SigmaFinite μ] (hf : Measurable f) : FinStronglyMeasurable f μ :=
  (finStronglyMeasurable_iff_measurable μ).mpr hf

/-- In a space with second countable topology and a sigma-finite measure,
  `AEFinStronglyMeasurable` and `AEMeasurable` are equivalent. -/
theorem aefinStronglyMeasurable_iff_aemeasurable {_m0 : MeasurableSpace α} (μ : Measure α)
    [SigmaFinite μ] : AEFinStronglyMeasurable f μ ↔ AEMeasurable f μ := by
  simp_rw [AEFinStronglyMeasurable, AEMeasurable, finStronglyMeasurable_iff_measurable]
#align measure_theory.ae_fin_strongly_measurable_iff_ae_measurable MeasureTheory.aefinStronglyMeasurable_iff_aemeasurable

/-- In a space with second countable topology and a sigma-finite measure,
  an `AEMeasurable` function is `AEFinStronglyMeasurable`. -/
@[aesop 90% apply (rule_sets := [Measurable])]
theorem aefinStronglyMeasurable_of_aemeasurable {_m0 : MeasurableSpace α} (μ : Measure α)
    [SigmaFinite μ] (hf : AEMeasurable f μ) : AEFinStronglyMeasurable f μ :=
  (aefinStronglyMeasurable_iff_aemeasurable μ).mpr hf

end SecondCountableTopology

theorem measurable_uncurry_of_continuous_of_measurable {α β ι : Type*} [TopologicalSpace ι]
    [MetrizableSpace ι] [MeasurableSpace ι] [SecondCountableTopology ι] [OpensMeasurableSpace ι]
    {mβ : MeasurableSpace β} [TopologicalSpace β] [PseudoMetrizableSpace β] [BorelSpace β]
    {m : MeasurableSpace α} {u : ι → α → β} (hu_cont : ∀ x, Continuous fun i => u i x)
    (h : ∀ i, Measurable (u i)) : Measurable (Function.uncurry u) := by
  obtain ⟨t_sf, ht_sf⟩ :
    ∃ t : ℕ → SimpleFunc ι ι, ∀ j x, Tendsto (fun n => u (t n j) x) atTop (𝓝 <| u j x) := by
    have h_str_meas : StronglyMeasurable (id : ι → ι) := stronglyMeasurable_id
    refine' ⟨h_str_meas.approx, fun j x => _⟩
    exact ((hu_cont x).tendsto j).comp (h_str_meas.tendsto_approx j)
  let U (n : ℕ) (p : ι × α) := u (t_sf n p.fst) p.snd
  have h_tendsto : Tendsto U atTop (𝓝 fun p => u p.fst p.snd) := by
    rw [tendsto_pi_nhds]
    exact fun p => ht_sf p.fst p.snd
  refine' measurable_of_tendsto_metrizable (fun n => _) h_tendsto
  have h_meas : Measurable fun p : (t_sf n).range × α => u (↑p.fst) p.snd := by
    have :
      (fun p : ↥(t_sf n).range × α => u (↑p.fst) p.snd) =
        (fun p : α × (t_sf n).range => u (↑p.snd) p.fst) ∘ Prod.swap :=
      rfl
    rw [this, @measurable_swap_iff α (↥(t_sf n).range) β m]
    exact measurable_from_prod_countable fun j => h j
  have :
    (fun p : ι × α => u (t_sf n p.fst) p.snd) =
      (fun p : ↥(t_sf n).range × α => u p.fst p.snd) ∘ fun p : ι × α =>
        (⟨t_sf n p.fst, SimpleFunc.mem_range_self _ _⟩, p.snd) :=
    rfl
  simp_rw [U, this]
  refine' h_meas.comp (Measurable.prod_mk _ measurable_snd)
  exact ((t_sf n).measurable.comp measurable_fst).subtype_mk
#align measure_theory.measurable_uncurry_of_continuous_of_measurable MeasureTheory.measurable_uncurry_of_continuous_of_measurable

theorem stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable {α β ι : Type*}
    [TopologicalSpace ι] [MetrizableSpace ι] [MeasurableSpace ι] [SecondCountableTopology ι]
    [OpensMeasurableSpace ι] [TopologicalSpace β] [PseudoMetrizableSpace β] [MeasurableSpace α]
    {u : ι → α → β} (hu_cont : ∀ x, Continuous fun i => u i x) (h : ∀ i, StronglyMeasurable (u i)) :
    StronglyMeasurable (Function.uncurry u) := by
  borelize β
  obtain ⟨t_sf, ht_sf⟩ :
    ∃ t : ℕ → SimpleFunc ι ι, ∀ j x, Tendsto (fun n => u (t n j) x) atTop (𝓝 <| u j x) := by
    have h_str_meas : StronglyMeasurable (id : ι → ι) := stronglyMeasurable_id
    refine' ⟨h_str_meas.approx, fun j x => _⟩
    exact ((hu_cont x).tendsto j).comp (h_str_meas.tendsto_approx j)
  let U (n : ℕ) (p : ι × α) := u (t_sf n p.fst) p.snd
  have h_tendsto : Tendsto U atTop (𝓝 fun p => u p.fst p.snd) := by
    rw [tendsto_pi_nhds]
    exact fun p => ht_sf p.fst p.snd
  refine' stronglyMeasurable_of_tendsto _ (fun n => _) h_tendsto
  have h_str_meas : StronglyMeasurable fun p : (t_sf n).range × α => u (↑p.fst) p.snd := by
    refine' stronglyMeasurable_iff_measurable_separable.2 ⟨_, _⟩
    · have :
        (fun p : ↥(t_sf n).range × α => u (↑p.fst) p.snd) =
          (fun p : α × (t_sf n).range => u (↑p.snd) p.fst) ∘ Prod.swap :=
        rfl
      rw [this, measurable_swap_iff]
      exact measurable_from_prod_countable fun j => (h j).measurable
    · have : IsSeparable (⋃ i : (t_sf n).range, range (u i)) :=
        .iUnion fun i => (h i).isSeparable_range
      apply this.mono
      rintro _ ⟨⟨i, x⟩, rfl⟩
      simp only [mem_iUnion, mem_range]
      exact ⟨i, x, rfl⟩
  have :
    (fun p : ι × α => u (t_sf n p.fst) p.snd) =
      (fun p : ↥(t_sf n).range × α => u p.fst p.snd) ∘ fun p : ι × α =>
        (⟨t_sf n p.fst, SimpleFunc.mem_range_self _ _⟩, p.snd) :=
    rfl
  simp_rw [U, this]
  refine' h_str_meas.comp_measurable (Measurable.prod_mk _ measurable_snd)
  exact ((t_sf n).measurable.comp measurable_fst).subtype_mk
#align measure_theory.strongly_measurable_uncurry_of_continuous_of_strongly_measurable MeasureTheory.stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable


section Coercions -- between different types of measurability

variable {α β ι : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
variable {f : α → β}


attribute [coe] StronglyMeasurable.measurable
instance _root_.MeasureTheory.StronglyMeasurable.instCoeStronglyMeasurable_toMeasurable
    [TopologicalSpace β]
    [TopologicalSpace.PseudoMetrizableSpace β]
    [BorelSpace β] :
    Coe (StronglyMeasurable f) (Measurable f) where
  coe h := h.measurable

attribute [coe] Measurable.stronglyMeasurable
instance _root_.Measurable.instCoeMeasurable_toStronglyMeasurable
    [TopologicalSpace β]
    [OpensMeasurableSpace β]
    [TopologicalSpace.PseudoMetrizableSpace β]
    [SecondCountableTopology β] :
    CoeOut (Measurable f) (StronglyMeasurable f) where
  coe h := h.stronglyMeasurable

variable {μ : Measure α}

attribute [coe] StronglyMeasurable.finStronglyMeasurable
instance _root_.MeasureTheory.StronglyMeasurable.instCoeStronglyMeasurable_toFinStronglyMeasurable
    [SigmaFinite μ]
    [TopologicalSpace β]
    [Zero β] :
    Coe (StronglyMeasurable f) (FinStronglyMeasurable f μ) where
  coe h := h.finStronglyMeasurable μ

attribute [coe] StronglyMeasurable.aestronglyMeasurable
instance _root_.MeasureTheory.StronglyMeasurable.instCoeStronglyMeasurable_toAEStronglyMeasurable
    [TopologicalSpace β] :
    Coe (StronglyMeasurable f) (AEStronglyMeasurable f μ) where
  coe h := h.aestronglyMeasurable

attribute [coe] AEStronglyMeasurable.aemeasurable
instance _root_.MeasureTheory.AEStronglyMeasurable.instCoeAEStronglyMeasurable_toAEMeasurable
    [TopologicalSpace β]
    [BorelSpace β]
    [TopologicalSpace.PseudoMetrizableSpace β] :
    Coe (AEStronglyMeasurable f μ) (AEMeasurable f μ) where
  coe h := h.aemeasurable

attribute [coe] aefinStronglyMeasurable_of_aemeasurable
instance _root_.AEMeasurable.instCoeAEMeasurable_toAEFinStronglyMeasurable
    [SigmaFinite μ]
    [SeminormedAddCommGroup β]
    [SecondCountableTopology β]
    [BorelSpace β] :
    CoeOut (AEMeasurable f μ) (AEFinStronglyMeasurable f μ) where
  coe h := aefinStronglyMeasurable_of_aemeasurable μ h

attribute [coe] Measurable.aemeasurable
instance _root_.Measurable.instCoeMeasurable_toAEMeasurable :
    Coe (Measurable f) (AEMeasurable f μ) where
  coe h := h.aemeasurable

attribute [coe] AEMeasurable.aestronglyMeasurable
instance _root_.Measurable.instCoeAEMeasurable_toAEStronglyMeasurable
    [TopologicalSpace β]
    [TopologicalSpace.PseudoMetrizableSpace β]
    [SecondCountableTopology β]
    [OpensMeasurableSpace β] :
    CoeOut (AEMeasurable f μ) (AEStronglyMeasurable f μ) where
  coe h := h.aestronglyMeasurable


end Coercions

end MeasureTheory

-- Guard against import creep
assert_not_exists InnerProductSpace
