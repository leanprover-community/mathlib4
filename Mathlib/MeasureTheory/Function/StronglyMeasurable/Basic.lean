/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.MeasureTheory.Function.SimpleFuncDense

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

open ENNReal Topology MeasureTheory NNReal

variable {α β γ ι : Type*} [Countable ι]

namespace MeasureTheory

@[inherit_doc] local infixr:25 " →ₛ " => SimpleFunc

section Definitions

variable [TopologicalSpace β]

/-- A function is `StronglyMeasurable` if it is the limit of simple functions. -/
def StronglyMeasurable [MeasurableSpace α] (f : α → β) : Prop :=
  ∃ fs : ℕ → α →ₛ β, ∀ x, Tendsto (fun n => fs n x) atTop (𝓝 (f x))

/-- The notation for StronglyMeasurable giving the measurable space instance explicitly. -/
scoped notation "StronglyMeasurable[" m "]" => @MeasureTheory.StronglyMeasurable _ _ _ m

/-- A function is `FinStronglyMeasurable` with respect to a measure if it is the limit of simple
  functions with support with finite measure. -/
def FinStronglyMeasurable [Zero β]
    {_ : MeasurableSpace α} (f : α → β) (μ : Measure α := by volume_tac) : Prop :=
  ∃ fs : ℕ → α →ₛ β, (∀ n, μ (support (fs n)) < ∞) ∧ ∀ x, Tendsto (fun n => fs n x) atTop (𝓝 (f x))

/-- A function is `AEStronglyMeasurable` with respect to a measure `μ` if it is almost everywhere
equal to the limit of a sequence of simple functions. -/
@[fun_prop]
def AEStronglyMeasurable
    {_ : MeasurableSpace α} (f : α → β) (μ : Measure α := by volume_tac) : Prop :=
  ∃ g, StronglyMeasurable g ∧ f =ᵐ[μ] g

/-- A function is `AEFinStronglyMeasurable` with respect to a measure if it is almost everywhere
equal to the limit of a sequence of simple functions with support with finite measure. -/
def AEFinStronglyMeasurable
    [Zero β] {_ : MeasurableSpace α} (f : α → β) (μ : Measure α := by volume_tac) : Prop :=
  ∃ g, FinStronglyMeasurable g μ ∧ f =ᵐ[μ] g

end Definitions

open MeasureTheory

/-! ## Strongly measurable functions -/

@[aesop 30% apply (rule_sets := [Measurable])]
protected theorem StronglyMeasurable.aestronglyMeasurable {α β} {_ : MeasurableSpace α}
    [TopologicalSpace β] {f : α → β} {μ : Measure α} (hf : StronglyMeasurable f) :
    AEStronglyMeasurable f μ :=
  ⟨f, hf, EventuallyEq.refl _ _⟩

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

theorem SimpleFunc.stronglyMeasurable {α β} {_ : MeasurableSpace α} [TopologicalSpace β]
    (f : α →ₛ β) : StronglyMeasurable f :=
  ⟨fun _ => f, fun _ => tendsto_const_nhds⟩

@[nontriviality]
theorem StronglyMeasurable.of_finite [Finite α] {_ : MeasurableSpace α}
    [MeasurableSingletonClass α] [TopologicalSpace β]
    (f : α → β) : StronglyMeasurable f :=
  ⟨fun _ => SimpleFunc.ofFinite f, fun _ => tendsto_const_nhds⟩

@[deprecated (since := "2024-02-05")]
alias stronglyMeasurable_of_fintype := StronglyMeasurable.of_finite

@[deprecated StronglyMeasurable.of_finite (since := "2024-02-06")]
theorem stronglyMeasurable_of_isEmpty [IsEmpty α] {_ : MeasurableSpace α} [TopologicalSpace β]
    (f : α → β) : StronglyMeasurable f :=
  .of_finite f

theorem stronglyMeasurable_const {α β} {_ : MeasurableSpace α} [TopologicalSpace β] {b : β} :
    StronglyMeasurable fun _ : α => b :=
  ⟨fun _ => SimpleFunc.const α b, fun _ => tendsto_const_nhds⟩

@[to_additive]
theorem stronglyMeasurable_one {α β} {_ : MeasurableSpace α} [TopologicalSpace β] [One β] :
    StronglyMeasurable (1 : α → β) :=
  stronglyMeasurable_const

/-- A version of `stronglyMeasurable_const` that assumes `f x = f y` for all `x, y`.
This version works for functions between empty types. -/
theorem stronglyMeasurable_const' {α β} {m : MeasurableSpace α} [TopologicalSpace β] {f : α → β}
    (hf : ∀ x y, f x = f y) : StronglyMeasurable f := by
  nontriviality α
  inhabit α
  convert stronglyMeasurable_const (β := β) using 1
  exact funext fun x => hf x default

-- Porting note: changed binding type of `MeasurableSpace α`.
@[simp]
theorem Subsingleton.stronglyMeasurable' {α β} [MeasurableSpace α] [TopologicalSpace β]
    [Subsingleton α] (f : α → β) : StronglyMeasurable f :=
  stronglyMeasurable_const' fun x y => by rw [Subsingleton.elim x y]

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

protected theorem tendsto_approx {_ : MeasurableSpace α} (hf : StronglyMeasurable f) :
    ∀ x, Tendsto (fun n => hf.approx n x) atTop (𝓝 (f x)) :=
  hf.choose_spec

/-- Similar to `stronglyMeasurable.approx`, but enforces that the norm of every function in the
sequence is less than `c` everywhere. If `‖f x‖ ≤ c` this sequence of simple functions verifies
`Tendsto (fun n => hf.approxBounded n x) atTop (𝓝 (f x))`. -/
noncomputable def approxBounded {_ : MeasurableSpace α} [Norm β] [SMul ℝ β]
    (hf : StronglyMeasurable f) (c : ℝ) : ℕ → SimpleFunc α β := fun n =>
  (hf.approx n).map fun x => min 1 (c / ‖x‖) • x

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
    refine squeeze_zero_norm (fun n => ?_) h_tendsto_norm
    calc
      ‖min 1 (c / ‖hf.approx n x‖) • hf.approx n x‖ =
          ‖min 1 (c / ‖hf.approx n x‖)‖ * ‖hf.approx n x‖ :=
        norm_smul _ _
      _ ≤ ‖(1 : ℝ)‖ * ‖hf.approx n x‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        rw [norm_one, Real.norm_of_nonneg]
        · exact min_le_left _ _
        · exact le_min zero_le_one (div_nonneg ((norm_nonneg _).trans hfx) (norm_nonneg _))
      _ = ‖hf.approx n x‖ := by rw [norm_one, one_mul]
  rw [← one_smul ℝ (f x)]
  refine Tendsto.smul ?_ h_tendsto
  have : min 1 (c / ‖f x‖) = 1 := by
    rw [min_eq_left_iff, one_le_div (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hfx0))]
    exact hfx
  nth_rw 2 [this.symm]
  refine Tendsto.min tendsto_const_nhds ?_
  exact Tendsto.div tendsto_const_nhds h_tendsto.norm hfx0

theorem tendsto_approxBounded_ae {β} {f : α → β} [NormedAddCommGroup β] [NormedSpace ℝ β]
    {m m0 : MeasurableSpace α} {μ : Measure α} (hf : StronglyMeasurable[m] f) {c : ℝ}
    (hf_bound : ∀ᵐ x ∂μ, ‖f x‖ ≤ c) :
    ∀ᵐ x ∂μ, Tendsto (fun n => hf.approxBounded c n x) atTop (𝓝 (f x)) := by
  filter_upwards [hf_bound] with x hfx using tendsto_approxBounded_of_norm_le hf hfx

theorem norm_approxBounded_le {β} {f : α → β} [SeminormedAddCommGroup β] [NormedSpace ℝ β]
    {m : MeasurableSpace α} {c : ℝ} (hf : StronglyMeasurable[m] f) (hc : 0 ≤ c) (n : ℕ) (x : α) :
    ‖hf.approxBounded c n x‖ ≤ c := by
  simp only [StronglyMeasurable.approxBounded, SimpleFunc.coe_map, Function.comp_apply]
  refine (norm_smul_le _ _).trans ?_
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

theorem _root_.stronglyMeasurable_bot_iff [Nonempty β] [T2Space β] :
    StronglyMeasurable[⊥] f ↔ ∃ c, f = fun _ => c := by
  cases' isEmpty_or_nonempty α with hα hα
  · simp only [@Subsingleton.stronglyMeasurable' _ _ ⊥ _ _ f,
      eq_iff_true_of_subsingleton, exists_const]
  refine ⟨fun hf => ?_, fun hf_eq => ?_⟩
  · refine ⟨f hα.some, ?_⟩
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
    refine Set.indicator_of_not_mem ?_ _
    simp [hxt]
  refine ⟨fs, ?_, fun x => ?_⟩
  · simp_rw [SimpleFunc.support_eq]
    refine fun n => (measure_biUnion_finset_le _ _).trans_lt ?_
    refine ENNReal.sum_lt_top_iff.mpr fun y hy => ?_
    rw [SimpleFunc.restrict_preimage_singleton _ ((hS_meas n).inter ht)]
    swap
    · letI : (y : β) → Decidable (y = 0) := fun y => Classical.propDecidable _
      rw [Finset.mem_filter] at hy
      exact hy.2
    refine (measure_mono Set.inter_subset_left).trans_lt ?_
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
      refine ⟨n, fun m hnm => ?_⟩
      simp_rw [fs, SimpleFunc.restrict_apply _ ((hS_meas m).inter ht),
        Set.indicator_of_mem (hn m hnm)]
    rw [tendsto_atTop'] at h ⊢
    intro s hs
    obtain ⟨n₂, hn₂⟩ := h s hs
    refine ⟨max n₁ n₂, fun m hm => ?_⟩
    rw [hn₁ m ((le_max_left _ _).trans hm.le)]
    exact hn₂ m ((le_max_right _ _).trans hm.le)

/-- If the measure is sigma-finite, all strongly measurable functions are
  `FinStronglyMeasurable`. -/
@[aesop 5% apply (rule_sets := [Measurable])]
protected theorem finStronglyMeasurable [TopologicalSpace β] [Zero β] {m0 : MeasurableSpace α}
    (hf : StronglyMeasurable f) (μ : Measure α) [SigmaFinite μ] : FinStronglyMeasurable f μ :=
  hf.finStronglyMeasurable_of_set_sigmaFinite MeasurableSet.univ (by simp)
    (by rwa [Measure.restrict_univ])

/-- A strongly measurable function is measurable. -/
@[aesop 5% apply (rule_sets := [Measurable])]
protected theorem measurable {_ : MeasurableSpace α} [TopologicalSpace β] [PseudoMetrizableSpace β]
    [MeasurableSpace β] [BorelSpace β] (hf : StronglyMeasurable f) : Measurable f :=
  measurable_of_tendsto_metrizable (fun n => (hf.approx n).measurable)
    (tendsto_pi_nhds.mpr hf.tendsto_approx)

/-- A strongly measurable function is almost everywhere measurable. -/
@[aesop 5% apply (rule_sets := [Measurable])]
protected theorem aemeasurable {_ : MeasurableSpace α} [TopologicalSpace β]
    [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β] {μ : Measure α}
    (hf : StronglyMeasurable f) : AEMeasurable f μ :=
  hf.measurable.aemeasurable

theorem _root_.Continuous.comp_stronglyMeasurable {_ : MeasurableSpace α} [TopologicalSpace β]
    [TopologicalSpace γ] {g : β → γ} {f : α → β} (hg : Continuous g) (hf : StronglyMeasurable f) :
    StronglyMeasurable fun x => g (f x) :=
  ⟨fun n => SimpleFunc.map g (hf.approx n), fun x => (hg.tendsto _).comp (hf.tendsto_approx x)⟩

@[to_additive]
nonrec theorem measurableSet_mulSupport {m : MeasurableSpace α} [One β] [TopologicalSpace β]
    [MetrizableSpace β] (hf : StronglyMeasurable f) : MeasurableSet (mulSupport f) := by
  borelize β
  exact measurableSet_mulSupport hf.measurable

protected theorem mono {m m' : MeasurableSpace α} [TopologicalSpace β]
    (hf : StronglyMeasurable[m'] f) (h_mono : m' ≤ m) : StronglyMeasurable[m] f := by
  let f_approx : ℕ → @SimpleFunc α m β := fun n =>
    @SimpleFunc.mk α m β
      (hf.approx n)
      (fun x => h_mono _ (SimpleFunc.measurableSet_fiber' _ x))
      (SimpleFunc.finite_range (hf.approx n))
  exact ⟨f_approx, hf.tendsto_approx⟩

protected theorem prod_mk {m : MeasurableSpace α} [TopologicalSpace β] [TopologicalSpace γ]
    {f : α → β} {g : α → γ} (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    StronglyMeasurable fun x => (f x, g x) := by
  refine ⟨fun n => SimpleFunc.pair (hf.approx n) (hg.approx n), fun x => ?_⟩
  rw [nhds_prod_eq]
  exact Tendsto.prod_mk (hf.tendsto_approx x) (hg.tendsto_approx x)

theorem comp_measurable [TopologicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ}
    {f : α → β} {g : γ → α} (hf : StronglyMeasurable f) (hg : Measurable g) :
    StronglyMeasurable (f ∘ g) :=
  ⟨fun n => SimpleFunc.comp (hf.approx n) g hg, fun x => hf.tendsto_approx (g x)⟩

theorem of_uncurry_left [TopologicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ}
    {f : α → γ → β} (hf : StronglyMeasurable (uncurry f)) {x : α} : StronglyMeasurable (f x) :=
  hf.comp_measurable measurable_prod_mk_left

theorem of_uncurry_right [TopologicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ}
    {f : α → γ → β} (hf : StronglyMeasurable (uncurry f)) {y : γ} :
    StronglyMeasurable fun x => f x y :=
  hf.comp_measurable measurable_prod_mk_right

section Arithmetic

variable {mα : MeasurableSpace α} [TopologicalSpace β]

@[to_additive (attr := aesop safe 20 apply (rule_sets := [Measurable]))]
protected theorem mul [Mul β] [ContinuousMul β] (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) : StronglyMeasurable (f * g) :=
  ⟨fun n => hf.approx n * hg.approx n, fun x => (hf.tendsto_approx x).mul (hg.tendsto_approx x)⟩

@[to_additive (attr := measurability)]
theorem mul_const [Mul β] [ContinuousMul β] (hf : StronglyMeasurable f) (c : β) :
    StronglyMeasurable fun x => f x * c :=
  hf.mul stronglyMeasurable_const

@[to_additive (attr := measurability)]
theorem const_mul [Mul β] [ContinuousMul β] (hf : StronglyMeasurable f) (c : β) :
    StronglyMeasurable fun x => c * f x :=
  stronglyMeasurable_const.mul hf

@[to_additive (attr := aesop safe 20 apply (rule_sets := [Measurable])) const_nsmul]
protected theorem pow [Monoid β] [ContinuousMul β] (hf : StronglyMeasurable f) (n : ℕ) :
    StronglyMeasurable (f ^ n) :=
  ⟨fun k => hf.approx k ^ n, fun x => (hf.tendsto_approx x).pow n⟩

@[to_additive (attr := measurability)]
protected theorem inv [Inv β] [ContinuousInv β] (hf : StronglyMeasurable f) :
    StronglyMeasurable f⁻¹ :=
  ⟨fun n => (hf.approx n)⁻¹, fun x => (hf.tendsto_approx x).inv⟩

@[to_additive (attr := aesop safe 20 apply (rule_sets := [Measurable]))]
protected theorem div [Div β] [ContinuousDiv β] (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) : StronglyMeasurable (f / g) :=
  ⟨fun n => hf.approx n / hg.approx n, fun x => (hf.tendsto_approx x).div' (hg.tendsto_approx x)⟩

@[to_additive]
theorem mul_iff_right [CommGroup β] [TopologicalGroup β] (hf : StronglyMeasurable f) :
    StronglyMeasurable (f * g) ↔ StronglyMeasurable g :=
  ⟨fun h ↦ show g = f * g * f⁻¹ by simp only [mul_inv_cancel_comm] ▸ h.mul hf.inv,
    fun h ↦ hf.mul h⟩

@[to_additive]
theorem mul_iff_left [CommGroup β] [TopologicalGroup β] (hf : StronglyMeasurable f) :
    StronglyMeasurable (g * f) ↔ StronglyMeasurable g :=
  mul_comm g f ▸ mul_iff_right hf

@[to_additive (attr := aesop safe 20 apply (rule_sets := [Measurable]))]
protected theorem smul {𝕜} [TopologicalSpace 𝕜] [SMul 𝕜 β] [ContinuousSMul 𝕜 β] {f : α → 𝕜}
    {g : α → β} (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    StronglyMeasurable fun x => f x • g x :=
  continuous_smul.comp_stronglyMeasurable (hf.prod_mk hg)

@[to_additive (attr := measurability)]
protected theorem const_smul {𝕜} [SMul 𝕜 β] [ContinuousConstSMul 𝕜 β] (hf : StronglyMeasurable f)
    (c : 𝕜) : StronglyMeasurable (c • f) :=
  ⟨fun n => c • hf.approx n, fun x => (hf.tendsto_approx x).const_smul c⟩

@[to_additive (attr := measurability)]
protected theorem const_smul' {𝕜} [SMul 𝕜 β] [ContinuousConstSMul 𝕜 β] (hf : StronglyMeasurable f)
    (c : 𝕜) : StronglyMeasurable fun x => c • f x :=
  hf.const_smul c

@[to_additive (attr := measurability)]
protected theorem smul_const {𝕜} [TopologicalSpace 𝕜] [SMul 𝕜 β] [ContinuousSMul 𝕜 β] {f : α → 𝕜}
    (hf : StronglyMeasurable f) (c : β) : StronglyMeasurable fun x => f x • c :=
  continuous_smul.comp_stronglyMeasurable (hf.prod_mk stronglyMeasurable_const)

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

nonrec theorem _root_.IsUnit.stronglyMeasurable_const_smul_iff {_ : MeasurableSpace α} {c : M}
    (hc : IsUnit c) :
    (StronglyMeasurable fun x => c • f x) ↔ StronglyMeasurable f :=
  let ⟨u, hu⟩ := hc
  hu ▸ stronglyMeasurable_const_smul_iff u

theorem _root_.stronglyMeasurable_const_smul_iff₀ {_ : MeasurableSpace α} {c : G₀} (hc : c ≠ 0) :
    (StronglyMeasurable fun x => c • f x) ↔ StronglyMeasurable f :=
  (IsUnit.mk0 _ hc).stronglyMeasurable_const_smul_iff

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

@[aesop safe 20 (rule_sets := [Measurable])]
protected theorem inf [Inf β] [ContinuousInf β] (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) : StronglyMeasurable (f ⊓ g) :=
  ⟨fun n => hf.approx n ⊓ hg.approx n, fun x =>
    (hf.tendsto_approx x).inf_nhds (hg.tendsto_approx x)⟩

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

@[to_additive (attr := measurability)]
theorem _root_.List.stronglyMeasurable_prod (l : List (α → M))
    (hl : ∀ f ∈ l, StronglyMeasurable f) :
    StronglyMeasurable fun x => (l.map fun f : α → M => f x).prod := by
  simpa only [← Pi.list_prod_apply] using l.stronglyMeasurable_prod' hl

end Monoid

section CommMonoid

variable {M : Type*} [CommMonoid M] [TopologicalSpace M] [ContinuousMul M] {m : MeasurableSpace α}

@[to_additive (attr := measurability)]
theorem _root_.Multiset.stronglyMeasurable_prod' (l : Multiset (α → M))
    (hl : ∀ f ∈ l, StronglyMeasurable f) : StronglyMeasurable l.prod := by
  rcases l with ⟨l⟩
  simpa using l.stronglyMeasurable_prod' (by simpa using hl)

@[to_additive (attr := measurability)]
theorem _root_.Multiset.stronglyMeasurable_prod (s : Multiset (α → M))
    (hs : ∀ f ∈ s, StronglyMeasurable f) :
    StronglyMeasurable fun x => (s.map fun f : α → M => f x).prod := by
  simpa only [← Pi.multiset_prod_apply] using s.stronglyMeasurable_prod' hs

@[to_additive (attr := measurability)]
theorem _root_.Finset.stronglyMeasurable_prod' {ι : Type*} {f : ι → α → M} (s : Finset ι)
    (hf : ∀ i ∈ s, StronglyMeasurable (f i)) : StronglyMeasurable (∏ i ∈ s, f i) :=
  Finset.prod_induction _ _ (fun _a _b ha hb => ha.mul hb) (@stronglyMeasurable_one α M _ _ _) hf

@[to_additive (attr := measurability)]
theorem _root_.Finset.stronglyMeasurable_prod {ι : Type*} {f : ι → α → M} (s : Finset ι)
    (hf : ∀ i ∈ s, StronglyMeasurable (f i)) : StronglyMeasurable fun a => ∏ i ∈ s, f i a := by
  simpa only [← Finset.prod_apply] using s.stronglyMeasurable_prod' hf

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

theorem separableSpace_range_union_singleton {_ : MeasurableSpace α} [TopologicalSpace β]
    [PseudoMetrizableSpace β] (hf : StronglyMeasurable f) {b : β} :
    SeparableSpace (range f ∪ {b} : Set β) :=
  letI := pseudoMetrizableSpacePseudoMetric β
  (hf.isSeparable_range.union (finite_singleton _).isSeparable).separableSpace

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

/-- In a space with second countable topology, strongly measurable and measurable are equivalent. -/
theorem _root_.stronglyMeasurable_iff_measurable [TopologicalSpace β] [MetrizableSpace β]
    [BorelSpace β] [SecondCountableTopology β] : StronglyMeasurable f ↔ Measurable f :=
  ⟨fun h => h.measurable, fun h => Measurable.stronglyMeasurable h⟩

@[measurability]
theorem _root_.stronglyMeasurable_id [TopologicalSpace α] [PseudoMetrizableSpace α]
    [OpensMeasurableSpace α] [SecondCountableTopology α] : StronglyMeasurable (id : α → α) :=
  measurable_id.stronglyMeasurable

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

/-- A continuous function is strongly measurable when either the source space or the target space
is second-countable. -/
theorem _root_.Continuous.stronglyMeasurable [MeasurableSpace α] [TopologicalSpace α]
    [OpensMeasurableSpace α] [TopologicalSpace β] [PseudoMetrizableSpace β]
    [h : SecondCountableTopologyEither α β] {f : α → β} (hf : Continuous f) :
    StronglyMeasurable f := by
  borelize β
  cases h.out
  · rw [stronglyMeasurable_iff_measurable_separable]
    refine ⟨hf.measurable, ?_⟩
    exact isSeparable_range hf
  · exact hf.measurable.stronglyMeasurable

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
  refine
    ⟨fun H => stronglyMeasurable_iff_measurable_separable.2 ⟨?_, ?_⟩, fun H =>
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

/-- A sequential limit of strongly measurable functions is strongly measurable. -/
theorem _root_.stronglyMeasurable_of_tendsto {ι : Type*} {m : MeasurableSpace α}
    [TopologicalSpace β] [PseudoMetrizableSpace β] (u : Filter ι) [NeBot u] [IsCountablyGenerated u]
    {f : ι → α → β} {g : α → β} (hf : ∀ i, StronglyMeasurable (f i)) (lim : Tendsto f u (𝓝 g)) :
    StronglyMeasurable g := by
  borelize β
  refine stronglyMeasurable_iff_measurable_separable.2 ⟨?_, ?_⟩
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

protected theorem piecewise {m : MeasurableSpace α} [TopologicalSpace β] {s : Set α}
    {_ : DecidablePred (· ∈ s)} (hs : MeasurableSet s) (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) : StronglyMeasurable (Set.piecewise s f g) := by
  refine ⟨fun n => SimpleFunc.piecewise s hs (hf.approx n) (hg.approx n), fun x => ?_⟩
  by_cases hx : x ∈ s
  · simpa [@Set.piecewise_eq_of_mem _ _ _ _ _ (fun _ => Classical.propDecidable _) _ hx,
      hx] using hf.tendsto_approx x
  · simpa [@Set.piecewise_eq_of_not_mem _ _ _ _ _ (fun _ => Classical.propDecidable _) _ hx,
      hx] using hg.tendsto_approx x

/-- this is slightly different from `StronglyMeasurable.piecewise`. It can be used to show
`StronglyMeasurable (ite (x=0) 0 1)` by
`exact StronglyMeasurable.ite (measurableSet_singleton 0) stronglyMeasurable_const
stronglyMeasurable_const`, but replacing `StronglyMeasurable.ite` by
`StronglyMeasurable.piecewise` in that example proof does not work. -/
protected theorem ite {_ : MeasurableSpace α} [TopologicalSpace β] {p : α → Prop}
    {_ : DecidablePred p} (hp : MeasurableSet { a : α | p a }) (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) : StronglyMeasurable fun x => ite (p x) (f x) (g x) :=
  StronglyMeasurable.piecewise hp hf hg

@[measurability]
theorem _root_.MeasurableEmbedding.stronglyMeasurable_extend {f : α → β} {g : α → γ} {g' : γ → β}
    {mα : MeasurableSpace α} {mγ : MeasurableSpace γ} [TopologicalSpace β]
    (hg : MeasurableEmbedding g) (hf : StronglyMeasurable f) (hg' : StronglyMeasurable g') :
    StronglyMeasurable (Function.extend g f g') := by
  refine ⟨fun n => SimpleFunc.extend (hf.approx n) g hg (hg'.approx n), ?_⟩
  intro x
  by_cases hx : ∃ y, g y = x
  · rcases hx with ⟨y, rfl⟩
    simpa only [SimpleFunc.extend_apply, hg.injective, Injective.extend_apply] using
      hf.tendsto_approx y
  · simpa only [hx, SimpleFunc.extend_apply', not_false_iff, extend_apply'] using
      hg'.tendsto_approx x

theorem _root_.MeasurableEmbedding.exists_stronglyMeasurable_extend {f : α → β} {g : α → γ}
    {_ : MeasurableSpace α} {_ : MeasurableSpace γ} [TopologicalSpace β]
    (hg : MeasurableEmbedding g) (hf : StronglyMeasurable f) (hne : γ → Nonempty β) :
    ∃ f' : γ → β, StronglyMeasurable f' ∧ f' ∘ g = f :=
  ⟨Function.extend g f fun x => Classical.choice (hne x),
    hg.stronglyMeasurable_extend hf (stronglyMeasurable_const' fun _ _ => rfl),
    funext fun _ => hg.injective.extend_apply _ _ _⟩

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

theorem _root_.stronglyMeasurable_of_restrict_of_restrict_compl {_ : MeasurableSpace α}
    [TopologicalSpace β] {f : α → β} {s : Set α} (hs : MeasurableSet s)
    (h₁ : StronglyMeasurable (s.restrict f)) (h₂ : StronglyMeasurable (sᶜ.restrict f)) :
    StronglyMeasurable f :=
  stronglyMeasurable_of_stronglyMeasurable_union_cover s sᶜ hs hs.compl (union_compl_self s).ge h₁
    h₂

@[measurability]
protected theorem indicator {_ : MeasurableSpace α} [TopologicalSpace β] [Zero β]
    (hf : StronglyMeasurable f) {s : Set α} (hs : MeasurableSet s) :
    StronglyMeasurable (s.indicator f) :=
  hf.piecewise hs stronglyMeasurable_const

@[aesop safe 20 apply (rule_sets := [Measurable])]
protected theorem dist {_ : MeasurableSpace α} {β : Type*} [PseudoMetricSpace β] {f g : α → β}
    (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    StronglyMeasurable fun x => dist (f x) (g x) :=
  continuous_dist.comp_stronglyMeasurable (hf.prod_mk hg)

@[measurability]
protected theorem norm {_ : MeasurableSpace α} {β : Type*} [SeminormedAddCommGroup β] {f : α → β}
    (hf : StronglyMeasurable f) : StronglyMeasurable fun x => ‖f x‖ :=
  continuous_norm.comp_stronglyMeasurable hf

@[measurability]
protected theorem nnnorm {_ : MeasurableSpace α} {β : Type*} [SeminormedAddCommGroup β] {f : α → β}
    (hf : StronglyMeasurable f) : StronglyMeasurable fun x => ‖f x‖₊ :=
  continuous_nnnorm.comp_stronglyMeasurable hf

@[measurability]
protected theorem ennnorm {_ : MeasurableSpace α} {β : Type*} [SeminormedAddCommGroup β]
    {f : α → β} (hf : StronglyMeasurable f) : Measurable fun a => (‖f a‖₊ : ℝ≥0∞) :=
  (ENNReal.continuous_coe.comp_stronglyMeasurable hf.nnnorm).measurable

@[measurability]
protected theorem real_toNNReal {_ : MeasurableSpace α} {f : α → ℝ} (hf : StronglyMeasurable f) :
    StronglyMeasurable fun x => (f x).toNNReal :=
  continuous_real_toNNReal.comp_stronglyMeasurable hf

theorem measurableSet_eq_fun {m : MeasurableSpace α} {E} [TopologicalSpace E] [MetrizableSpace E]
    {f g : α → E} (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    MeasurableSet { x | f x = g x } := by
  borelize (E × E)
  exact (hf.prod_mk hg).measurable isClosed_diagonal.measurableSet

theorem measurableSet_lt {m : MeasurableSpace α} [TopologicalSpace β] [LinearOrder β]
    [OrderClosedTopology β] [PseudoMetrizableSpace β] {f g : α → β} (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) : MeasurableSet { a | f a < g a } := by
  borelize (β × β)
  exact (hf.prod_mk hg).measurable isOpen_lt_prod.measurableSet

theorem measurableSet_le {m : MeasurableSpace α} [TopologicalSpace β] [Preorder β]
    [OrderClosedTopology β] [PseudoMetrizableSpace β] {f g : α → β} (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) : MeasurableSet { a | f a ≤ g a } := by
  borelize (β × β)
  exact (hf.prod_mk hg).measurable isClosed_le_prod.measurableSet

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
  refine ⟨g_seq_s, fun x => ?_, hg_zero⟩
  by_cases hx : x ∈ s
  · simp_rw [hg_eq x hx]
    exact hf.tendsto_approx x
  · simp_rw [hg_zero x hx, hf_zero x hx]
    exact tendsto_const_nhds

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
    refine hs Set.univ ?_
    rwa [Set.inter_univ]
  obtain ⟨g_seq_s, hg_seq_tendsto, hg_seq_zero⟩ := stronglyMeasurable_in_set hs_m hf hf_zero
  let g_seq_s₂ : ℕ → @SimpleFunc α m₂ E := fun n =>
    { toFun := g_seq_s n
      measurableSet_fiber' := fun x => by
        rw [← Set.inter_univ (g_seq_s n ⁻¹' {x}), ← Set.union_compl_self s,
          Set.inter_union_distrib_left, Set.inter_comm (g_seq_s n ⁻¹' {x})]
        refine MeasurableSet.union (hs _ (hs_m.inter ?_)) ?_
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
          refine Function.mtr fun hys => ?_
          rw [hg_seq_zero y hys n]
          exact Ne.symm hx
      finite_range' := @SimpleFunc.finite_range _ _ m (g_seq_s n) }
  exact ⟨g_seq_s₂, hg_seq_tendsto⟩

/-- If a function `f` is strongly measurable w.r.t. a sub-σ-algebra `m` and the measure is σ-finite
on `m`, then there exists spanning measurable sets with finite measure on which `f` has bounded
norm. In particular, `f` is integrable on each of those sets. -/
theorem exists_spanning_measurableSet_norm_le [SeminormedAddCommGroup β] {m m0 : MeasurableSpace α}
    (hm : m ≤ m0) (hf : StronglyMeasurable[m] f) (μ : Measure α) [SigmaFinite (μ.trim hm)] :
    ∃ s : ℕ → Set α,
      (∀ n, MeasurableSet[m] (s n) ∧ μ (s n) < ∞ ∧ ∀ x ∈ s n, ‖f x‖ ≤ n) ∧
      ⋃ i, s i = Set.univ := by
  obtain ⟨s, hs, hs_univ⟩ :=
    @exists_spanning_measurableSet_le _ m _ hf.nnnorm.measurable (μ.trim hm) _
  refine ⟨s, fun n ↦ ⟨(hs n).1, (le_trim hm).trans_lt (hs n).2.1, fun x hx ↦ ?_⟩, hs_univ⟩
  have hx_nnnorm : ‖f x‖₊ ≤ n := (hs n).2.2 x hx
  rw [← coe_nnnorm]
  norm_cast

end StronglyMeasurable

/-! ## Finitely strongly measurable functions -/


theorem finStronglyMeasurable_zero {α β} {m : MeasurableSpace α} {μ : Measure α} [Zero β]
    [TopologicalSpace β] : FinStronglyMeasurable (0 : α → β) μ :=
  ⟨0, by
    simp only [Pi.zero_apply, SimpleFunc.coe_zero, support_zero', measure_empty,
      zero_lt_top, forall_const],
    fun _ => tendsto_const_nhds⟩

namespace FinStronglyMeasurable

variable {m0 : MeasurableSpace α} {μ : Measure α} {f g : α → β}

theorem aefinStronglyMeasurable [Zero β] [TopologicalSpace β] (hf : FinStronglyMeasurable f μ) :
    AEFinStronglyMeasurable f μ :=
  ⟨f, hf, ae_eq_refl f⟩

section sequence

variable [Zero β] [TopologicalSpace β] (hf : FinStronglyMeasurable f μ)

/-- A sequence of simple functions such that `∀ x, Tendsto (fun n ↦ hf.approx n x) atTop (𝓝 (f x))`
and `∀ n, μ (support (hf.approx n)) < ∞`. These properties are given by
`FinStronglyMeasurable.tendsto_approx` and `FinStronglyMeasurable.fin_support_approx`. -/
protected noncomputable def approx : ℕ → α →ₛ β :=
  hf.choose

protected theorem fin_support_approx : ∀ n, μ (support (hf.approx n)) < ∞ :=
  hf.choose_spec.1

protected theorem tendsto_approx : ∀ x, Tendsto (fun n => hf.approx n x) atTop (𝓝 (f x)) :=
  hf.choose_spec.2

end sequence

/-- A finitely strongly measurable function is strongly measurable. -/
@[aesop 5% apply (rule_sets := [Measurable])]
protected theorem stronglyMeasurable [Zero β] [TopologicalSpace β]
    (hf : FinStronglyMeasurable f μ) : StronglyMeasurable f :=
  ⟨hf.approx, hf.tendsto_approx⟩

theorem exists_set_sigmaFinite [Zero β] [TopologicalSpace β] [T2Space β]
    (hf : FinStronglyMeasurable f μ) :
    ∃ t, MeasurableSet t ∧ (∀ x ∈ tᶜ, f x = 0) ∧ SigmaFinite (μ.restrict t) := by
  rcases hf with ⟨fs, hT_lt_top, h_approx⟩
  let T n := support (fs n)
  have hT_meas : ∀ n, MeasurableSet (T n) := fun n => SimpleFunc.measurableSet_support (fs n)
  let t := ⋃ n, T n
  refine ⟨t, MeasurableSet.iUnion hT_meas, ?_, ?_⟩
  · have h_fs_zero : ∀ n, ∀ x ∈ tᶜ, fs n x = 0 := by
      intro n x hxt
      rw [Set.mem_compl_iff, Set.mem_iUnion, not_exists] at hxt
      simpa [T] using hxt n
    refine fun x hxt => tendsto_nhds_unique (h_approx x) ?_
    rw [funext fun n => h_fs_zero n x hxt]
    exact tendsto_const_nhds
  · refine ⟨⟨⟨fun n => tᶜ ∪ T n, fun _ => trivial, fun n => ?_, ?_⟩⟩⟩
    · rw [Measure.restrict_apply' (MeasurableSet.iUnion hT_meas), Set.union_inter_distrib_right,
        Set.compl_inter_self t, Set.empty_union]
      exact (measure_mono Set.inter_subset_left).trans_lt (hT_lt_top n)
    · rw [← Set.union_iUnion tᶜ T]
      exact Set.compl_union_self _

/-- A finitely strongly measurable function is measurable. -/
protected theorem measurable [Zero β] [TopologicalSpace β] [PseudoMetrizableSpace β]
    [MeasurableSpace β] [BorelSpace β] (hf : FinStronglyMeasurable f μ) : Measurable f :=
  hf.stronglyMeasurable.measurable

section Arithmetic

variable [TopologicalSpace β]

@[aesop safe 20 (rule_sets := [Measurable])]
protected theorem mul [MonoidWithZero β] [ContinuousMul β] (hf : FinStronglyMeasurable f μ)
    (hg : FinStronglyMeasurable g μ) : FinStronglyMeasurable (f * g) μ := by
  refine
    ⟨fun n => hf.approx n * hg.approx n, ?_, fun x =>
      (hf.tendsto_approx x).mul (hg.tendsto_approx x)⟩
  intro n
  exact (measure_mono (support_mul_subset_left _ _)).trans_lt (hf.fin_support_approx n)

@[aesop safe 20 (rule_sets := [Measurable])]
protected theorem add [AddMonoid β] [ContinuousAdd β] (hf : FinStronglyMeasurable f μ)
    (hg : FinStronglyMeasurable g μ) : FinStronglyMeasurable (f + g) μ :=
  ⟨fun n => hf.approx n + hg.approx n, fun n =>
    (measure_mono (Function.support_add _ _)).trans_lt
      ((measure_union_le _ _).trans_lt
        (ENNReal.add_lt_top.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩)),
    fun x => (hf.tendsto_approx x).add (hg.tendsto_approx x)⟩

@[measurability]
protected theorem neg [AddGroup β] [TopologicalAddGroup β] (hf : FinStronglyMeasurable f μ) :
    FinStronglyMeasurable (-f) μ := by
  refine ⟨fun n => -hf.approx n, fun n => ?_, fun x => (hf.tendsto_approx x).neg⟩
  suffices μ (Function.support fun x => -(hf.approx n) x) < ∞ by convert this
  rw [Function.support_neg (hf.approx n)]
  exact hf.fin_support_approx n

@[measurability]
protected theorem sub [AddGroup β] [ContinuousSub β] (hf : FinStronglyMeasurable f μ)
    (hg : FinStronglyMeasurable g μ) : FinStronglyMeasurable (f - g) μ :=
  ⟨fun n => hf.approx n - hg.approx n, fun n =>
    (measure_mono (Function.support_sub _ _)).trans_lt
      ((measure_union_le _ _).trans_lt
        (ENNReal.add_lt_top.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩)),
    fun x => (hf.tendsto_approx x).sub (hg.tendsto_approx x)⟩

@[measurability]
protected theorem const_smul {𝕜} [TopologicalSpace 𝕜] [AddMonoid β] [Monoid 𝕜]
    [DistribMulAction 𝕜 β] [ContinuousSMul 𝕜 β] (hf : FinStronglyMeasurable f μ) (c : 𝕜) :
    FinStronglyMeasurable (c • f) μ := by
  refine ⟨fun n => c • hf.approx n, fun n => ?_, fun x => (hf.tendsto_approx x).const_smul c⟩
  rw [SimpleFunc.coe_smul]
  exact (measure_mono (support_const_smul_subset c _)).trans_lt (hf.fin_support_approx n)

end Arithmetic

section Order

variable [TopologicalSpace β] [Zero β]

@[aesop safe 20 (rule_sets := [Measurable])]
protected theorem sup [SemilatticeSup β] [ContinuousSup β] (hf : FinStronglyMeasurable f μ)
    (hg : FinStronglyMeasurable g μ) : FinStronglyMeasurable (f ⊔ g) μ := by
  refine
    ⟨fun n => hf.approx n ⊔ hg.approx n, fun n => ?_, fun x =>
      (hf.tendsto_approx x).sup_nhds (hg.tendsto_approx x)⟩
  refine (measure_mono (support_sup _ _)).trans_lt ?_
  exact measure_union_lt_top_iff.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩

@[aesop safe 20 (rule_sets := [Measurable])]
protected theorem inf [SemilatticeInf β] [ContinuousInf β] (hf : FinStronglyMeasurable f μ)
    (hg : FinStronglyMeasurable g μ) : FinStronglyMeasurable (f ⊓ g) μ := by
  refine
    ⟨fun n => hf.approx n ⊓ hg.approx n, fun n => ?_, fun x =>
      (hf.tendsto_approx x).inf_nhds (hg.tendsto_approx x)⟩
  refine (measure_mono (support_inf _ _)).trans_lt ?_
  exact measure_union_lt_top_iff.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩

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

theorem aefinStronglyMeasurable_zero {α β} {_ : MeasurableSpace α} (μ : Measure α) [Zero β]
    [TopologicalSpace β] : AEFinStronglyMeasurable (0 : α → β) μ :=
  ⟨0, finStronglyMeasurable_zero, EventuallyEq.rfl⟩

/-! ## Almost everywhere strongly measurable functions -/

@[measurability]
theorem aestronglyMeasurable_const {α β} {_ : MeasurableSpace α} {μ : Measure α}
    [TopologicalSpace β] {b : β} : AEStronglyMeasurable (fun _ : α => b) μ :=
  stronglyMeasurable_const.aestronglyMeasurable

@[to_additive (attr := measurability)]
theorem aestronglyMeasurable_one {α β} {_ : MeasurableSpace α} {μ : Measure α} [TopologicalSpace β]
    [One β] : AEStronglyMeasurable (1 : α → β) μ :=
  stronglyMeasurable_one.aestronglyMeasurable

@[simp]
theorem Subsingleton.aestronglyMeasurable {_ : MeasurableSpace α} [TopologicalSpace β]
    [Subsingleton β] {μ : Measure α} (f : α → β) : AEStronglyMeasurable f μ :=
  (Subsingleton.stronglyMeasurable f).aestronglyMeasurable

@[simp]
theorem Subsingleton.aestronglyMeasurable' {_ : MeasurableSpace α} [TopologicalSpace β]
    [Subsingleton α] {μ : Measure α} (f : α → β) : AEStronglyMeasurable f μ :=
  (Subsingleton.stronglyMeasurable' f).aestronglyMeasurable

@[simp]
theorem aestronglyMeasurable_zero_measure [MeasurableSpace α] [TopologicalSpace β] (f : α → β) :
    AEStronglyMeasurable f (0 : Measure α) := by
  nontriviality α
  inhabit α
  exact ⟨fun _ => f default, stronglyMeasurable_const, rfl⟩

@[measurability]
theorem SimpleFunc.aestronglyMeasurable {_ : MeasurableSpace α} {μ : Measure α} [TopologicalSpace β]
    (f : α →ₛ β) : AEStronglyMeasurable f μ :=
  f.stronglyMeasurable.aestronglyMeasurable

namespace AEStronglyMeasurable

variable {m : MeasurableSpace α} {μ ν : Measure α} [TopologicalSpace β] [TopologicalSpace γ]
  {f g : α → β}

section Mk

/-- A `StronglyMeasurable` function such that `f =ᵐ[μ] hf.mk f`. See lemmas
`stronglyMeasurable_mk` and `ae_eq_mk`. -/
protected noncomputable def mk (f : α → β) (hf : AEStronglyMeasurable f μ) : α → β :=
  hf.choose

theorem stronglyMeasurable_mk (hf : AEStronglyMeasurable f μ) : StronglyMeasurable (hf.mk f) :=
  hf.choose_spec.1

theorem measurable_mk [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
    (hf : AEStronglyMeasurable f μ) : Measurable (hf.mk f) :=
  hf.stronglyMeasurable_mk.measurable

theorem ae_eq_mk (hf : AEStronglyMeasurable f μ) : f =ᵐ[μ] hf.mk f :=
  hf.choose_spec.2

@[aesop 5% apply (rule_sets := [Measurable])]
protected theorem aemeasurable {β} [MeasurableSpace β] [TopologicalSpace β]
    [PseudoMetrizableSpace β] [BorelSpace β] {f : α → β} (hf : AEStronglyMeasurable f μ) :
    AEMeasurable f μ :=
  ⟨hf.mk f, hf.stronglyMeasurable_mk.measurable, hf.ae_eq_mk⟩

end Mk

theorem congr (hf : AEStronglyMeasurable f μ) (h : f =ᵐ[μ] g) : AEStronglyMeasurable g μ :=
  ⟨hf.mk f, hf.stronglyMeasurable_mk, h.symm.trans hf.ae_eq_mk⟩

theorem _root_.aestronglyMeasurable_congr (h : f =ᵐ[μ] g) :
    AEStronglyMeasurable f μ ↔ AEStronglyMeasurable g μ :=
  ⟨fun hf => hf.congr h, fun hg => hg.congr h.symm⟩

theorem mono_measure {ν : Measure α} (hf : AEStronglyMeasurable f μ) (h : ν ≤ μ) :
    AEStronglyMeasurable f ν :=
  ⟨hf.mk f, hf.stronglyMeasurable_mk, Eventually.filter_mono (ae_mono h) hf.ae_eq_mk⟩

protected lemma mono_ac (h : ν ≪ μ) (hμ : AEStronglyMeasurable f μ) : AEStronglyMeasurable f ν :=
  let ⟨g, hg, hg'⟩ := hμ; ⟨g, hg, h.ae_eq hg'⟩

@[deprecated (since := "2024-02-15")] protected alias mono' := AEStronglyMeasurable.mono_ac

theorem mono_set {s t} (h : s ⊆ t) (ht : AEStronglyMeasurable f (μ.restrict t)) :
    AEStronglyMeasurable f (μ.restrict s) :=
  ht.mono_measure (restrict_mono h le_rfl)

protected theorem restrict (hfm : AEStronglyMeasurable f μ) {s} :
    AEStronglyMeasurable f (μ.restrict s) :=
  hfm.mono_measure Measure.restrict_le_self

theorem ae_mem_imp_eq_mk {s} (h : AEStronglyMeasurable f (μ.restrict s)) :
    ∀ᵐ x ∂μ, x ∈ s → f x = h.mk f x :=
  ae_imp_of_ae_restrict h.ae_eq_mk

/-- The composition of a continuous function and an ae strongly measurable function is ae strongly
measurable. -/
theorem _root_.Continuous.comp_aestronglyMeasurable {g : β → γ} {f : α → β} (hg : Continuous g)
    (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurable (fun x => g (f x)) μ :=
  ⟨_, hg.comp_stronglyMeasurable hf.stronglyMeasurable_mk, EventuallyEq.fun_comp hf.ae_eq_mk g⟩

/-- A continuous function from `α` to `β` is ae strongly measurable when one of the two spaces is
second countable. -/
theorem _root_.Continuous.aestronglyMeasurable [TopologicalSpace α] [OpensMeasurableSpace α]
    [PseudoMetrizableSpace β] [SecondCountableTopologyEither α β] (hf : Continuous f) :
    AEStronglyMeasurable f μ :=
  hf.stronglyMeasurable.aestronglyMeasurable

protected theorem prod_mk {f : α → β} {g : α → γ} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) : AEStronglyMeasurable (fun x => (f x, g x)) μ :=
  ⟨fun x => (hf.mk f x, hg.mk g x), hf.stronglyMeasurable_mk.prod_mk hg.stronglyMeasurable_mk,
    hf.ae_eq_mk.prod_mk hg.ae_eq_mk⟩

/-- The composition of a continuous function of two variables and two ae strongly measurable
functions is ae strongly measurable. -/
theorem _root_.Continuous.comp_aestronglyMeasurable₂
    {β' : Type*} [TopologicalSpace β']
    {g : β → β' → γ} {f : α → β} {f' : α → β'} (hg : Continuous g.uncurry)
    (hf : AEStronglyMeasurable f μ) (h'f : AEStronglyMeasurable f' μ) :
    AEStronglyMeasurable (fun x => g (f x) (f' x)) μ :=
  hg.comp_aestronglyMeasurable (hf.prod_mk h'f)

/-- In a space with second countable topology, measurable implies ae strongly measurable. -/
@[fun_prop, aesop unsafe 30% apply (rule_sets := [Measurable])]
theorem _root_.Measurable.aestronglyMeasurable {_ : MeasurableSpace α} {μ : Measure α}
    [MeasurableSpace β] [PseudoMetrizableSpace β] [SecondCountableTopology β]
    [OpensMeasurableSpace β] (hf : Measurable f) : AEStronglyMeasurable f μ :=
  hf.stronglyMeasurable.aestronglyMeasurable

section Arithmetic

@[to_additive (attr := aesop safe 20 apply (rule_sets := [Measurable]))]
protected theorem mul [Mul β] [ContinuousMul β] (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) : AEStronglyMeasurable (f * g) μ :=
  ⟨hf.mk f * hg.mk g, hf.stronglyMeasurable_mk.mul hg.stronglyMeasurable_mk,
    hf.ae_eq_mk.mul hg.ae_eq_mk⟩

@[to_additive (attr := measurability)]
protected theorem mul_const [Mul β] [ContinuousMul β] (hf : AEStronglyMeasurable f μ) (c : β) :
    AEStronglyMeasurable (fun x => f x * c) μ :=
  hf.mul aestronglyMeasurable_const

@[to_additive (attr := measurability)]
protected theorem const_mul [Mul β] [ContinuousMul β] (hf : AEStronglyMeasurable f μ) (c : β) :
    AEStronglyMeasurable (fun x => c * f x) μ :=
  aestronglyMeasurable_const.mul hf

@[to_additive (attr := measurability)]
protected theorem inv [Inv β] [ContinuousInv β] (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable f⁻¹ μ :=
  ⟨(hf.mk f)⁻¹, hf.stronglyMeasurable_mk.inv, hf.ae_eq_mk.inv⟩

@[to_additive (attr := aesop safe 20 apply (rule_sets := [Measurable]))]
protected theorem div [Group β] [TopologicalGroup β] (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) : AEStronglyMeasurable (f / g) μ :=
  ⟨hf.mk f / hg.mk g, hf.stronglyMeasurable_mk.div hg.stronglyMeasurable_mk,
    hf.ae_eq_mk.div hg.ae_eq_mk⟩

@[to_additive]
theorem mul_iff_right [CommGroup β] [TopologicalGroup β] (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (f * g) μ ↔ AEStronglyMeasurable g μ :=
  ⟨fun h ↦ show g = f * g * f⁻¹ by simp only [mul_inv_cancel_comm] ▸ h.mul hf.inv,
    fun h ↦ hf.mul h⟩

@[to_additive]
theorem mul_iff_left [CommGroup β] [TopologicalGroup β] (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (g * f) μ ↔ AEStronglyMeasurable g μ :=
  mul_comm g f ▸ AEStronglyMeasurable.mul_iff_right hf

@[to_additive (attr := aesop safe 20 apply (rule_sets := [Measurable]))]
protected theorem smul {𝕜} [TopologicalSpace 𝕜] [SMul 𝕜 β] [ContinuousSMul 𝕜 β] {f : α → 𝕜}
    {g : α → β} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun x => f x • g x) μ :=
  continuous_smul.comp_aestronglyMeasurable (hf.prod_mk hg)

@[to_additive (attr := aesop safe 20 apply (rule_sets := [Measurable])) const_nsmul]
protected theorem pow [Monoid β] [ContinuousMul β] (hf : AEStronglyMeasurable f μ) (n : ℕ) :
    AEStronglyMeasurable (f ^ n) μ :=
  ⟨hf.mk f ^ n, hf.stronglyMeasurable_mk.pow _, hf.ae_eq_mk.pow_const _⟩

@[to_additive (attr := measurability)]
protected theorem const_smul {𝕜} [SMul 𝕜 β] [ContinuousConstSMul 𝕜 β]
    (hf : AEStronglyMeasurable f μ) (c : 𝕜) : AEStronglyMeasurable (c • f) μ :=
  ⟨c • hf.mk f, hf.stronglyMeasurable_mk.const_smul c, hf.ae_eq_mk.const_smul c⟩

@[to_additive (attr := measurability)]
protected theorem const_smul' {𝕜} [SMul 𝕜 β] [ContinuousConstSMul 𝕜 β]
    (hf : AEStronglyMeasurable f μ) (c : 𝕜) : AEStronglyMeasurable (fun x => c • f x) μ :=
  hf.const_smul c

@[to_additive (attr := measurability)]
protected theorem smul_const {𝕜} [TopologicalSpace 𝕜] [SMul 𝕜 β] [ContinuousSMul 𝕜 β] {f : α → 𝕜}
    (hf : AEStronglyMeasurable f μ) (c : β) : AEStronglyMeasurable (fun x => f x • c) μ :=
  continuous_smul.comp_aestronglyMeasurable (hf.prod_mk aestronglyMeasurable_const)

end Arithmetic

section Order

@[aesop safe 20 apply (rule_sets := [Measurable])]
protected theorem sup [SemilatticeSup β] [ContinuousSup β] (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) : AEStronglyMeasurable (f ⊔ g) μ :=
  ⟨hf.mk f ⊔ hg.mk g, hf.stronglyMeasurable_mk.sup hg.stronglyMeasurable_mk,
    hf.ae_eq_mk.sup hg.ae_eq_mk⟩

@[aesop safe 20 apply (rule_sets := [Measurable])]
protected theorem inf [SemilatticeInf β] [ContinuousInf β] (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) : AEStronglyMeasurable (f ⊓ g) μ :=
  ⟨hf.mk f ⊓ hg.mk g, hf.stronglyMeasurable_mk.inf hg.stronglyMeasurable_mk,
    hf.ae_eq_mk.inf hg.ae_eq_mk⟩

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

@[to_additive (attr := measurability)]
theorem _root_.List.aestronglyMeasurable_prod
    (l : List (α → M)) (hl : ∀ f ∈ l, AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => (l.map fun f : α → M => f x).prod) μ := by
  simpa only [← Pi.list_prod_apply] using l.aestronglyMeasurable_prod' hl

end Monoid

section CommMonoid

variable {M : Type*} [CommMonoid M] [TopologicalSpace M] [ContinuousMul M]

@[to_additive (attr := measurability)]
theorem _root_.Multiset.aestronglyMeasurable_prod' (l : Multiset (α → M))
    (hl : ∀ f ∈ l, AEStronglyMeasurable f μ) : AEStronglyMeasurable l.prod μ := by
  rcases l with ⟨l⟩
  simpa using l.aestronglyMeasurable_prod' (by simpa using hl)

@[to_additive (attr := measurability)]
theorem _root_.Multiset.aestronglyMeasurable_prod (s : Multiset (α → M))
    (hs : ∀ f ∈ s, AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => (s.map fun f : α → M => f x).prod) μ := by
  simpa only [← Pi.multiset_prod_apply] using s.aestronglyMeasurable_prod' hs

@[to_additive (attr := measurability)]
theorem _root_.Finset.aestronglyMeasurable_prod' {ι : Type*} {f : ι → α → M} (s : Finset ι)
    (hf : ∀ i ∈ s, AEStronglyMeasurable (f i) μ) : AEStronglyMeasurable (∏ i ∈ s, f i) μ :=
  Multiset.aestronglyMeasurable_prod' _ fun _g hg =>
    let ⟨_i, hi, hg⟩ := Multiset.mem_map.1 hg
    hg ▸ hf _ hi

@[to_additive (attr := measurability)]
theorem _root_.Finset.aestronglyMeasurable_prod {ι : Type*} {f : ι → α → M} (s : Finset ι)
    (hf : ∀ i ∈ s, AEStronglyMeasurable (f i) μ) :
    AEStronglyMeasurable (fun a => ∏ i ∈ s, f i a) μ := by
  simpa only [← Finset.prod_apply] using s.aestronglyMeasurable_prod' hf

end CommMonoid

section SecondCountableAEStronglyMeasurable

variable [MeasurableSpace β]

/-- In a space with second countable topology, measurable implies strongly measurable. -/
@[aesop 90% apply (rule_sets := [Measurable])]
theorem _root_.AEMeasurable.aestronglyMeasurable [PseudoMetrizableSpace β] [OpensMeasurableSpace β]
    [SecondCountableTopology β] (hf : AEMeasurable f μ) : AEStronglyMeasurable f μ :=
  ⟨hf.mk f, hf.measurable_mk.stronglyMeasurable, hf.ae_eq_mk⟩

@[measurability]
theorem _root_.aestronglyMeasurable_id {α : Type*} [TopologicalSpace α] [PseudoMetrizableSpace α]
    {_ : MeasurableSpace α} [OpensMeasurableSpace α] [SecondCountableTopology α] {μ : Measure α} :
    AEStronglyMeasurable (id : α → α) μ :=
  aemeasurable_id.aestronglyMeasurable

/-- In a space with second countable topology, strongly measurable and measurable are equivalent. -/
theorem _root_.aestronglyMeasurable_iff_aemeasurable [PseudoMetrizableSpace β] [BorelSpace β]
    [SecondCountableTopology β] : AEStronglyMeasurable f μ ↔ AEMeasurable f μ :=
  ⟨fun h => h.aemeasurable, fun h => h.aestronglyMeasurable⟩

end SecondCountableAEStronglyMeasurable

@[aesop safe 20 apply (rule_sets := [Measurable])]
protected theorem dist {β : Type*} [PseudoMetricSpace β] {f g : α → β}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun x => dist (f x) (g x)) μ :=
  continuous_dist.comp_aestronglyMeasurable (hf.prod_mk hg)

@[measurability]
protected theorem norm {β : Type*} [SeminormedAddCommGroup β] {f : α → β}
    (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurable (fun x => ‖f x‖) μ :=
  continuous_norm.comp_aestronglyMeasurable hf

@[measurability]
protected theorem nnnorm {β : Type*} [SeminormedAddCommGroup β] {f : α → β}
    (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurable (fun x => ‖f x‖₊) μ :=
  continuous_nnnorm.comp_aestronglyMeasurable hf

@[measurability]
protected theorem ennnorm {β : Type*} [SeminormedAddCommGroup β] {f : α → β}
    (hf : AEStronglyMeasurable f μ) : AEMeasurable (fun a => (‖f a‖₊ : ℝ≥0∞)) μ :=
  (ENNReal.continuous_coe.comp_aestronglyMeasurable hf.nnnorm).aemeasurable

@[aesop safe 20 apply (rule_sets := [Measurable])]
protected theorem edist {β : Type*} [SeminormedAddCommGroup β] {f g : α → β}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    AEMeasurable (fun a => edist (f a) (g a)) μ :=
  (continuous_edist.comp_aestronglyMeasurable (hf.prod_mk hg)).aemeasurable

@[measurability]
protected theorem real_toNNReal {f : α → ℝ} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => (f x).toNNReal) μ :=
  continuous_real_toNNReal.comp_aestronglyMeasurable hf

theorem _root_.aestronglyMeasurable_indicator_iff [Zero β] {s : Set α} (hs : MeasurableSet s) :
    AEStronglyMeasurable (indicator s f) μ ↔ AEStronglyMeasurable f (μ.restrict s) := by
  constructor
  · intro h
    exact (h.mono_measure Measure.restrict_le_self).congr (indicator_ae_eq_restrict hs)
  · intro h
    refine ⟨indicator s (h.mk f), h.stronglyMeasurable_mk.indicator hs, ?_⟩
    have A : s.indicator f =ᵐ[μ.restrict s] s.indicator (h.mk f) :=
      (indicator_ae_eq_restrict hs).trans (h.ae_eq_mk.trans <| (indicator_ae_eq_restrict hs).symm)
    have B : s.indicator f =ᵐ[μ.restrict sᶜ] s.indicator (h.mk f) :=
      (indicator_ae_eq_restrict_compl hs).trans (indicator_ae_eq_restrict_compl hs).symm
    exact ae_of_ae_restrict_of_ae_restrict_compl _ A B

@[measurability]
protected theorem indicator [Zero β] (hfm : AEStronglyMeasurable f μ) {s : Set α}
    (hs : MeasurableSet s) : AEStronglyMeasurable (s.indicator f) μ :=
  (aestronglyMeasurable_indicator_iff hs).mpr hfm.restrict

theorem nullMeasurableSet_eq_fun {E} [TopologicalSpace E] [MetrizableSpace E] {f g : α → E}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    NullMeasurableSet { x | f x = g x } μ := by
  apply
    (hf.stronglyMeasurable_mk.measurableSet_eq_fun
          hg.stronglyMeasurable_mk).nullMeasurableSet.congr
  filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with x hfx hgx
  change (hf.mk f x = hg.mk g x) = (f x = g x)
  simp only [hfx, hgx]

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

theorem nullMeasurableSet_le [Preorder β] [OrderClosedTopology β] [PseudoMetrizableSpace β]
    {f g : α → β} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    NullMeasurableSet { a | f a ≤ g a } μ := by
  apply
    (hf.stronglyMeasurable_mk.measurableSet_le hg.stronglyMeasurable_mk).nullMeasurableSet.congr
  filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with x hfx hgx
  change (hf.mk f x ≤ hg.mk g x) = (f x ≤ g x)
  simp only [hfx, hgx]

theorem _root_.aestronglyMeasurable_of_aestronglyMeasurable_trim {α} {m m0 : MeasurableSpace α}
    {μ : Measure α} (hm : m ≤ m0) {f : α → β} (hf : AEStronglyMeasurable f (μ.trim hm)) :
    AEStronglyMeasurable f μ :=
  ⟨hf.mk f, StronglyMeasurable.mono hf.stronglyMeasurable_mk hm, ae_eq_of_ae_eq_trim hf.ae_eq_mk⟩

theorem comp_aemeasurable {γ : Type*} {_ : MeasurableSpace γ} {_ : MeasurableSpace α} {f : γ → α}
    {μ : Measure γ} (hg : AEStronglyMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) :
    AEStronglyMeasurable (g ∘ f) μ :=
  ⟨hg.mk g ∘ hf.mk f, hg.stronglyMeasurable_mk.comp_measurable hf.measurable_mk,
    (ae_eq_comp hf hg.ae_eq_mk).trans (hf.ae_eq_mk.fun_comp (hg.mk g))⟩

theorem comp_measurable {γ : Type*} {_ : MeasurableSpace γ} {_ : MeasurableSpace α} {f : γ → α}
    {μ : Measure γ} (hg : AEStronglyMeasurable g (Measure.map f μ)) (hf : Measurable f) :
    AEStronglyMeasurable (g ∘ f) μ :=
  hg.comp_aemeasurable hf.aemeasurable

theorem comp_quasiMeasurePreserving {γ : Type*} {_ : MeasurableSpace γ} {_ : MeasurableSpace α}
    {f : γ → α} {μ : Measure γ} {ν : Measure α} (hg : AEStronglyMeasurable g ν)
    (hf : QuasiMeasurePreserving f μ ν) : AEStronglyMeasurable (g ∘ f) μ :=
  (hg.mono_ac hf.absolutelyContinuous).comp_measurable hf.measurable

theorem isSeparable_ae_range (hf : AEStronglyMeasurable f μ) :
    ∃ t : Set β, IsSeparable t ∧ ∀ᵐ x ∂μ, f x ∈ t := by
  refine ⟨range (hf.mk f), hf.stronglyMeasurable_mk.isSeparable_range, ?_⟩
  filter_upwards [hf.ae_eq_mk] with x hx
  simp [hx]

/-- A function is almost everywhere strongly measurable if and only if it is almost everywhere
measurable, and up to a zero measure set its range is contained in a separable set. -/
theorem _root_.aestronglyMeasurable_iff_aemeasurable_separable [PseudoMetrizableSpace β]
    [MeasurableSpace β] [BorelSpace β] :
    AEStronglyMeasurable f μ ↔
      AEMeasurable f μ ∧ ∃ t : Set β, IsSeparable t ∧ ∀ᵐ x ∂μ, f x ∈ t := by
  refine ⟨fun H => ⟨H.aemeasurable, H.isSeparable_ae_range⟩, ?_⟩
  rintro ⟨H, ⟨t, t_sep, ht⟩⟩
  rcases eq_empty_or_nonempty t with (rfl | h₀)
  · simp only [mem_empty_iff_false, eventually_false_iff_eq_bot, ae_eq_bot] at ht
    rw [ht]
    exact aestronglyMeasurable_zero_measure f
  · obtain ⟨g, g_meas, gt, fg⟩ : ∃ g : α → β, Measurable g ∧ range g ⊆ t ∧ f =ᵐ[μ] g :=
      H.exists_ae_eq_range_subset ht h₀
    refine ⟨g, ?_, fg⟩
    exact stronglyMeasurable_iff_measurable_separable.2 ⟨g_meas, t_sep.mono gt⟩

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
  refine ⟨fun H => H.comp_measurable hf.measurable, ?_⟩
  rintro ⟨g₁, hgm₁, heq⟩
  rcases hf.exists_stronglyMeasurable_extend hgm₁ fun x => ⟨g x⟩ with ⟨g₂, hgm₂, rfl⟩
  exact ⟨g₂, hgm₂, hf.ae_map_iff.2 heq⟩

theorem _root_.Embedding.aestronglyMeasurable_comp_iff [PseudoMetrizableSpace β]
    [PseudoMetrizableSpace γ] {g : β → γ} {f : α → β} (hg : Embedding g) :
    AEStronglyMeasurable (fun x => g (f x)) μ ↔ AEStronglyMeasurable f μ := by
  letI := pseudoMetrizableSpacePseudoMetric γ
  borelize β γ
  refine
    ⟨fun H => aestronglyMeasurable_iff_aemeasurable_separable.2 ⟨?_, ?_⟩, fun H =>
      hg.continuous.comp_aestronglyMeasurable H⟩
  · let G : β → range g := rangeFactorization g
    have hG : ClosedEmbedding G :=
      { hg.codRestrict _ _ with
        isClosed_range := by rw [surjective_onto_range.range_eq]; exact isClosed_univ }
    have : AEMeasurable (G ∘ f) μ := AEMeasurable.subtype_mk H.aemeasurable
    exact hG.measurableEmbedding.aemeasurable_comp_iff.1 this
  · rcases (aestronglyMeasurable_iff_aemeasurable_separable.1 H).2 with ⟨t, ht, h't⟩
    exact ⟨g ⁻¹' t, hg.isSeparable_preimage ht, h't⟩

/-- An almost everywhere sequential limit of almost everywhere strongly measurable functions is
almost everywhere strongly measurable. -/
theorem _root_.aestronglyMeasurable_of_tendsto_ae {ι : Type*} [PseudoMetrizableSpace β]
    (u : Filter ι) [NeBot u] [IsCountablyGenerated u] {f : ι → α → β} {g : α → β}
    (hf : ∀ i, AEStronglyMeasurable (f i) μ) (lim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) u (𝓝 (g x))) :
    AEStronglyMeasurable g μ := by
  borelize β
  refine aestronglyMeasurable_iff_aemeasurable_separable.2 ⟨?_, ?_⟩
  · exact aemeasurable_of_tendsto_metrizable_ae _ (fun n => (hf n).aemeasurable) lim
  · rcases u.exists_seq_tendsto with ⟨v, hv⟩
    have : ∀ n : ℕ, ∃ t : Set β, IsSeparable t ∧ f (v n) ⁻¹' t ∈ ae μ := fun n =>
      (aestronglyMeasurable_iff_aemeasurable_separable.1 (hf (v n))).2
    choose t t_sep ht using this
    refine ⟨closure (⋃ i, t i), .closure <| .iUnion t_sep, ?_⟩
    filter_upwards [ae_all_iff.2 ht, lim] with x hx h'x
    apply mem_closure_of_tendsto (h'x.comp hv)
    filter_upwards with n using mem_iUnion_of_mem n (hx n)

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
  refine ⟨Hg.mk g, Hg.stronglyMeasurable_mk, ?_⟩
  filter_upwards [hg, Hg.ae_eq_mk] with x hx h'x
  rwa [h'x] at hx

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
  refine
    aestronglyMeasurable_iff_aemeasurable_separable.2
      ⟨AEMeasurable.sum_measure fun i => (h i).aemeasurable, ?_⟩
  have A : ∀ i : ι, ∃ t : Set β, IsSeparable t ∧ f ⁻¹' t ∈ ae (μ i) := fun i =>
    (aestronglyMeasurable_iff_aemeasurable_separable.1 (h i)).2
  choose t t_sep ht using A
  refine ⟨⋃ i, t i, .iUnion t_sep, ?_⟩
  simp only [Measure.ae_sum_eq, mem_iUnion, eventually_iSup]
  intro i
  filter_upwards [ht i] with x hx
  exact ⟨i, hx⟩

@[simp]
theorem _root_.aestronglyMeasurable_sum_measure_iff [PseudoMetrizableSpace β]
    {_m : MeasurableSpace α} {μ : ι → Measure α} :
    AEStronglyMeasurable f (sum μ) ↔ ∀ i, AEStronglyMeasurable f (μ i) :=
  ⟨fun h _ => h.mono_measure (Measure.le_sum _ _), sum_measure⟩

@[simp]
theorem _root_.aestronglyMeasurable_add_measure_iff [PseudoMetrizableSpace β] {ν : Measure α} :
    AEStronglyMeasurable f (μ + ν) ↔ AEStronglyMeasurable f μ ∧ AEStronglyMeasurable f ν := by
  rw [← sum_cond, aestronglyMeasurable_sum_measure_iff, Bool.forall_bool, and_comm]
  rfl

@[measurability]
theorem add_measure [PseudoMetrizableSpace β] {ν : Measure α} {f : α → β}
    (hμ : AEStronglyMeasurable f μ) (hν : AEStronglyMeasurable f ν) :
    AEStronglyMeasurable f (μ + ν) :=
  aestronglyMeasurable_add_measure_iff.2 ⟨hμ, hν⟩

@[measurability]
protected theorem iUnion [PseudoMetrizableSpace β] {s : ι → Set α}
    (h : ∀ i, AEStronglyMeasurable f (μ.restrict (s i))) :
    AEStronglyMeasurable f (μ.restrict (⋃ i, s i)) :=
  (sum_measure h).mono_measure <| restrict_iUnion_le

@[simp]
theorem _root_.aestronglyMeasurable_iUnion_iff [PseudoMetrizableSpace β] {s : ι → Set α} :
    AEStronglyMeasurable f (μ.restrict (⋃ i, s i)) ↔
      ∀ i, AEStronglyMeasurable f (μ.restrict (s i)) :=
  ⟨fun h _ => h.mono_measure <| restrict_mono (subset_iUnion _ _) le_rfl,
    AEStronglyMeasurable.iUnion⟩

@[simp]
theorem _root_.aestronglyMeasurable_union_iff [PseudoMetrizableSpace β] {s t : Set α} :
    AEStronglyMeasurable f (μ.restrict (s ∪ t)) ↔
      AEStronglyMeasurable f (μ.restrict s) ∧ AEStronglyMeasurable f (μ.restrict t) := by
  simp only [union_eq_iUnion, aestronglyMeasurable_iUnion_iff, Bool.forall_bool, cond, and_comm]

theorem aestronglyMeasurable_uIoc_iff [LinearOrder α] [PseudoMetrizableSpace β] {f : α → β}
    {a b : α} :
    AEStronglyMeasurable f (μ.restrict <| uIoc a b) ↔
      AEStronglyMeasurable f (μ.restrict <| Ioc a b) ∧
        AEStronglyMeasurable f (μ.restrict <| Ioc b a) := by
  rw [uIoc_eq_union, aestronglyMeasurable_union_iff]

@[measurability]
theorem smul_measure {R : Type*} [Monoid R] [DistribMulAction R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    (h : AEStronglyMeasurable f μ) (c : R) : AEStronglyMeasurable f (c • μ) :=
  ⟨h.mk f, h.stronglyMeasurable_mk, ae_smul_measure h.ae_eq_mk c⟩

section MulAction

variable {M G G₀ : Type*}
variable [Monoid M] [MulAction M β] [ContinuousConstSMul M β]
variable [Group G] [MulAction G β] [ContinuousConstSMul G β]
variable [GroupWithZero G₀] [MulAction G₀ β] [ContinuousConstSMul G₀ β]

theorem _root_.aestronglyMeasurable_const_smul_iff (c : G) :
    AEStronglyMeasurable (fun x => c • f x) μ ↔ AEStronglyMeasurable f μ :=
  ⟨fun h => by simpa only [inv_smul_smul] using h.const_smul' c⁻¹, fun h => h.const_smul c⟩

nonrec theorem _root_.IsUnit.aestronglyMeasurable_const_smul_iff {c : M} (hc : IsUnit c) :
    AEStronglyMeasurable (fun x => c • f x) μ ↔ AEStronglyMeasurable f μ :=
  let ⟨u, hu⟩ := hc
  hu ▸ aestronglyMeasurable_const_smul_iff u

theorem _root_.aestronglyMeasurable_const_smul_iff₀ {c : G₀} (hc : c ≠ 0) :
    AEStronglyMeasurable (fun x => c • f x) μ ↔ AEStronglyMeasurable f μ :=
  (IsUnit.mk0 _ hc).aestronglyMeasurable_const_smul_iff

end MulAction

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

theorem finStronglyMeasurable_mk (hf : AEFinStronglyMeasurable f μ) :
    FinStronglyMeasurable (hf.mk f) μ :=
  hf.choose_spec.1

theorem ae_eq_mk (hf : AEFinStronglyMeasurable f μ) : f =ᵐ[μ] hf.mk f :=
  hf.choose_spec.2

@[aesop 10% apply (rule_sets := [Measurable])]
protected theorem aemeasurable {β} [Zero β] [MeasurableSpace β] [TopologicalSpace β]
    [PseudoMetrizableSpace β] [BorelSpace β] {f : α → β} (hf : AEFinStronglyMeasurable f μ) :
    AEMeasurable f μ :=
  ⟨hf.mk f, hf.finStronglyMeasurable_mk.measurable, hf.ae_eq_mk⟩

end Mk

section Arithmetic

@[aesop safe 20 (rule_sets := [Measurable])]
protected theorem mul [MonoidWithZero β] [ContinuousMul β] (hf : AEFinStronglyMeasurable f μ)
    (hg : AEFinStronglyMeasurable g μ) : AEFinStronglyMeasurable (f * g) μ :=
  ⟨hf.mk f * hg.mk g, hf.finStronglyMeasurable_mk.mul hg.finStronglyMeasurable_mk,
    hf.ae_eq_mk.mul hg.ae_eq_mk⟩

@[aesop safe 20 (rule_sets := [Measurable])]
protected theorem add [AddMonoid β] [ContinuousAdd β] (hf : AEFinStronglyMeasurable f μ)
    (hg : AEFinStronglyMeasurable g μ) : AEFinStronglyMeasurable (f + g) μ :=
  ⟨hf.mk f + hg.mk g, hf.finStronglyMeasurable_mk.add hg.finStronglyMeasurable_mk,
    hf.ae_eq_mk.add hg.ae_eq_mk⟩

@[measurability]
protected theorem neg [AddGroup β] [TopologicalAddGroup β] (hf : AEFinStronglyMeasurable f μ) :
    AEFinStronglyMeasurable (-f) μ :=
  ⟨-hf.mk f, hf.finStronglyMeasurable_mk.neg, hf.ae_eq_mk.neg⟩

@[measurability]
protected theorem sub [AddGroup β] [ContinuousSub β] (hf : AEFinStronglyMeasurable f μ)
    (hg : AEFinStronglyMeasurable g μ) : AEFinStronglyMeasurable (f - g) μ :=
  ⟨hf.mk f - hg.mk g, hf.finStronglyMeasurable_mk.sub hg.finStronglyMeasurable_mk,
    hf.ae_eq_mk.sub hg.ae_eq_mk⟩

@[measurability]
protected theorem const_smul {𝕜} [TopologicalSpace 𝕜] [AddMonoid β] [Monoid 𝕜]
    [DistribMulAction 𝕜 β] [ContinuousSMul 𝕜 β] (hf : AEFinStronglyMeasurable f μ) (c : 𝕜) :
    AEFinStronglyMeasurable (c • f) μ :=
  ⟨c • hf.mk f, hf.finStronglyMeasurable_mk.const_smul c, hf.ae_eq_mk.const_smul c⟩

end Arithmetic

section Order

variable [Zero β]

@[aesop safe 20 (rule_sets := [Measurable])]
protected theorem sup [SemilatticeSup β] [ContinuousSup β] (hf : AEFinStronglyMeasurable f μ)
    (hg : AEFinStronglyMeasurable g μ) : AEFinStronglyMeasurable (f ⊔ g) μ :=
  ⟨hf.mk f ⊔ hg.mk g, hf.finStronglyMeasurable_mk.sup hg.finStronglyMeasurable_mk,
    hf.ae_eq_mk.sup hg.ae_eq_mk⟩

@[aesop safe 20 (rule_sets := [Measurable])]
protected theorem inf [SemilatticeInf β] [ContinuousInf β] (hf : AEFinStronglyMeasurable f μ)
    (hg : AEFinStronglyMeasurable g μ) : AEFinStronglyMeasurable (f ⊓ g) μ :=
  ⟨hf.mk f ⊓ hg.mk g, hf.finStronglyMeasurable_mk.inf hg.finStronglyMeasurable_mk,
    hf.ae_eq_mk.inf hg.ae_eq_mk⟩

end Order

variable [Zero β] [T2Space β]

theorem exists_set_sigmaFinite (hf : AEFinStronglyMeasurable f μ) :
    ∃ t, MeasurableSet t ∧ f =ᵐ[μ.restrict tᶜ] 0 ∧ SigmaFinite (μ.restrict t) := by
  rcases hf with ⟨g, hg, hfg⟩
  obtain ⟨t, ht, hgt_zero, htμ⟩ := hg.exists_set_sigmaFinite
  refine ⟨t, ht, ?_, htμ⟩
  refine EventuallyEq.trans (ae_restrict_of_ae hfg) ?_
  rw [EventuallyEq, ae_restrict_iff' ht.compl]
  exact eventually_of_forall hgt_zero

/-- A measurable set `t` such that `f =ᵐ[μ.restrict tᶜ] 0` and `sigma_finite (μ.restrict t)`. -/
def sigmaFiniteSet (hf : AEFinStronglyMeasurable f μ) : Set α :=
  hf.exists_set_sigmaFinite.choose

protected theorem measurableSet (hf : AEFinStronglyMeasurable f μ) :
    MeasurableSet hf.sigmaFiniteSet :=
  hf.exists_set_sigmaFinite.choose_spec.1

theorem ae_eq_zero_compl (hf : AEFinStronglyMeasurable f μ) :
    f =ᵐ[μ.restrict hf.sigmaFiniteSetᶜ] 0 :=
  hf.exists_set_sigmaFinite.choose_spec.2.1

instance sigmaFinite_restrict (hf : AEFinStronglyMeasurable f μ) :
    SigmaFinite (μ.restrict hf.sigmaFiniteSet) :=
  hf.exists_set_sigmaFinite.choose_spec.2.2

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
    refine ⟨h_str_meas.approx, fun j x => ?_⟩
    exact ((hu_cont x).tendsto j).comp (h_str_meas.tendsto_approx j)
  let U (n : ℕ) (p : ι × α) := u (t_sf n p.fst) p.snd
  have h_tendsto : Tendsto U atTop (𝓝 fun p => u p.fst p.snd) := by
    rw [tendsto_pi_nhds]
    exact fun p => ht_sf p.fst p.snd
  refine measurable_of_tendsto_metrizable (fun n => ?_) h_tendsto
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
  refine h_meas.comp (Measurable.prod_mk ?_ measurable_snd)
  exact ((t_sf n).measurable.comp measurable_fst).subtype_mk

theorem stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable {α β ι : Type*}
    [TopologicalSpace ι] [MetrizableSpace ι] [MeasurableSpace ι] [SecondCountableTopology ι]
    [OpensMeasurableSpace ι] [TopologicalSpace β] [PseudoMetrizableSpace β] [MeasurableSpace α]
    {u : ι → α → β} (hu_cont : ∀ x, Continuous fun i => u i x) (h : ∀ i, StronglyMeasurable (u i)) :
    StronglyMeasurable (Function.uncurry u) := by
  borelize β
  obtain ⟨t_sf, ht_sf⟩ :
    ∃ t : ℕ → SimpleFunc ι ι, ∀ j x, Tendsto (fun n => u (t n j) x) atTop (𝓝 <| u j x) := by
    have h_str_meas : StronglyMeasurable (id : ι → ι) := stronglyMeasurable_id
    refine ⟨h_str_meas.approx, fun j x => ?_⟩
    exact ((hu_cont x).tendsto j).comp (h_str_meas.tendsto_approx j)
  let U (n : ℕ) (p : ι × α) := u (t_sf n p.fst) p.snd
  have h_tendsto : Tendsto U atTop (𝓝 fun p => u p.fst p.snd) := by
    rw [tendsto_pi_nhds]
    exact fun p => ht_sf p.fst p.snd
  refine stronglyMeasurable_of_tendsto _ (fun n => ?_) h_tendsto
  have h_str_meas : StronglyMeasurable fun p : (t_sf n).range × α => u (↑p.fst) p.snd := by
    refine stronglyMeasurable_iff_measurable_separable.2 ⟨?_, ?_⟩
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
  refine h_str_meas.comp_measurable (Measurable.prod_mk ?_ measurable_snd)
  exact ((t_sf n).measurable.comp measurable_fst).subtype_mk

end MeasureTheory

-- Guard against import creep
assert_not_exists InnerProductSpace
