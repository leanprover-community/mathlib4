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
of those simple functions have finite measure.

If the target space has a second countable topology, strongly measurable and measurable are
equivalent.

If the measure is sigma-finite, strongly measurable and finitely strongly measurable are equivalent.

The main property of finitely strongly measurable functions is
`FinStronglyMeasurable.exists_set_sigmaFinite`: there exists a measurable set `t` such that the
function is supported on `t` and `μ.restrict t` is sigma-finite. As a consequence, we can prove some
results for those functions as if the measure was sigma-finite.

We provide a solid API for strongly measurable functions, as a basis for the Bochner integral.

## Main definitions

* `StronglyMeasurable f`: `f : α → β` is the limit of a sequence `fs : ℕ → SimpleFunc α β`.
* `FinStronglyMeasurable f μ`: `f : α → β` is the limit of a sequence `fs : ℕ → SimpleFunc α β`
  such that for all `n ∈ ℕ`, the measure of the support of `fs n` is finite.

## References

* [Hytönen, Tuomas, Jan Van Neerven, Mark Veraar, and Lutz Weis. Analysis in Banach spaces.
  Springer, 2016.][Hytonen_VanNeerven_Veraar_Wies_2016]

-/

-- Guard against import creep
assert_not_exists InnerProductSpace

open MeasureTheory Filter TopologicalSpace Function Set MeasureTheory.Measure

open ENNReal Topology MeasureTheory NNReal

variable {α β γ ι : Type*} [Countable ι]

namespace MeasureTheory

local infixr:25 " →ₛ " => SimpleFunc

section Definitions

variable [TopologicalSpace β]

/-- A function is `StronglyMeasurable` if it is the limit of simple functions. -/
@[fun_prop]
def StronglyMeasurable [MeasurableSpace α] (f : α → β) : Prop :=
  ∃ fs : ℕ → α →ₛ β, ∀ x, Tendsto (fun n => fs n x) atTop (𝓝 (f x))

/-- The notation for StronglyMeasurable giving the measurable space instance explicitly. -/
scoped notation "StronglyMeasurable[" m "]" => @MeasureTheory.StronglyMeasurable _ _ _ m

/-- A function is `FinStronglyMeasurable` with respect to a measure if it is the limit of simple
  functions with support with finite measure. -/
def FinStronglyMeasurable [Zero β]
    {_ : MeasurableSpace α} (f : α → β) (μ : Measure α := by volume_tac) : Prop :=
  ∃ fs : ℕ → α →ₛ β, (∀ n, μ (support (fs n)) < ∞) ∧ ∀ x, Tendsto (fun n => fs n x) atTop (𝓝 (f x))

end Definitions

open MeasureTheory

/-! ## Strongly measurable functions -/

section StronglyMeasurable
variable {_ : MeasurableSpace α} {μ : Measure α} {f : α → β} {g : ℕ → α} {m : ℕ}

variable [TopologicalSpace β]

@[fun_prop]
theorem SimpleFunc.stronglyMeasurable (f : α →ₛ β) : StronglyMeasurable f :=
  ⟨fun _ => f, fun _ => tendsto_const_nhds⟩

@[simp, nontriviality]
lemma StronglyMeasurable.of_subsingleton_dom [Subsingleton α] : StronglyMeasurable f :=
  ⟨fun _ => SimpleFunc.ofFinite f, fun _ => tendsto_const_nhds⟩

@[simp, nontriviality]
lemma StronglyMeasurable.of_subsingleton_cod [Subsingleton β] : StronglyMeasurable f := by
  let f_sf : α →ₛ β := ⟨f, fun x => ?_, Set.Subsingleton.finite Set.subsingleton_of_subsingleton⟩
  · exact ⟨fun _ => f_sf, fun x => tendsto_const_nhds⟩
  · simp [Set.preimage, eq_iff_true_of_subsingleton]

@[fun_prop]
theorem stronglyMeasurable_const {b : β} : StronglyMeasurable fun _ : α => b :=
  ⟨fun _ => SimpleFunc.const α b, fun _ => tendsto_const_nhds⟩

@[to_additive]
theorem stronglyMeasurable_one [One β] : StronglyMeasurable (1 : α → β) := stronglyMeasurable_const

/-- A version of `stronglyMeasurable_const` that assumes `f x = f y` for all `x, y`.
This version works for functions between empty types. -/
theorem stronglyMeasurable_const' (hf : ∀ x y, f x = f y) : StronglyMeasurable f := by
  nontriviality α
  inhabit α
  convert stronglyMeasurable_const (β := β) using 1
  exact funext fun x => hf x default

variable [MeasurableSingletonClass α]

section aux
omit [TopologicalSpace β]

/-- Auxiliary definition for `StronglyMeasurable.of_discrete`. -/
private noncomputable def simpleFuncAux (f : α → β) (g : ℕ → α) : ℕ → SimpleFunc α β
  | 0 => .const _ (f (g 0))
  | n + 1 => .piecewise {g n} (.singleton _) (.const _ <| f (g n)) (simpleFuncAux f g n)

private lemma simpleFuncAux_eq_of_lt : ∀ n > m, simpleFuncAux f g n (g m) = f (g m)
  | _, .refl => by simp [simpleFuncAux]
  | _, Nat.le.step (m := n) hmn => by
    obtain hnm | hnm := eq_or_ne (g n) (g m) <;>
      simp [simpleFuncAux, Set.piecewise_eq_of_notMem, hnm.symm, simpleFuncAux_eq_of_lt _ hmn]

private lemma simpleFuncAux_eventuallyEq : ∀ᶠ n in atTop, simpleFuncAux f g n (g m) = f (g m) :=
  eventually_atTop.2 ⟨_, simpleFuncAux_eq_of_lt⟩

end aux

@[fun_prop]
lemma StronglyMeasurable.of_discrete [Countable α] : StronglyMeasurable f := by
  nontriviality α
  nontriviality β
  obtain ⟨g, hg⟩ := exists_surjective_nat α
  exact ⟨simpleFuncAux f g, hg.forall.2 fun m ↦
    tendsto_nhds_of_eventually_eq simpleFuncAux_eventuallyEq⟩

end StronglyMeasurable

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
        inv_mul_cancel₀ h0, one_mul, Real.norm_of_nonneg hc]
    · rwa [div_le_one (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0))]

theorem _root_.stronglyMeasurable_bot_iff [Nonempty β] [T2Space β] :
    StronglyMeasurable[⊥] f ↔ ∃ c, f = fun _ => c := by
  rcases isEmpty_or_nonempty α with hα | hα
  · simp [eq_iff_true_of_subsingleton]
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
  have hS_meas : ∀ n, MeasurableSet (S n) := measurableSet_spanningSets (μ.restrict t)
  let f_approx := hf_meas.approx
  let fs n := SimpleFunc.restrict (f_approx n) (S n ∩ t)
  have h_fs_t_compl : ∀ n, ∀ x, x ∉ t → fs n x = 0 := by
    intro n x hxt
    rw [SimpleFunc.restrict_apply _ ((hS_meas n).inter ht)]
    refine Set.indicator_of_notMem ?_ _
    simp [hxt]
  refine ⟨fs, ?_, fun x => ?_⟩
  · simp_rw [SimpleFunc.support_eq, ← Finset.mem_coe]
    classical
    refine fun n => measure_biUnion_lt_top {y ∈ (fs n).range | y ≠ 0}.finite_toSet fun y hy => ?_
    rw [SimpleFunc.restrict_preimage_singleton _ ((hS_meas n).inter ht)]
    swap
    · letI : (y : β) → Decidable (y = 0) := fun y => Classical.propDecidable _
      rw [Finset.mem_coe, Finset.mem_filter] at hy
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

@[fun_prop]
protected theorem fst {m : MeasurableSpace α} [TopologicalSpace β] [TopologicalSpace γ]
    {f : α → β × γ} (hf : StronglyMeasurable f) : StronglyMeasurable fun x ↦ (f x).1 :=
  continuous_fst.comp_stronglyMeasurable hf

@[fun_prop]
protected theorem snd {m : MeasurableSpace α} [TopologicalSpace β] [TopologicalSpace γ]
    {f : α → β × γ} (hf : StronglyMeasurable f) : StronglyMeasurable fun x ↦ (f x).2 :=
  continuous_snd.comp_stronglyMeasurable hf

@[fun_prop]
protected theorem prodMk {m : MeasurableSpace α} [TopologicalSpace β] [TopologicalSpace γ]
    {f : α → β} {g : α → γ} (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    StronglyMeasurable fun x => (f x, g x) := by
  refine ⟨fun n => SimpleFunc.pair (hf.approx n) (hg.approx n), fun x => ?_⟩
  rw [nhds_prod_eq]
  exact Tendsto.prodMk (hf.tendsto_approx x) (hg.tendsto_approx x)

@[fun_prop]
theorem comp_measurable [TopologicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ}
    {f : α → β} {g : γ → α} (hf : StronglyMeasurable f) (hg : Measurable g) :
    StronglyMeasurable (f ∘ g) :=
  ⟨fun n => SimpleFunc.comp (hf.approx n) g hg, fun x => hf.tendsto_approx (g x)⟩

theorem of_uncurry_left [TopologicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ}
    {f : α → γ → β} (hf : StronglyMeasurable (uncurry f)) {x : α} : StronglyMeasurable (f x) :=
  hf.comp_measurable measurable_prodMk_left

theorem of_uncurry_right [TopologicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ}
    {f : α → γ → β} (hf : StronglyMeasurable (uncurry f)) {y : γ} :
    StronglyMeasurable fun x => f x y :=
  hf.comp_measurable measurable_prodMk_right

protected theorem prod_swap {_ : MeasurableSpace α} {_ : MeasurableSpace β} [TopologicalSpace γ]
    {f : β × α → γ} (hf : StronglyMeasurable f) :
    StronglyMeasurable (fun z : α × β => f z.swap) :=
  hf.comp_measurable measurable_swap

protected theorem comp_fst {_ : MeasurableSpace α} [mβ : MeasurableSpace β] [TopologicalSpace γ]
    {f : α → γ} (hf : StronglyMeasurable f) :
    StronglyMeasurable (fun z : α × β => f z.1) :=
  hf.comp_measurable measurable_fst

protected theorem comp_snd [mα : MeasurableSpace α] {_ : MeasurableSpace β} [TopologicalSpace γ]
    {f : β → γ} (hf : StronglyMeasurable f) :
    StronglyMeasurable (fun z : α × β => f z.2) :=
  hf.comp_measurable measurable_snd

section Arithmetic

variable {mα : MeasurableSpace α} [TopologicalSpace β]

@[to_additive (attr := fun_prop, aesop safe 20 apply (rule_sets := [Measurable]))]
protected theorem mul [Mul β] [ContinuousMul β] (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) : StronglyMeasurable (f * g) :=
  ⟨fun n => hf.approx n * hg.approx n, fun x => (hf.tendsto_approx x).mul (hg.tendsto_approx x)⟩

@[to_additive (attr := fun_prop, measurability)]
theorem mul_const [Mul β] [ContinuousMul β] (hf : StronglyMeasurable f) (c : β) :
    StronglyMeasurable fun x => f x * c :=
  hf.mul stronglyMeasurable_const

@[to_additive (attr := fun_prop, measurability)]
theorem const_mul [Mul β] [ContinuousMul β] (hf : StronglyMeasurable f) (c : β) :
    StronglyMeasurable fun x => c * f x :=
  stronglyMeasurable_const.mul hf

@[to_additive (attr := fun_prop, aesop safe 20 apply (rule_sets := [Measurable])) const_nsmul]
protected theorem pow [Monoid β] [ContinuousMul β] (hf : StronglyMeasurable f) (n : ℕ) :
    StronglyMeasurable (f ^ n) :=
  ⟨fun k => hf.approx k ^ n, fun x => (hf.tendsto_approx x).pow n⟩

@[to_additive (attr := fun_prop, measurability)]
protected theorem inv [Inv β] [ContinuousInv β] (hf : StronglyMeasurable f) :
    StronglyMeasurable f⁻¹ :=
  ⟨fun n => (hf.approx n)⁻¹, fun x => (hf.tendsto_approx x).inv⟩

@[to_additive (attr := fun_prop, aesop safe 20 apply (rule_sets := [Measurable]))]
protected theorem div [Div β] [ContinuousDiv β] (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) : StronglyMeasurable (f / g) :=
  ⟨fun n => hf.approx n / hg.approx n, fun x => (hf.tendsto_approx x).div' (hg.tendsto_approx x)⟩

@[to_additive]
theorem mul_iff_right [CommGroup β] [IsTopologicalGroup β] (hf : StronglyMeasurable f) :
    StronglyMeasurable (f * g) ↔ StronglyMeasurable g :=
  ⟨fun h ↦ show g = f * g * f⁻¹ by simp only [mul_inv_cancel_comm] ▸ h.mul hf.inv,
    fun h ↦ hf.mul h⟩

@[to_additive]
theorem mul_iff_left [CommGroup β] [IsTopologicalGroup β] (hf : StronglyMeasurable f) :
    StronglyMeasurable (g * f) ↔ StronglyMeasurable g :=
  mul_comm g f ▸ mul_iff_right hf

@[to_additive (attr := fun_prop, aesop safe 20 apply (rule_sets := [Measurable]))]
protected theorem smul {𝕜} [TopologicalSpace 𝕜] [SMul 𝕜 β] [ContinuousSMul 𝕜 β] {f : α → 𝕜}
    {g : α → β} (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    StronglyMeasurable fun x => f x • g x :=
  continuous_smul.comp_stronglyMeasurable (hf.prodMk hg)

@[to_additive (attr := fun_prop, measurability)]
protected theorem const_smul {𝕜} [SMul 𝕜 β] [ContinuousConstSMul 𝕜 β] (hf : StronglyMeasurable f)
    (c : 𝕜) : StronglyMeasurable (c • f) :=
  ⟨fun n => c • hf.approx n, fun x => (hf.tendsto_approx x).const_smul c⟩

@[to_additive (attr := fun_prop, measurability)]
protected theorem const_smul' {𝕜} [SMul 𝕜 β] [ContinuousConstSMul 𝕜 β] (hf : StronglyMeasurable f)
    (c : 𝕜) : StronglyMeasurable fun x => c • f x :=
  hf.const_smul c

@[to_additive (attr := fun_prop, measurability)]
protected theorem smul_const {𝕜} [TopologicalSpace 𝕜] [SMul 𝕜 β] [ContinuousSMul 𝕜 β] {f : α → 𝕜}
    (hf : StronglyMeasurable f) (c : β) : StronglyMeasurable fun x => f x • c :=
  continuous_smul.comp_stronglyMeasurable (hf.prodMk stronglyMeasurable_const)

/-- Pointwise star on functions induced from continuous star preserves strong measurability. -/
@[measurability]
protected theorem star {R : Type*} [MeasurableSpace α] [Star R] [TopologicalSpace R]
    [ContinuousStar R] (f : α → R) (hf : StronglyMeasurable f) : StronglyMeasurable (star f) :=
  ⟨fun n => star (hf.approx n), fun x => (hf.tendsto_approx x).star⟩

/-- In a normed vector space, the addition of a measurable function and a strongly measurable
function is measurable. Note that this is not true without further second-countability assumptions
for the addition of two measurable functions. -/
theorem _root_.Measurable.add_stronglyMeasurable
    {α E : Type*} {_ : MeasurableSpace α} [AddCancelMonoid E] [TopologicalSpace E]
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
    {α E : Type*} {_ : MeasurableSpace α} [AddGroup E] [TopologicalSpace E]
    [MeasurableSpace E] [BorelSpace E] [ContinuousAdd E] [ContinuousNeg E] [PseudoMetrizableSpace E]
    {g f : α → E} (hg : Measurable g) (hf : StronglyMeasurable f) :
    Measurable (g - f) := by
  rw [sub_eq_add_neg]
  exact hg.add_stronglyMeasurable hf.neg

/-- In a normed vector space, the addition of a strongly measurable function and a measurable
function is measurable. Note that this is not true without further second-countability assumptions
for the addition of two measurable functions. -/
theorem _root_.Measurable.stronglyMeasurable_add
    {α E : Type*} {_ : MeasurableSpace α} [AddCancelMonoid E] [TopologicalSpace E]
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

@[fun_prop, aesop safe 20 (rule_sets := [Measurable])]
protected theorem sup [Max β] [ContinuousSup β] (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) : StronglyMeasurable (f ⊔ g) :=
  ⟨fun n => hf.approx n ⊔ hg.approx n, fun x =>
    (hf.tendsto_approx x).sup_nhds (hg.tendsto_approx x)⟩

@[fun_prop, aesop safe 20 (rule_sets := [Measurable])]
protected theorem inf [Min β] [ContinuousInf β] (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) : StronglyMeasurable (f ⊓ g) :=
  ⟨fun n => hf.approx n ⊓ hg.approx n, fun x =>
    (hf.tendsto_approx x).inf_nhds (hg.tendsto_approx x)⟩

end Order

/-!
### Big operators: `∏` and `∑`
-/


section Monoid

variable {M : Type*} [Monoid M] [TopologicalSpace M] [ContinuousMul M] {m : MeasurableSpace α}

@[to_additive (attr := fun_prop, measurability)]
theorem _root_.List.stronglyMeasurable_prod (l : List (α → M))
    (hl : ∀ f ∈ l, StronglyMeasurable f) : StronglyMeasurable l.prod := by
  induction l with
  | nil => exact stronglyMeasurable_one
  | cons f l ihl =>
    rw [List.forall_mem_cons] at hl
    rw [List.prod_cons]
    exact hl.1.mul (ihl hl.2)

@[deprecated (since := "2025-05-30")]
alias _root_.List.stronglyMeasurable_sum' := List.stronglyMeasurable_sum
@[to_additive existing, deprecated (since := "2025-05-30")]
alias _root_.List.stronglyMeasurable_prod' := List.stronglyMeasurable_prod

@[to_additive (attr := fun_prop, measurability)]
theorem _root_.List.stronglyMeasurable_fun_prod (l : List (α → M))
    (hl : ∀ f ∈ l, StronglyMeasurable f) :
    StronglyMeasurable fun x => (l.map fun f : α → M => f x).prod := by
  simpa only [← Pi.list_prod_apply] using l.stronglyMeasurable_prod hl

end Monoid

section CommMonoid

variable {M : Type*} [CommMonoid M] [TopologicalSpace M] [ContinuousMul M] {m : MeasurableSpace α}


@[to_additive (attr := fun_prop, measurability)]
theorem _root_.Multiset.stronglyMeasurable_prod (l : Multiset (α → M))
    (hl : ∀ f ∈ l, StronglyMeasurable f) : StronglyMeasurable l.prod := by
  rcases l with ⟨l⟩
  simpa using l.stronglyMeasurable_prod (by simpa using hl)

@[deprecated (since := "2025-05-30")]
alias _root_.Multiset.stronglyMeasurable_sum' := Multiset.stronglyMeasurable_sum
@[to_additive existing, deprecated (since := "2025-05-30")]
alias _root_.Multiset.stronglyMeasurable_prod' := Multiset.stronglyMeasurable_prod

@[to_additive (attr := fun_prop, measurability)]
theorem _root_.Multiset.stronglyMeasurable_fun_prod (s : Multiset (α → M))
    (hs : ∀ f ∈ s, StronglyMeasurable f) :
    StronglyMeasurable fun x => (s.map fun f : α → M => f x).prod := by
  simpa only [← Pi.multiset_prod_apply] using s.stronglyMeasurable_prod hs

@[to_additive (attr := measurability, fun_prop)]
theorem _root_.Finset.stronglyMeasurable_prod {ι : Type*} {f : ι → α → M} (s : Finset ι)
    (hf : ∀ i ∈ s, StronglyMeasurable (f i)) : StronglyMeasurable (∏ i ∈ s, f i) :=
  Finset.prod_induction _ _ (fun _a _b ha hb => ha.mul hb) (@stronglyMeasurable_one α M _ _ _) hf

@[deprecated (since := "2025-05-30")]
alias _root_.Finset.stronglyMeasurable_sum' := Finset.stronglyMeasurable_sum
@[to_additive existing, deprecated (since := "2025-05-30")]
alias _root_.Finset.stronglyMeasurable_prod' := Finset.stronglyMeasurable_prod

@[to_additive (attr := measurability, fun_prop)]
theorem _root_.Finset.stronglyMeasurable_fun_prod {ι : Type*} {f : ι → α → M} (s : Finset ι)
    (hf : ∀ i ∈ s, StronglyMeasurable (f i)) : StronglyMeasurable fun a => ∏ i ∈ s, f i a := by
  simpa only [← Finset.prod_apply] using s.stronglyMeasurable_prod hf

variable {n : MeasurableSpace β} in
/-- Compositional version of `Finset.stronglyMeasurable_prod` for use by `fun_prop`. -/
@[to_additive (attr := measurability, fun_prop)
/-- Compositional version of `Finset.stronglyMeasurable_sum` for use by `fun_prop`. -/]
lemma Finset.stronglyMeasurable_prod_apply {ι : Type*} {f : ι → α → β → M} {g : α → β}
    {s : Finset ι} (hf : ∀ i ∈ s, StronglyMeasurable ↿(f i)) (hg : Measurable g) :
    StronglyMeasurable fun a ↦ (∏ i ∈ s, f i a) (g a) := by
  simp only [Finset.prod_apply]; fun_prop (discharger := assumption)

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
    SimpleFunc.tendsto_approxOn hf (Set.mem_univ _) (by simp)⟩

/-- In a space with second countable topology, strongly measurable and measurable are equivalent. -/
theorem _root_.stronglyMeasurable_iff_measurable [TopologicalSpace β] [MetrizableSpace β]
    [BorelSpace β] [SecondCountableTopology β] : StronglyMeasurable f ↔ Measurable f :=
  ⟨fun h => h.measurable, fun h => Measurable.stronglyMeasurable h⟩

@[fun_prop, measurability]
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
    (hg : IsEmbedding g) : (StronglyMeasurable fun x => g (f x)) ↔ StronglyMeasurable f := by
  letI := pseudoMetrizableSpacePseudoMetric γ
  borelize β γ
  refine
    ⟨fun H => stronglyMeasurable_iff_measurable_separable.2 ⟨?_, ?_⟩, fun H =>
      hg.continuous.comp_stronglyMeasurable H⟩
  · let G : β → range g := rangeFactorization g
    have hG : IsClosedEmbedding G :=
      { hg.codRestrict _ _ with
        isClosed_range := by
          rw [rangeFactorization_surjective.range_eq]
          exact isClosed_univ }
    have : Measurable (G ∘ f) := Measurable.subtype_mk H.measurable
    exact hG.measurableEmbedding.measurable_comp_iff.1 this
  · have : IsSeparable (g ⁻¹' range (g ∘ f)) := hg.isSeparable_preimage H.isSeparable_range
    rwa [range_comp, hg.injective.preimage_image] at this

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
  · simpa [@Set.piecewise_eq_of_notMem _ _ _ _ _ (fun _ => Classical.propDecidable _) _ hx,
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
    simp
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

/-- To prove that a property holds for any strongly measurable function, it is enough to show
that it holds for constant indicator functions of measurable sets and that it is closed under
addition and pointwise limit.

To use in an induction proof, the syntax is
`induction f, hf using StronglyMeasurable.induction with`. -/
theorem induction [MeasurableSpace α] [AddZeroClass β] [TopologicalSpace β]
    {P : (f : α → β) → StronglyMeasurable f → Prop}
    (ind : ∀ c ⦃s : Set α⦄ (hs : MeasurableSet s),
      P (s.indicator fun _ ↦ c) (stronglyMeasurable_const.indicator hs))
    (add : ∀ ⦃f g : α → β⦄ (hf : StronglyMeasurable f) (hg : StronglyMeasurable g)
      (hfg : StronglyMeasurable (f + g)), Disjoint f.support g.support →
      P f hf → P g hg → P (f + g) hfg)
    (lim : ∀ ⦃f : ℕ → α → β⦄ ⦃g : α → β⦄ (hf : ∀ n, StronglyMeasurable (f n))
      (hg : StronglyMeasurable g), (∀ n, P (f n) (hf n)) →
      (∀ x, Tendsto (f · x) atTop (𝓝 (g x))) → P g hg)
    (f : α → β) (hf : StronglyMeasurable f) : P f hf := by
  let s := hf.approx
  refine lim (fun n ↦ (s n).stronglyMeasurable) hf (fun n ↦ ?_) hf.tendsto_approx
  change P (s n) (s n).stronglyMeasurable
  induction s n using SimpleFunc.induction with
  | const c hs => exact ind c hs
  | @add f g h_supp hf hg =>
    exact add f.stronglyMeasurable g.stronglyMeasurable (f + g).stronglyMeasurable h_supp hf hg

open scoped Classical in
/-- To prove that a property holds for any strongly measurable function, it is enough to show
that it holds for constant functions and that it is closed under piecewise combination of functions
and pointwise limits.

To use in an induction proof, the syntax is
`induction f, hf using StronglyMeasurable.induction' with`. -/
theorem induction' [MeasurableSpace α] [Nonempty β] [TopologicalSpace β]
    {P : (f : α → β) → StronglyMeasurable f → Prop}
    (const : ∀ (c), P (fun _ ↦ c) stronglyMeasurable_const)
    (pcw : ∀ ⦃f g : α → β⦄ {s} (hf : StronglyMeasurable f) (hg : StronglyMeasurable g)
      (hs : MeasurableSet s), P f hf → P g hg → P (s.piecewise f g) (hf.piecewise hs hg))
    (lim : ∀ ⦃f : ℕ → α → β⦄ ⦃g : α → β⦄ (hf : ∀ n, StronglyMeasurable (f n))
      (hg : StronglyMeasurable g), (∀ n, P (f n) (hf n)) →
      (∀ x, Tendsto (f · x) atTop (𝓝 (g x))) → P g hg)
    (f : α → β) (hf : StronglyMeasurable f) : P f hf := by
  let s := hf.approx
  refine lim (fun n ↦ (s n).stronglyMeasurable) hf (fun n ↦ ?_) hf.tendsto_approx
  change P (s n) (s n).stronglyMeasurable
  induction s n with
  | const c => exact const c
  | @pcw f g s hs Pf Pg =>
    simp_rw [SimpleFunc.coe_piecewise]
    exact pcw f.stronglyMeasurable g.stronglyMeasurable hs Pf Pg

@[fun_prop, aesop safe 20 apply (rule_sets := [Measurable])]
protected theorem dist {_ : MeasurableSpace α} {β : Type*} [PseudoMetricSpace β] {f g : α → β}
    (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    StronglyMeasurable fun x => dist (f x) (g x) :=
  continuous_dist.comp_stronglyMeasurable (hf.prodMk hg)

@[fun_prop, aesop safe 20 apply (rule_sets := [Measurable])]
protected theorem edist {_ : MeasurableSpace α} {β : Type*} [PseudoEMetricSpace β] {f g : α → β}
    (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    StronglyMeasurable fun x => edist (f x) (g x) :=
  continuous_edist.comp_stronglyMeasurable (hf.prodMk hg)

@[fun_prop, measurability]
protected theorem norm {_ : MeasurableSpace α} {β : Type*} [SeminormedAddCommGroup β] {f : α → β}
    (hf : StronglyMeasurable f) : StronglyMeasurable fun x => ‖f x‖ :=
  continuous_norm.comp_stronglyMeasurable hf

@[fun_prop, measurability]
protected theorem nnnorm {_ : MeasurableSpace α} {β : Type*} [SeminormedAddCommGroup β] {f : α → β}
    (hf : StronglyMeasurable f) : StronglyMeasurable fun x => ‖f x‖₊ :=
  continuous_nnnorm.comp_stronglyMeasurable hf

/-- The `enorm` of a strongly measurable function is measurable.

Unlike `StrongMeasurable.norm` and `StronglyMeasurable.nnnorm`, this lemma proves measurability,
**not** strong measurability. This is an intentional decision: for functions taking values in
ℝ≥0∞, measurability is much more useful than strong measurability. -/
@[fun_prop, measurability]
protected theorem enorm {_ : MeasurableSpace α} {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε]
    {f : α → ε} (hf : StronglyMeasurable f) : Measurable (‖f ·‖ₑ) :=
  (continuous_enorm.comp_stronglyMeasurable hf).measurable

@[fun_prop, measurability]
protected theorem real_toNNReal {_ : MeasurableSpace α} {f : α → ℝ} (hf : StronglyMeasurable f) :
    StronglyMeasurable fun x => (f x).toNNReal :=
  continuous_real_toNNReal.comp_stronglyMeasurable hf

section PseudoMetrizableSpace
variable {E : Type*} {m m₀ : MeasurableSpace α} {μ : Measure[m₀] α} {f g : α → E}
  [TopologicalSpace E] [Preorder E] [OrderClosedTopology E] [PseudoMetrizableSpace E]

lemma measurableSet_le (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g) :
    MeasurableSet[m] {a | f a ≤ g a} := by
  borelize (E × E)
  exact (hf.prodMk hg).measurable isClosed_le_prod.measurableSet

lemma measurableSet_lt (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g) :
    MeasurableSet[m] {a | f a < g a} := by
  simpa only [lt_iff_le_not_ge] using (hf.measurableSet_le hg).inter (hg.measurableSet_le hf).compl

lemma ae_le_trim_of_stronglyMeasurable (hm : m ≤ m₀) (hf : StronglyMeasurable[m] f)
    (hg : StronglyMeasurable[m] g) (hfg : f ≤ᵐ[μ] g) : f ≤ᵐ[μ.trim hm] g := by
  rwa [EventuallyLE, ae_iff, trim_measurableSet_eq hm]
  exact (hf.measurableSet_le hg).compl

lemma ae_le_trim_iff (hm : m ≤ m₀) (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g) :
    f ≤ᵐ[μ.trim hm] g ↔ f ≤ᵐ[μ] g :=
  ⟨ae_le_of_ae_le_trim, ae_le_trim_of_stronglyMeasurable hm hf hg⟩

end PseudoMetrizableSpace

section MetrizableSpace
variable {E : Type*} {m m₀ : MeasurableSpace α} {μ : Measure[m₀] α} {f g : α → E}
  [TopologicalSpace E] [MetrizableSpace E]

lemma measurableSet_eq_fun (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g) :
    MeasurableSet[m] {a | f a = g a} := by
  borelize (E × E)
  exact (hf.prodMk hg).measurable isClosed_diagonal.measurableSet

lemma ae_eq_trim_of_stronglyMeasurable (hm : m ≤ m₀) (hf : StronglyMeasurable[m] f)
    (hg : StronglyMeasurable[m] g) (hfg : f =ᵐ[μ] g) : f =ᵐ[μ.trim hm] g := by
  rwa [EventuallyEq, ae_iff, trim_measurableSet_eq hm]
  exact (hf.measurableSet_eq_fun hg).compl

lemma ae_eq_trim_iff (hm : m ≤ m₀) (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g) :
    f =ᵐ[μ.trim hm] g ↔ f =ᵐ[μ] g :=
  ⟨ae_eq_of_ae_eq_trim, ae_eq_trim_of_stronglyMeasurable hm hf hg⟩

end MetrizableSpace

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
    rw [SimpleFunc.coe_restrict _ hs, Set.indicator_of_notMem hx]
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
            mem_empty_iff_false, iff_false, not_and, not_notMem]
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
    simp only [Pi.zero_apply, SimpleFunc.coe_zero, support_zero, measure_empty,
      zero_lt_top, forall_const],
    fun _ => tendsto_const_nhds⟩

namespace FinStronglyMeasurable

variable {m0 : MeasurableSpace α} {μ : Measure α} {f g : α → β}

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
protected theorem mul [MulZeroClass β] [ContinuousMul β] (hf : FinStronglyMeasurable f μ)
    (hg : FinStronglyMeasurable g μ) : FinStronglyMeasurable (f * g) μ := by
  refine
    ⟨fun n => hf.approx n * hg.approx n, ?_, fun x =>
      (hf.tendsto_approx x).mul (hg.tendsto_approx x)⟩
  intro n
  exact (measure_mono (support_mul_subset_left _ _)).trans_lt (hf.fin_support_approx n)

@[aesop safe 20 (rule_sets := [Measurable])]
protected theorem add [AddZeroClass β] [ContinuousAdd β] (hf : FinStronglyMeasurable f μ)
    (hg : FinStronglyMeasurable g μ) : FinStronglyMeasurable (f + g) μ :=
  ⟨fun n => hf.approx n + hg.approx n, fun n =>
    (measure_mono (Function.support_add _ _)).trans_lt
      ((measure_union_le _ _).trans_lt
        (ENNReal.add_lt_top.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩)),
    fun x => (hf.tendsto_approx x).add (hg.tendsto_approx x)⟩

@[measurability]
protected theorem neg [SubtractionMonoid β] [ContinuousNeg β] (hf : FinStronglyMeasurable f μ) :
    FinStronglyMeasurable (-f) μ := by
  refine ⟨fun n ↦ -hf.approx n, fun n ↦ ?_, fun x ↦ (hf.tendsto_approx x).neg⟩
  suffices μ (Function.support fun x ↦ -(hf.approx n) x) < ∞ by convert this
  rw [Function.support_fun_neg (hf.approx n)]
  exact hf.fin_support_approx n

@[measurability]
protected theorem sub [SubtractionMonoid β] [ContinuousSub β] (hf : FinStronglyMeasurable f μ)
    (hg : FinStronglyMeasurable g μ) : FinStronglyMeasurable (f - g) μ :=
  ⟨fun n => hf.approx n - hg.approx n, fun n =>
    (measure_mono (Function.support_sub _ _)).trans_lt
      ((measure_union_le _ _).trans_lt
        (ENNReal.add_lt_top.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩)),
    fun x => (hf.tendsto_approx x).sub (hg.tendsto_approx x)⟩

@[measurability]
protected theorem const_smul {𝕜} [TopologicalSpace 𝕜] [Zero β]
    [SMulZeroClass 𝕜 β] [ContinuousSMul 𝕜 β] (hf : FinStronglyMeasurable f μ) (c : 𝕜) :
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

section SecondCountableTopology

variable {G : Type*} [SeminormedAddCommGroup G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] {f : α → G}

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
    exact measurable_from_prod_countable_left fun j => h j
  have :
    (fun p : ι × α => u (t_sf n p.fst) p.snd) =
      (fun p : ↥(t_sf n).range × α => u p.fst p.snd) ∘ fun p : ι × α =>
        (⟨t_sf n p.fst, SimpleFunc.mem_range_self _ _⟩, p.snd) :=
    rfl
  simp_rw [U, this]
  refine h_meas.comp (Measurable.prodMk ?_ measurable_snd)
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
      exact measurable_from_prod_countable_left fun j => (h j).measurable
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
  refine h_str_meas.comp_measurable (Measurable.prodMk ?_ measurable_snd)
  exact ((t_sf n).measurable.comp measurable_fst).subtype_mk

end MeasureTheory
