/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov

! This file was ported from Lean 3 source module measure_theory.integral.average
! leanprover-community/mathlib commit f2ce6086713c78a7f880485f7917ea547a215982
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.MeasureTheory.Integral.SetIntegral

/-!
# Integral average of a function

In this file we define `MeasureTheory.average μ f` (notation: `⨍ x, f x ∂μ`) to be the average
value of `f` with respect to measure `μ`. It is defined as `∫ x, f x ∂((μ univ)⁻¹ • μ)`, so it
is equal to zero if `f` is not integrable or if `μ` is an infinite measure. If `μ` is a probability
measure, then the average of any function is equal to its integral.

For the average on a set, we use `⨍ x in s, f x ∂μ` (notation for `⨍ x, f x ∂(μ.restrict s)`). For
average w.r.t. the volume, one can omit `∂volume`.

## Implementation notes

The average is defined as an integral over `(μ univ)⁻¹ • μ` so that all theorems about Bochner
integrals work for the average without modifications. For theorems that require integrability of a
function, we provide a convenience lemma `MeasureTheory.Integrable.to_average`.

## Tags

integral, center mass, average value
-/


open MeasureTheory MeasureTheory.Measure Metric Set Filter TopologicalSpace Function

open scoped Topology BigOperators ENNReal Convex

variable {α E F : Type _} {m0 : MeasurableSpace α} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {μ : Measure α}
  {s : Set E}

/-!
### Average value of a function w.r.t. a measure

The average value of a function `f` w.r.t. a measure `μ` (notation: `⨍ x, f x ∂μ`) is defined as
`(μ univ).toReal⁻¹ • ∫ x, f x ∂μ`, so it is equal to zero if `f` is not integrable or if `μ` is an
infinite measure. If `μ` is a probability measure, then the average of any function is equal to its
integral.

-/


namespace MeasureTheory

variable (μ)

/-- Average value of a function `f` w.r.t. a measure `μ`, notation: `⨍ x, f x ∂μ`. It is defined as
`(μ univ).toReal⁻¹ • ∫ x, f x ∂μ`, so it is equal to zero if `f` is not integrable or if `μ` is an
infinite measure. If `μ` is a probability measure, then the average of any function is equal to its
integral.

For the average on a set, use `⨍ x in s, f x ∂μ` (defined as `⨍ x, f x ∂(μ.restrict s)`). For
average w.r.t. the volume, one can omit `∂volume`. -/
noncomputable def average (f : α → E) :=
  ∫ x, f x ∂(μ univ)⁻¹ • μ
#align measure_theory.average MeasureTheory.average

@[inherit_doc average]
notation3 "⨍ "(...)", "r:60:(scoped f => f)" ∂"μ:70 => average μ r

@[inherit_doc average]
notation3 "⨍ "(...)", "r:60:(scoped f => average volume f) => r

@[inherit_doc average]
notation3 "⨍ "(...)" in "s", "r:60:(scoped f => f)" ∂"μ:70 => average (Measure.restrict μ s) r

@[inherit_doc average]
notation3 "⨍ "(...)" in "s", "r:60:(scoped f => average (Measure.restrict volume s) f) => r

@[simp]
theorem average_zero : ⨍ _, (0 : E) ∂μ = 0 := by rw [average, integral_zero]
#align measure_theory.average_zero MeasureTheory.average_zero

@[simp]
theorem average_zero_measure (f : α → E) : (⨍ x, f x ∂(0 : Measure α)) = 0 := by
  rw [average, smul_zero, integral_zero_measure]
#align measure_theory.average_zero_measure MeasureTheory.average_zero_measure

@[simp]
theorem average_neg (f : α → E) : ⨍ x, -f x ∂μ = -⨍ x, f x ∂μ :=
  integral_neg f
#align measure_theory.average_neg MeasureTheory.average_neg

theorem average_eq' (f : α → E) : ⨍ x, f x ∂μ = ∫ x, f x ∂(μ univ)⁻¹ • μ :=
  rfl
#align measure_theory.average_eq' MeasureTheory.average_eq'

theorem average_eq (f : α → E) : ⨍ x, f x ∂μ = (μ univ).toReal⁻¹ • ∫ x, f x ∂μ := by
  rw [average_eq', integral_smul_measure, ENNReal.toReal_inv]
#align measure_theory.average_eq MeasureTheory.average_eq

theorem average_eq_integral [IsProbabilityMeasure μ] (f : α → E) : ⨍ x, f x ∂μ = ∫ x, f x ∂μ := by
  rw [average, measure_univ, inv_one, one_smul]
#align measure_theory.average_eq_integral MeasureTheory.average_eq_integral

@[simp]
theorem measure_smul_average [IsFiniteMeasure μ] (f : α → E) :
    ((μ univ).toReal • ⨍ x, f x ∂μ) = ∫ x, f x ∂μ := by
  cases' eq_or_ne μ 0 with hμ hμ
  · rw [hμ, integral_zero_measure, average_zero_measure, smul_zero]
  · rw [average_eq, smul_inv_smul₀]
    refine' (ENNReal.toReal_pos _ <| measure_ne_top _ _).ne'
    rwa [Ne.def, measure_univ_eq_zero]
#align measure_theory.measure_smul_average MeasureTheory.measure_smul_average

theorem set_average_eq (f : α → E) (s : Set α) :
    ⨍ x in s, f x ∂μ = (μ s).toReal⁻¹ • ∫ x in s, f x ∂μ := by
  rw [average_eq, restrict_apply_univ]
#align measure_theory.set_average_eq MeasureTheory.set_average_eq

theorem set_average_eq' (f : α → E) (s : Set α) :
    ⨍ x in s, f x ∂μ = ∫ x, f x ∂(μ s)⁻¹ • μ.restrict s := by
  simp only [average_eq', restrict_apply_univ]
#align measure_theory.set_average_eq' MeasureTheory.set_average_eq'

variable {μ}

theorem average_congr {f g : α → E} (h : f =ᵐ[μ] g) : ⨍ x, f x ∂μ = ⨍ x, g x ∂μ := by
  simp only [average_eq, integral_congr_ae h]
#align measure_theory.average_congr MeasureTheory.average_congr

theorem average_add_measure [IsFiniteMeasure μ] {ν : Measure α} [IsFiniteMeasure ν] {f : α → E}
    (hμ : Integrable f μ) (hν : Integrable f ν) :
    ⨍ x, f x ∂(μ + ν) =
      (((μ univ).toReal / ((μ univ).toReal + (ν univ).toReal)) • ⨍ x, f x ∂μ) +
        ((ν univ).toReal / ((μ univ).toReal + (ν univ).toReal)) • ⨍ x, f x ∂ν := by
  simp only [div_eq_inv_mul, mul_smul, measure_smul_average, ← smul_add, ←
    integral_add_measure hμ hν, ← ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top ν _)]
  rw [average_eq, Measure.add_apply]
#align measure_theory.average_add_measure MeasureTheory.average_add_measure

theorem average_pair {f : α → E} {g : α → F} (hfi : Integrable f μ) (hgi : Integrable g μ) :
    ⨍ x, (f x, g x) ∂μ = (⨍ x, f x ∂μ, ⨍ x, g x ∂μ) :=
  integral_pair hfi.to_average hgi.to_average
#align measure_theory.average_pair MeasureTheory.average_pair

theorem measure_smul_set_average (f : α → E) {s : Set α} (h : μ s ≠ ∞) :
    ((μ s).toReal • ⨍ x in s, f x ∂μ) = ∫ x in s, f x ∂μ := by
  haveI := Fact.mk h.lt_top
  rw [← measure_smul_average, restrict_apply_univ]
#align measure_theory.measure_smul_set_average MeasureTheory.measure_smul_set_average

theorem average_union {f : α → E} {s t : Set α} (hd : AEDisjoint μ s t) (ht : NullMeasurableSet t μ)
    (hsμ : μ s ≠ ∞) (htμ : μ t ≠ ∞) (hfs : IntegrableOn f s μ) (hft : IntegrableOn f t μ) :
    ⨍ x in s ∪ t, f x ∂μ =
      (((μ s).toReal / ((μ s).toReal + (μ t).toReal)) • ⨍ x in s, f x ∂μ) +
        ((μ t).toReal / ((μ s).toReal + (μ t).toReal)) • ⨍ x in t, f x ∂μ := by
  haveI := Fact.mk hsμ.lt_top; haveI := Fact.mk htμ.lt_top
  rw [restrict_union₀ hd ht, average_add_measure hfs hft, restrict_apply_univ, restrict_apply_univ]
#align measure_theory.average_union MeasureTheory.average_union

theorem average_union_mem_openSegment {f : α → E} {s t : Set α} (hd : AEDisjoint μ s t)
    (ht : NullMeasurableSet t μ) (hs₀ : μ s ≠ 0) (ht₀ : μ t ≠ 0) (hsμ : μ s ≠ ∞) (htμ : μ t ≠ ∞)
    (hfs : IntegrableOn f s μ) (hft : IntegrableOn f t μ) :
    ⨍ x in s ∪ t, f x ∂μ ∈ openSegment ℝ (⨍ x in s, f x ∂μ) (⨍ x in t, f x ∂μ) := by
  replace hs₀ : 0 < (μ s).toReal; exact ENNReal.toReal_pos hs₀ hsμ
  replace ht₀ : 0 < (μ t).toReal; exact ENNReal.toReal_pos ht₀ htμ
  refine' mem_openSegment_iff_div.mpr
    ⟨(μ s).toReal, (μ t).toReal, hs₀, ht₀, (average_union hd ht hsμ htμ hfs hft).symm⟩
#align measure_theory.average_union_mem_open_segment MeasureTheory.average_union_mem_openSegment

theorem average_union_mem_segment {f : α → E} {s t : Set α} (hd : AEDisjoint μ s t)
    (ht : NullMeasurableSet t μ) (hsμ : μ s ≠ ∞) (htμ : μ t ≠ ∞) (hfs : IntegrableOn f s μ)
    (hft : IntegrableOn f t μ) :
    ⨍ x in s ∪ t, f x ∂μ ∈ [⨍ x in s, f x ∂μ -[ℝ] ⨍ x in t, f x ∂μ] := by
  by_cases hse : μ s = 0
  · rw [← ae_eq_empty] at hse
    rw [restrict_congr_set (hse.union EventuallyEq.rfl), empty_union]
    exact right_mem_segment _ _ _
  · refine'
      mem_segment_iff_div.mpr
        ⟨(μ s).toReal, (μ t).toReal, ENNReal.toReal_nonneg, ENNReal.toReal_nonneg, _,
          (average_union hd ht hsμ htμ hfs hft).symm⟩
    calc
      0 < (μ s).toReal := ENNReal.toReal_pos hse hsμ
      _ ≤ _ := le_add_of_nonneg_right ENNReal.toReal_nonneg
#align measure_theory.average_union_mem_segment MeasureTheory.average_union_mem_segment

theorem average_mem_openSegment_compl_self [IsFiniteMeasure μ] {f : α → E} {s : Set α}
    (hs : NullMeasurableSet s μ) (hs₀ : μ s ≠ 0) (hsc₀ : μ (sᶜ) ≠ 0) (hfi : Integrable f μ) :
    ⨍ x, f x ∂μ ∈ openSegment ℝ (⨍ x in s, f x ∂μ) (⨍ x in sᶜ, f x ∂μ) := by
  simpa only [union_compl_self, restrict_univ] using
    average_union_mem_openSegment aedisjoint_compl_right hs.compl hs₀ hsc₀ (measure_ne_top _ _)
      (measure_ne_top _ _) hfi.integrableOn hfi.integrableOn
#align measure_theory.average_mem_open_segment_compl_self MeasureTheory.average_mem_openSegment_compl_self

@[simp]
theorem average_const [IsFiniteMeasure μ] [h : μ.ae.NeBot] (c : E) : ⨍ _, c ∂μ = c := by
  simp only [average_eq, integral_const, Measure.restrict_apply, MeasurableSet.univ, one_smul,
    univ_inter, smul_smul, ← ENNReal.toReal_inv, ← ENNReal.toReal_mul, ENNReal.inv_mul_cancel,
    measure_ne_top μ univ, Ne.def, measure_univ_eq_zero, ae_neBot.1 h, not_false_iff,
    ENNReal.one_toReal]
#align measure_theory.average_const MeasureTheory.average_const

theorem set_average_const {s : Set α} (hs₀ : μ s ≠ 0) (hs : μ s ≠ ∞) (c : E) :
    ⨍ _ in s, c ∂μ = c := by
  simp only [set_average_eq, integral_const, Measure.restrict_apply, MeasurableSet.univ, univ_inter,
    smul_smul, ← ENNReal.toReal_inv, ← ENNReal.toReal_mul, ENNReal.inv_mul_cancel hs₀ hs,
    ENNReal.one_toReal, one_smul]
#align measure_theory.set_average_const MeasureTheory.set_average_const

/-- If the average of a function `f` along a sequence of sets `aₙ` converges to `c` (more precisely,
we require that `⨍ y in a i, ‖f y - c‖ ∂μ` tends to `0`), then the integral of `gₙ • f` also tends
to `c` if `gₙ` is supported in `aₙ`, has integral converging to one and supremum at most `K / μ aₙ`.
-/
theorem tendsto_integral_smul_of_tendsto_average_norm_sub
    {ι : Type _} {a : ι → Set α} {l : Filter ι} {f : α → E} {c : E} {g : ι → α → ℝ} (K : ℝ)
    (hf : Tendsto (fun i ↦ ⨍ y in a i, ‖f y - c‖ ∂μ) l (𝓝 0))
    (f_int : ∀ᶠ i in l, IntegrableOn f (a i) μ)
    (hg : Tendsto (fun i ↦ ∫ y, g i y ∂μ) l (𝓝 1))
    (g_supp : ∀ᶠ i in l, Function.support (g i) ⊆ a i)
    (g_bound : ∀ᶠ i in l, ∀ x, |g i x| ≤ K / (μ (a i)).toReal) :
    Tendsto (fun i ↦ ∫ y, g i y • f y ∂μ) l (𝓝 c) := by
  have g_int : ∀ᶠ i in l, Integrable (g i) μ := by
    filter_upwards [(tendsto_order.1 hg).1 _ zero_lt_one] with i hi
    contrapose hi
    simp only [integral_undef hi, lt_self_iff_false, not_false_eq_true]
  have I : ∀ᶠ i in l, ∫ y, g i y • (f y - c) ∂μ + (∫ y, g i y ∂μ) • c = ∫ y, g i y • f y ∂μ := by
    filter_upwards [f_int, g_int, g_supp, g_bound] with i hif hig hisupp hibound
    dsimp
    rw [← integral_smul_const, ← integral_add]
    · simp only [smul_sub, sub_add_cancel]
    · simp_rw [smul_sub]
      apply Integrable.sub _ (hig.smul_const _)
      have A : Function.support (fun y ↦ g i y • f y) ⊆ a i := by
        apply Subset.trans _ hisupp
        exact Function.support_smul_subset_left _ _
      rw [← integrableOn_iff_integrable_of_support_subset A]
      apply Integrable.smul_of_top_right hif
      exact memℒp_top_of_bound hig.aestronglyMeasurable.restrict
        (K / (μ (a i)).toReal) (eventually_of_forall hibound)
    · exact hig.smul_const _
  have L0 : Tendsto (fun i ↦ ∫ y, g i y • (f y - c) ∂μ) l (𝓝 0) := by
    have := hf.const_mul K
    simp only [mul_zero] at this
    refine' squeeze_zero_norm' _ this
    filter_upwards [g_supp, g_bound, f_int, (tendsto_order.1 hg).1 _ zero_lt_one]
      with i hi h'i h''i hi_int
    have mu_ai : μ (a i) < ∞ := by
      rw [lt_top_iff_ne_top]
      intro h
      simp only [h, ENNReal.top_toReal, div_zero, abs_nonpos_iff] at h'i
      have : ∫ (y : α), g i y ∂μ = ∫ (y : α), 0 ∂μ := by congr; ext y; exact h'i y
      simp [this] at hi_int
    apply (norm_integral_le_integral_norm _).trans
    simp_rw [average_eq, smul_eq_mul, ← integral_mul_left, norm_smul, ← mul_assoc, ← div_eq_mul_inv]
    have : ∀ x, x ∉ a i → ‖g i x‖ * ‖(f x - c)‖ = 0 := by
      intro x hx
      have : g i x = 0 := by rw [← Function.nmem_support]; exact fun h ↦ hx (hi h)
      simp [this]
    rw [← set_integral_eq_integral_of_forall_compl_eq_zero this (μ := μ)]
    refine' integral_mono_of_nonneg (eventually_of_forall (fun x ↦ by positivity)) _
      (eventually_of_forall (fun x ↦ _))
    · apply (Integrable.sub h''i _).norm.const_mul
      change IntegrableOn (fun _ ↦ c) (a i) μ
      simp [integrableOn_const, mu_ai]
    · dsimp; gcongr; simpa using h'i x
  have := L0.add (hg.smul_const c)
  simp only [one_smul, zero_add] at this
  exact Tendsto.congr' I this

end MeasureTheory
