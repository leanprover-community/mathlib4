/-
Copyright (c) 2026 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion, David Ledvinka
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.HasLaw
public import Mathlib.Topology.UnitInterval

/-!
# Bernoulli distribution

We define the **Bernoulli distribution** over an arbitrary measurable space `X`. Given `x y : X`
and `p : I` (`I` is the `unitInterval`),
`Ber(x, y, p) := toNNReal p • dirac x + toNNReal (σ p) • dirac y`.
It is the measure which gives mass `p` to `{x}` and `1 - p` to `{y}`.

## Main definition

* `bernoulliMeasure x y p`: The measure `Ber(x, y, p)` which gives mass
  `p` to `{x}` and `1 - p` to `{y}`.

## Notation

* `Ber(x, y, p)`: notation for `bernoulliMeasure x y p`.

## Tags

Bernoulli distribution
-/

public section

open MeasureTheory Measure unitInterval
open scoped ENNReal

namespace ProbabilityTheory

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {x y : X} {p : I}

/-- The **Bernoulli distribution** over an arbitrary measurable space `X`.
Given `x y : X` and `p : I` (`I` is the `unitInterval`),
it is the measure which gives mass `p` to `{x}` and `1 - p` to `{y}`. -/
@[expose]
noncomputable def bernoulliMeasure (x y : X) (p : I) : Measure X :=
  toNNReal p • dirac x + toNNReal (σ p) • dirac y

@[inherit_doc]
scoped notation "Ber(" x ", " y ", " p ")" => bernoulliMeasure x y p

lemma bernoulliMeasure_def (x y : X) (p : I) :
    Ber(x, y, p) = toNNReal p • dirac x + toNNReal (σ p) • dirac y := rfl

@[simp]
lemma bernoulliMeasure_zero (x y : X) : bernoulliMeasure x y 0 = dirac y := by
  simp [bernoulliMeasure_def]

@[simp]
lemma bernoulliMeasure_one (x y : X) : bernoulliMeasure x y 1 = dirac x := by
  simp [bernoulliMeasure_def]

lemma bernoulliMeasure_apply (p : I) {s : Set X}
    (hs : MeasurableSet s) [DecidablePred (· ∈ s)] :
    Ber(x, y, p) s =
      if x ∈ s
        then if y ∈ s
          then (1 : ℝ≥0∞)
          else toNNReal p
        else if y ∈ s
          then toNNReal (σ p)
          else 0 := by
  split_ifs <;> simp_all [bernoulliMeasure_def, ← ENNReal.coe_add]

lemma bernoulliMeasure_real_apply (p : I) {s : Set X}
    (hs : MeasurableSet s) [DecidablePred (· ∈ s)] :
    Ber(x, y, p).real s =
      if x ∈ s
        then if y ∈ s
          then (1 : ℝ)
          else toNNReal p
        else if y ∈ s
          then toNNReal (σ p)
          else 0 := by
  simp [measureReal_def, bernoulliMeasure_apply p hs, apply_ite ENNReal.toReal]

@[simp]
lemma bernoulliMeasure_apply_of_mem_of_mem (p : I) {s : Set X}
    (hs : MeasurableSet s) (hx : x ∈ s) (hy : y ∈ s) :
    Ber(x, y, p) s = 1 := by
  classical
  simp_all [bernoulliMeasure_apply]

@[simp]
lemma bernoulliMeasure_real_apply_of_mem_of_mem (p : I) {s : Set X}
    (hs : MeasurableSet s) (hx : x ∈ s) (hy : y ∈ s) :
    Ber(x, y, p).real s = 1 := by
  classical
  simp_all [bernoulliMeasure_real_apply]

@[simp]
lemma bernoulliMeasure_apply_of_mem_of_notMem (p : I) {s : Set X}
    (hs : MeasurableSet s) (hx : x ∈ s) (hy : y ∉ s) :
    Ber(x, y, p) s = toNNReal p := by
  classical
  simp_all [bernoulliMeasure_apply]

@[simp]
lemma bernoulliMeasure_real_apply_of_mem_of_notMem (p : I) {s : Set X}
    (hs : MeasurableSet s) (hx : x ∈ s) (hy : y ∉ s) :
    Ber(x, y, p).real s = p := by
  classical
  simp_all [bernoulliMeasure_real_apply]

@[simp]
lemma bernoulliMeasure_apply_of_notMem_of_mem (p : I) {s : Set X}
    (hs : MeasurableSet s) (hx : x ∉ s) (hy : y ∈ s) :
    Ber(x, y, p) s = toNNReal (σ p) := by
  classical
  simp_all [bernoulliMeasure_apply]

@[simp]
lemma bernoulliMeasure_real_apply_of_notMem_of_mem (p : I) {s : Set X}
    (hs : MeasurableSet s) (hx : x ∉ s) (hy : y ∈ s) :
    Ber(x, y, p).real s = 1 - p := by
  classical
  simp_all [bernoulliMeasure_real_apply]

@[simp]
lemma bernoulliMeasure_apply_of_notMem_of_notMem (p : I) {s : Set X}
    (hs : MeasurableSet s) (hx : x ∉ s) (hy : y ∉ s) :
    Ber(x, y, p) s = 0 := by
  classical
  simp_all [bernoulliMeasure_apply]

@[simp]
lemma bernoulliMeasure_real_apply_of_notMem_of_notMem (p : I) {s : Set X}
    (hs : MeasurableSet s) (hx : x ∉ s) (hy : y ∉ s) :
    Ber(x, y, p).real s = 0 := by
  classical
  simp_all [bernoulliMeasure_real_apply]

instance : IsProbabilityMeasure Ber(x, y, p) where
  measure_univ := by simp [bernoulliMeasure_def]

@[simp]
theorem bernoulliMeasure_self_eq_dirac (x : X) (p : I) :
    bernoulliMeasure x x p = dirac x := by
  simp [bernoulliMeasure_def, ← add_smul]

@[simp]
theorem map_bernoulliMeasure [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    (x y : X) (f : X → Y) (p : I) :
    Ber(x, y, p).map f = bernoulliMeasure (f x) (f y) p := by
  have hf (x : X) : AEMeasurable f (dirac x) := by fun_prop
  simp only [bernoulliMeasure_def]
  rw [AEMeasurable.map_add₀ (by fun_prop) (by fun_prop)]
  simp

theorem map_bernoulliMeasure' (x y : X) {f : X → Y} (hf : Measurable f) (p : I) :
    Ber(x, y, p).map f = bernoulliMeasure (f x) (f y) p := by
  simp [bernoulliMeasure_def, Measure.map_add _ _ hf, Measure.map_smul, map_dirac' hf]

lemma eq_bernoulliMeasure {μ : Measure X}
    (h1 : ∀ s, MeasurableSet s → x ∈ s → y ∈ s → μ s = 1)
    (h2 : ∀ s, MeasurableSet s → x ∈ s → y ∉ s → μ s = toNNReal p)
    (h3 : ∀ s, MeasurableSet s → x ∉ s → y ∈ s → μ s = toNNReal (σ p))
    (h4 : ∀ s, MeasurableSet s → x ∉ s → y ∉ s → μ s = 0) :
    μ = Ber(x, y, p) := by
  ext s hs
  by_cases hx : x ∈ s <;> by_cases hy : y ∈ s <;> simp_all

section Integral

variable {E : Type*} [NormedAddCommGroup E]

variable {X E : Type*} {mX : MeasurableSpace X} [SeminormedAddCommGroup E]
  {f : X → E} {p : ENNReal} {μ ν : Measure X}

lemma test : eLpNormEssSup f (μ + ν) = max (eLpNormEssSup f μ) (eLpNormEssSup f ν) := by
  apply le_antisymm
  · apply eLpNormEssSup_le_of_ae_enorm_bound
    rw [ae_add_measure_iff]
    constructor
    filter_upwards [enorm_ae_le_eLpNormEssSup f μ] with x hx
    grw [hx, ← le_max_left]
    filter_upwards [enorm_ae_le_eLpNormEssSup f ν] with x hx
    grw [hx, ← le_max_right]
  · rw [max_le_iff]
    constructor
    · exact eLpNormEssSup_mono_measure _ (by exact AbsolutelyContinuous.add_right (fun ⦃s⦄ a ↦ a) ν)
    · exact eLpNormEssSup_mono_measure _ (by exact AbsolutelyContinuous.add_right' (fun ⦃s⦄ a ↦ a) μ)

lemma test' : eLpNormEssSup f (μ + ν) ≤ eLpNormEssSup f μ + eLpNormEssSup f ν := by
  apply eLpNormEssSup_le_of_ae_enorm_bound
  rw [ae_add_measure_iff]
  constructor
  filter_upwards [enorm_ae_le_eLpNormEssSup f μ] with x hx
  grw [hx, ← le_add_right]
  rfl
  filter_upwards [enorm_ae_le_eLpNormEssSup f ν] with x hx
  grw [hx, ← le_add_left]
  rfl

lemma test'' (p : ℝ) (hp : 1 ≤ p) : eLpNorm' f p (μ + ν) ≤ eLpNorm' f p μ + eLpNorm' f p ν := by
  grw [eLpNorm', lintegral_add_measure, ENNReal.rpow_add_le_add_rpow, ← eLpNorm', ← eLpNorm']
  simp
  grind
  rw [one_div_le]
  simpa
  grind
  grind

lemma test''' (hp : 1 ≤ p) : MemLp f p (μ + ν) ↔ MemLp f p μ ∧ MemLp f p ν where
  mp h := ⟨h.left_of_add_measure, h.right_of_add_measure⟩
  mpr h := by
    refine ⟨h.1.aestronglyMeasurable.add_measure h.2.aestronglyMeasurable, ?_⟩
    obtain rfl | hp' := eq_or_ne p ∞
    · grw [eLpNorm_exponent_top, test, max_le_add_of_nonneg, ← eLpNorm_exponent_top,
        ← eLpNorm_exponent_top, h.1.2]
      · simp
      · exact h.2.2.ne
      all_goals positivity
    · grw [eLpNorm_eq_eLpNorm' _ hp', test'', ← eLpNorm_eq_eLpNorm', ← eLpNorm_eq_eLpNorm',
        h.1.2]
      · simp
      · exact h.2.2.ne
      · exact zero_lt_one.trans_le hp |>.ne'
      · exact hp'
      · exact zero_lt_one.trans_le hp |>.ne'
      · exact hp'
      · rw [← ENNReal.ofReal_le_iff_le_toReal hp']
        simpa
      · exact zero_lt_one.trans_le hp |>.ne'

@[simp]
lemma eLpNormEssSup_dirac [MeasurableSingletonClass X] (x : X) :
    eLpNormEssSup f (dirac x) = ‖f x‖ₑ := by
  simp [eLpNormEssSup, essSup, Filter.limsup, Filter.limsSup]
  apply le_antisymm
  · apply sInf_le le_rfl
  · simp

lemma memLp_dirac (x : X) (q : ℝ≥0∞) [MeasurableSingletonClass X] : MemLp f q (dirac x) := by
  refine ⟨by fun_prop, ?_⟩
  rw [eLpNorm]
  split_ifs with hq hq'
  · simp
  · simp
  · simp [eLpNorm']
    finiteness

lemma memLp_bernoulliMeasure [MeasurableSingletonClass X] (x y : X) (p : I) (f : X → E) (q : ℝ≥0∞)
    (hq : 1 ≤ q) :
    MemLp f q Ber(x, y, p) := by
  simp [bernoulliMeasure_def, test''', hq,
    Integrable.smul_measure_nnreal]

lemma integrable_bernoulliMeasure [MeasurableSingletonClass X] (x y : X) (p : I) (f : X → E) :
    Integrable f Ber(x, y, p) := by
  simp [bernoulliMeasure_def, integrable_add_measure, integrable_dirac,
    Integrable.smul_measure_nnreal]

variable [NormedSpace ℝ E] [CompleteSpace E]

lemma integral_bernoulliMeasure [MeasurableSingletonClass X] (x y : X) (p : I) (f : X → E) :
    ∫ z, f z ∂Ber(x, y, p) = (p : ℝ) • (f x) + (1 - p : ℝ) • (f y) := by
  rw [bernoulliMeasure_def, integral_add_measure]
  · simp [NNReal.smul_def]
  all_goals exact (integrable_dirac (by simp)).smul_measure_nnreal

lemma integral_id_bernoulliMeasure : ∫ x : ℝ, x ∂Ber(1, 0, p) = p := by
  simp [integral_bernoulliMeasure]

lemma variance_id_bernoulliMeasure : Var[id; Ber(1, 0, p)] = p * (1 - p) := by
  rw [variance_eq_integral (by fun_prop)]
  simp [integral_bernoulliMeasure]
  ring

private lemma memLp_top_id_bernoulliMeasure : MemLp (id : ℝ → ℝ)

end Integral

section HasLaw

/-! ### Bernoulli random variables -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- The constant indicator of a set follows a Bernoulli distribution. -/
theorem hasLaw_indicator_bernoulliMeasure [IsProbabilityMeasure P] {M : Type*} [Zero M]
    [MeasurableSpace M] (c : M) {s : Set Ω} (hs : NullMeasurableSet s P) :
    HasLaw (s.indicator (fun _ ↦ c)) Ber(c, 0, ⟨P.real s, by simp⟩) P := by
  classical
  have h : AEMeasurable (s.indicator fun _ ↦ c) P := aemeasurable_const.indicator₀ hs
  refine ⟨h, eq_bernoulliMeasure ?_ ?_ ?_ ?_⟩
  all_goals
    intro t ht h1 h2
    simp_all [map_apply_of_aemeasurable h ht, Set.indicator_const_preimage_eq_union,
      measure_compl₀ hs, ENNReal.coe_nnreal_eq, ENNReal.ofReal_sub]

/-- The constant indicator of a set follows a Bernoulli distribution. -/
theorem hasLaw_indicator_one_bernoulliMeasure [IsProbabilityMeasure P] {M : Type*} [Zero M] [One M]
    [MeasurableSpace M] {s : Set Ω} (hs : NullMeasurableSet s P) :
    HasLaw (s.indicator (1 : Ω → M)) Ber(1, 0, ⟨P.real s, by simp⟩) P :=
  hasLaw_indicator_bernoulliMeasure 1 hs

end HasLaw

end ProbabilityTheory
