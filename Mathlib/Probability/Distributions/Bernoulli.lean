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

@[expose]
noncomputable def bernoulliMeasure (x y : X) (p : I) : Measure X :=
  toNNReal p • dirac x + toNNReal (σ p) • dirac y

scoped notation "Ber(" x ", " y ", " p ")" => bernoulliMeasure x y p

lemma bernoulliMeasure_def (x y : X) (p : I) :
    Ber(x, y, p) = toNNReal p • dirac x + toNNReal (σ p) • dirac y := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma bernoulliMeasure_zero (x y : X) : bernoulliMeasure x y 0 = dirac y := by
  simp [bernoulliMeasure_def]

set_option backward.isDefEq.respectTransparency false in
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

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma bernoulliMeasure_apply_of_mem_of_mem (p : I) {s : Set X}
    (hs : MeasurableSet s) (hx : x ∈ s) (hy : y ∈ s) :
    Ber(x, y, p) s = 1 := by
  classical
  simp_all [bernoulliMeasure_apply]

@[simp]
lemma bernoulliMeasure_apply_of_mem_of_notMem (p : I) {s : Set X}
    (hs : MeasurableSet s) (hx : x ∈ s) (hy : y ∉ s) :
    Ber(x, y, p) s = toNNReal p := by
  classical
  simp_all [bernoulliMeasure_apply]

@[simp]
lemma bernoulliMeasure_apply_of_notMem_of_mem (p : I) {s : Set X}
    (hs : MeasurableSet s) (hx : x ∉ s) (hy : y ∈ s) :
    Ber(x, y, p) s = toNNReal (σ p) := by
  classical
  simp_all [bernoulliMeasure_apply]

@[simp]
lemma bernoulliMeasure_apply_of_notMem_of_notMem (p : I) {s : Set X}
    (hs : MeasurableSet s) (hx : x ∉ s) (hy : y ∉ s) :
    Ber(x, y, p) s = 0 := by
  classical
  simp_all [bernoulliMeasure_apply]

@[simp]
lemma bernoulliMeasure_apply_singleton_left [MeasurableSingletonClass X] (p : I) (h : x ≠ y) :
    Ber(x, y, p) {x} = toNNReal p :=
  bernoulliMeasure_apply_of_mem_of_notMem p (by simp) (by simp) (by grind)

@[simp]
lemma bernoulliMeasure_apply_singleton_right [MeasurableSingletonClass X] (p : I) (h : x ≠ y) :
    Ber(x, y, p) {y} = toNNReal (σ p) :=
  bernoulliMeasure_apply_of_notMem_of_mem p (by simp) (by grind) (by grind)

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
lemma bernoulliMeasure_real_apply_of_mem_of_mem (p : I) {s : Set X}
    (hs : MeasurableSet s) (hx : x ∈ s) (hy : y ∈ s) :
    Ber(x, y, p).real s = 1 := by
  classical
  simp_all [bernoulliMeasure_real_apply]

@[simp]
lemma bernoulliMeasure_real_apply_of_mem_of_notMem (p : I) {s : Set X}
    (hs : MeasurableSet s) (hx : x ∈ s) (hy : y ∉ s) :
    Ber(x, y, p).real s = p := by
  classical
  simp_all [bernoulliMeasure_real_apply]

@[simp]
lemma bernoulliMeasure_real_apply_of_notMem_of_mem (p : I) {s : Set X}
    (hs : MeasurableSet s) (hx : x ∉ s) (hy : y ∈ s) :
    Ber(x, y, p).real s = 1 - p := by
  classical
  simp_all [bernoulliMeasure_real_apply]

@[simp]
lemma bernoulliMeasure_real_apply_of_notMem_of_notMem (p : I) {s : Set X}
    (hs : MeasurableSet s) (hx : x ∉ s) (hy : y ∉ s) :
    Ber(x, y, p).real s = 0 := by
  classical
  simp_all [bernoulliMeasure_real_apply]

@[simp]
lemma bernoulliMeasure_real_apply_singleton_left [MeasurableSingletonClass X] (p : I) (h : x ≠ y) :
    Ber(x, y, p).real {x} = p :=
  bernoulliMeasure_real_apply_of_mem_of_notMem p (by simp) (by simp) (by grind)

@[simp]
lemma bernoulliMeasure_real_apply_singleton_right [MeasurableSingletonClass X] (p : I) (h : x ≠ y) :
    Ber(x, y, p).real {y} = 1 - p :=
  bernoulliMeasure_real_apply_of_notMem_of_mem p (by simp) (by grind) (by grind)

instance : IsProbabilityMeasure Ber(x, y, p) where
  measure_univ := by simp [bernoulliMeasure_def]

set_option backward.isDefEq.respectTransparency false in
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

end Integral

section HasLaw

/-! ### Bernoulli random variables -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

theorem hasLaw_indicator_bernoulliMeasure [IsProbabilityMeasure P] {M : Type*} [Zero M]
    [MeasurableSpace M] [MeasurableSingletonClass M] (c : M) [NeZero c] {s : Set Ω}
    (hs : NullMeasurableSet s P) :
    HasLaw (s.indicator (fun _ ↦ c)) (bernoulliMeasure c 0 ⟨P.real s, by simp⟩) P where
  aemeasurable := (aemeasurable_indicator_const_iff c).2 hs
  map_eq := by
    classical
    have := (aemeasurable_indicator_const_iff c).2 hs
    apply eq_bernoulliMeasure
    all_goals
      intro t ht h1 h2
      rw [map_apply_of_aemeasurable this ht]
      simp_all [Set.indicator_const_preimage_eq_union, measure_compl₀ hs, ENNReal.coe_nnreal_eq,
        ENNReal.ofReal_sub]

theorem hasLaw_indicator_one_bernoulliMeasure [IsProbabilityMeasure P] {M : Type*} [Zero M] [One M]
    [MeasurableSpace M] [MeasurableSingletonClass M] [NeZero (1 : M)] {s : Set Ω}
    (hs : NullMeasurableSet s P) :
    HasLaw (s.indicator (1 : Ω → M)) (bernoulliMeasure 1 0 ⟨P.real s, by simp⟩) P :=
  hasLaw_indicator_bernoulliMeasure 1 hs

end HasLaw

end ProbabilityTheory
