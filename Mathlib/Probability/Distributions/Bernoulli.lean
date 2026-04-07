module

public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.HasLaw

public section

open MeasureTheory Measure unitInterval Set
open scoped ENNReal

namespace ProbabilityTheory


variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {a b : α} {p : I}

@[expose]
noncomputable def bernoulliMeasure (a b : α) (p : I) : Measure α :=
  toNNReal p • dirac a + toNNReal (σ p) • dirac b

lemma bernoulliMeasure_def (a b : α) (p : I) :
    bernoulliMeasure a b p = toNNReal p • dirac a + toNNReal (σ p) • dirac b := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma bernoulliMeasure_apply_of_mem_of_mem (p : I) {s : Set α}
    (hs : MeasurableSet s) (ha : a ∈ s) (hb : b ∈ s) :
    bernoulliMeasure a b p s = 1 := by
  simp_all [bernoulliMeasure_def, ← add_smul]

@[simp]
lemma ENNReal.nnreal_smul_one (r : NNReal) :
    r • (1 : ℝ≥0∞) = r := by
  change ((r • 1 : NNReal) : ENNReal) = r
  simp

@[simp]
lemma bernoulliMeasure_apply_of_mem_of_notMem (p : I) {s : Set α}
    (hs : MeasurableSet s) (ha : a ∈ s) (hb : b ∉ s) :
    bernoulliMeasure a b p s = toNNReal p := by
  simp_all [bernoulliMeasure_def]

@[simp]
lemma bernoulliMeasure_apply_of_notMem_of_mem (p : I) {s : Set α}
    (hs : MeasurableSet s) (ha : a ∉ s) (hb : b ∈ s) :
    bernoulliMeasure a b p s = toNNReal (σ p) := by
  simp_all [bernoulliMeasure_def]

@[simp]
lemma bernoulliMeasure_apply_of_notMem_of_notMem (p : I) {s : Set α}
    (hs : MeasurableSet s) (ha : a ∉ s) (hb : b ∉ s) :
    bernoulliMeasure a b p s = 0 := by
  simp_all [bernoulliMeasure_def]
@[simp]
lemma bernoulliMeasure_real_apply_of_mem_of_mem (p : I) {s : Set α}
    (hs : MeasurableSet s) (ha : a ∈ s) (hb : b ∈ s) :
    (bernoulliMeasure a b p).real s = 1 := by
  simp_all [bernoulliMeasure_def, measureReal_def, ENNReal.toReal_add]

@[simp]
lemma bernoulliMeasure_real_apply_of_mem_of_notMem (p : I) {s : Set α}
    (hs : MeasurableSet s) (ha : a ∈ s) (hb : b ∉ s) :
    (bernoulliMeasure a b p).real s = p := by
  simp_all [bernoulliMeasure_def, measureReal_def]

@[simp]
lemma bernoulliMeasure_real_apply_of_notMem_of_mem (p : I) {s : Set α}
    (hs : MeasurableSet s) (ha : a ∉ s) (hb : b ∈ s) :
    (bernoulliMeasure a b p).real s = 1 - p := by
  simp_all [bernoulliMeasure_def, measureReal_def]

@[simp]
lemma bernoulliMeasure_real_apply_of_notMem_of_notMem (p : I) {s : Set α}
    (hs : MeasurableSet s) (ha : a ∉ s) (hb : b ∉ s) :
    (bernoulliMeasure a b p).real s = 0 := by
  simp_all [bernoulliMeasure_def, measureReal_def]

instance (a b : α) (p : I) : IsProbabilityMeasure (bernoulliMeasure a b p) where
  measure_univ := by simp [bernoulliMeasure_def]

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem bernoulliMeasure_self_eq_dirac (a : α) (p : I) :
    bernoulliMeasure a a p = dirac a := by
  simp [bernoulliMeasure_def, ← add_smul]

@[simp]
theorem map_bernoulliMeasure [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (a b : α) (f : α → β) (p : I) :
    (bernoulliMeasure a b p).map f = bernoulliMeasure (f a) (f b) p := by
  have hf (a : α) : AEMeasurable f (dirac a) := by fun_prop
  simp only [bernoulliMeasure_def]
  rw [AEMeasurable.map_add₀ (by fun_prop) (by fun_prop)]
  simp

theorem map_bernoulliMeasure' (a b : α) {f : α → β} (hf : Measurable f) (p : I) :
    (bernoulliMeasure a b p).map f = bernoulliMeasure (f a) (f b) p := by
  simp [bernoulliMeasure_def, Measure.map_add _ _ hf, Measure.map_smul, map_dirac' hf]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

@[simp]
lemma test {x : I} : ((toNNReal x) : ℝ≥0∞) = ENNReal.ofReal x := by
  rw [ENNReal.coe_nnreal_eq]
  rfl

theorem HasLaw.uniform_le_hasLaw {M : Type*} [Zero M] [MeasurableSpace M]
    [MeasurableSingletonClass M] (c : M) [NeZero c] {s : Set Ω}
    (hs : NullMeasurableSet s P) :
    HasLaw (s.indicator (fun _ ↦ c)) (bernoulliMeasure c 0 ⟨P.real s, by simp⟩) P where
  aemeasurable := (aemeasurable_indicator_const_iff c).2 hs
  map_eq := by
    have := (aemeasurable_indicator_const_iff c).2 hs
    ext t ht
    rw [map_apply_of_aemeasurable this ht]
    by_cases! h1 : 0 ∈ t <;> by_cases h2 : c ∈ t
    · have : s.indicator (fun _ ↦ c) ⁻¹' t = univ := by
        ext x; simp; by_cases h : x ∈ s <;> simpa [h]
      rw [this]
      simp_all
    · have : s.indicator (fun _ ↦ c) ⁻¹' t = sᶜ := by ext x; simp; by_cases h : x ∈ s <;> simpa [h]
      rw [this]
      simp_all [measure_compl₀ hs, ENNReal.ofReal_sub]
    · have : s.indicator (fun _ ↦ c) ⁻¹' t = s := by ext x; simp; by_cases h : x ∈ s <;> simpa [h]
      rw [this]
      simp_all
    · have : s.indicator (fun _ ↦ c) ⁻¹' t = ∅ := by ext x; simp; by_cases h : x ∈ s <;> simpa [h]
      rw [this]
      simp_all
theorem HasLaw.uniform_le_hasLaw' {M : Type*} [Zero M] [One M] [MeasurableSpace M]
    [MeasurableSingletonClass M] [NeZero (1 : M)] {s : Set Ω}
    (hs : NullMeasurableSet s P) :
    HasLaw (s.indicator (1 : Ω → M)) (bernoulliMeasure 1 0 ⟨P.real s, by simp⟩) P :=
  HasLaw.uniform_le_hasLaw 1 hs

end ProbabilityTheory
