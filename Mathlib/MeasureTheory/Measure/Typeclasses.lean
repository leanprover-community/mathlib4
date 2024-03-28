/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.MeasureTheory.Measure.Restrict

/-!
# Classes of measures

We introduce the following typeclasses for measures:

* `IsProbabilityMeasure μ`: `μ univ = 1`;
* `IsFiniteMeasure μ`: `μ univ < ∞`;
* `SigmaFinite μ`: there exists a countable collection of sets that cover `univ`
  where `μ` is finite;
* `SFinite μ`: the measure `μ` can be written as a countable sum of finite measures;
* `IsLocallyFiniteMeasure μ` : `∀ x, ∃ s ∈ 𝓝 x, μ s < ∞`;
* `NoAtoms μ` : `∀ x, μ {x} = 0`; possibly should be redefined as
  `∀ s, 0 < μ s → ∃ t ⊆ s, 0 < μ t ∧ μ t < μ s`.
-/

open scoped ENNReal NNReal Topology BigOperators
open Set MeasureTheory Measure Filter Function MeasurableSpace ENNReal

variable {α β δ ι : Type*}

namespace MeasureTheory

variable {m0 : MeasurableSpace α} [MeasurableSpace β] {μ ν ν₁ ν₂: Measure α}
  {s t : Set α}

section IsFiniteMeasure

/-- A measure `μ` is called finite if `μ univ < ∞`. -/
class IsFiniteMeasure (μ : Measure α) : Prop where
  measure_univ_lt_top : μ univ < ∞
#align measure_theory.is_finite_measure MeasureTheory.IsFiniteMeasure
#align measure_theory.is_finite_measure.measure_univ_lt_top MeasureTheory.IsFiniteMeasure.measure_univ_lt_top

theorem not_isFiniteMeasure_iff : ¬IsFiniteMeasure μ ↔ μ Set.univ = ∞ := by
  refine' ⟨fun h => _, fun h => fun h' => h'.measure_univ_lt_top.ne h⟩
  by_contra h'
  exact h ⟨lt_top_iff_ne_top.mpr h'⟩
#align measure_theory.not_is_finite_measure_iff MeasureTheory.not_isFiniteMeasure_iff

instance Restrict.isFiniteMeasure (μ : Measure α) [hs : Fact (μ s < ∞)] :
    IsFiniteMeasure (μ.restrict s) :=
  ⟨by simpa using hs.elim⟩
#align measure_theory.restrict.is_finite_measure MeasureTheory.Restrict.isFiniteMeasure

theorem measure_lt_top (μ : Measure α) [IsFiniteMeasure μ] (s : Set α) : μ s < ∞ :=
  (measure_mono (subset_univ s)).trans_lt IsFiniteMeasure.measure_univ_lt_top
#align measure_theory.measure_lt_top MeasureTheory.measure_lt_top

instance isFiniteMeasureRestrict (μ : Measure α) (s : Set α) [h : IsFiniteMeasure μ] :
    IsFiniteMeasure (μ.restrict s) :=
  ⟨by simpa using measure_lt_top μ s⟩
#align measure_theory.is_finite_measure_restrict MeasureTheory.isFiniteMeasureRestrict

theorem measure_ne_top (μ : Measure α) [IsFiniteMeasure μ] (s : Set α) : μ s ≠ ∞ :=
  ne_of_lt (measure_lt_top μ s)
#align measure_theory.measure_ne_top MeasureTheory.measure_ne_top

theorem measure_compl_le_add_of_le_add [IsFiniteMeasure μ] (hs : MeasurableSet s)
    (ht : MeasurableSet t) {ε : ℝ≥0∞} (h : μ s ≤ μ t + ε) : μ tᶜ ≤ μ sᶜ + ε := by
  rw [measure_compl ht (measure_ne_top μ _), measure_compl hs (measure_ne_top μ _),
    tsub_le_iff_right]
  calc
    μ univ = μ univ - μ s + μ s := (tsub_add_cancel_of_le <| measure_mono s.subset_univ).symm
    _ ≤ μ univ - μ s + (μ t + ε) := (add_le_add_left h _)
    _ = _ := by rw [add_right_comm, add_assoc]

#align measure_theory.measure_compl_le_add_of_le_add MeasureTheory.measure_compl_le_add_of_le_add

theorem measure_compl_le_add_iff [IsFiniteMeasure μ] (hs : MeasurableSet s) (ht : MeasurableSet t)
    {ε : ℝ≥0∞} : μ sᶜ ≤ μ tᶜ + ε ↔ μ t ≤ μ s + ε :=
  ⟨fun h => compl_compl s ▸ compl_compl t ▸ measure_compl_le_add_of_le_add hs.compl ht.compl h,
    measure_compl_le_add_of_le_add ht hs⟩
#align measure_theory.measure_compl_le_add_iff MeasureTheory.measure_compl_le_add_iff

/-- The measure of the whole space with respect to a finite measure, considered as `ℝ≥0`. -/
def measureUnivNNReal (μ : Measure α) : ℝ≥0 :=
  (μ univ).toNNReal
#align measure_theory.measure_univ_nnreal MeasureTheory.measureUnivNNReal

@[simp]
theorem coe_measureUnivNNReal (μ : Measure α) [IsFiniteMeasure μ] :
    ↑(measureUnivNNReal μ) = μ univ :=
  ENNReal.coe_toNNReal (measure_ne_top μ univ)
#align measure_theory.coe_measure_univ_nnreal MeasureTheory.coe_measureUnivNNReal

instance isFiniteMeasureZero : IsFiniteMeasure (0 : Measure α) :=
  ⟨by simp⟩
#align measure_theory.is_finite_measure_zero MeasureTheory.isFiniteMeasureZero

instance (priority := 50) isFiniteMeasureOfIsEmpty [IsEmpty α] : IsFiniteMeasure μ := by
  rw [eq_zero_of_isEmpty μ]
  infer_instance
#align measure_theory.is_finite_measure_of_is_empty MeasureTheory.isFiniteMeasureOfIsEmpty

@[simp]
theorem measureUnivNNReal_zero : measureUnivNNReal (0 : Measure α) = 0 :=
  rfl
#align measure_theory.measure_univ_nnreal_zero MeasureTheory.measureUnivNNReal_zero

instance isFiniteMeasureAdd [IsFiniteMeasure μ] [IsFiniteMeasure ν] : IsFiniteMeasure (μ + ν) where
  measure_univ_lt_top := by
    rw [Measure.coe_add, Pi.add_apply, ENNReal.add_lt_top]
    exact ⟨measure_lt_top _ _, measure_lt_top _ _⟩
#align measure_theory.is_finite_measure_add MeasureTheory.isFiniteMeasureAdd

instance isFiniteMeasureSMulNNReal [IsFiniteMeasure μ] {r : ℝ≥0} : IsFiniteMeasure (r • μ) where
  measure_univ_lt_top := ENNReal.mul_lt_top ENNReal.coe_ne_top (measure_ne_top _ _)
#align measure_theory.is_finite_measure_smul_nnreal MeasureTheory.isFiniteMeasureSMulNNReal

instance IsFiniteMeasure.average : IsFiniteMeasure ((μ univ)⁻¹ • μ) where
  measure_univ_lt_top := by
    rw [smul_apply, smul_eq_mul, ← ENNReal.div_eq_inv_mul]
    exact ENNReal.div_self_le_one.trans_lt ENNReal.one_lt_top

instance isFiniteMeasureSMulOfNNRealTower {R} [SMul R ℝ≥0] [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0 ℝ≥0∞]
    [IsScalarTower R ℝ≥0∞ ℝ≥0∞] [IsFiniteMeasure μ] {r : R} : IsFiniteMeasure (r • μ) := by
  rw [← smul_one_smul ℝ≥0 r μ]
  infer_instance
#align measure_theory.is_finite_measure_smul_of_nnreal_tower MeasureTheory.isFiniteMeasureSMulOfNNRealTower

theorem isFiniteMeasure_of_le (μ : Measure α) [IsFiniteMeasure μ] (h : ν ≤ μ) : IsFiniteMeasure ν :=
  { measure_univ_lt_top := (h Set.univ).trans_lt (measure_lt_top _ _) }
#align measure_theory.is_finite_measure_of_le MeasureTheory.isFiniteMeasure_of_le

@[instance]
theorem Measure.isFiniteMeasure_map {m : MeasurableSpace α} (μ : Measure α) [IsFiniteMeasure μ]
    (f : α → β) : IsFiniteMeasure (μ.map f) := by
  by_cases hf : AEMeasurable f μ
  · constructor
    rw [map_apply_of_aemeasurable hf MeasurableSet.univ]
    exact measure_lt_top μ _
  · rw [map_of_not_aemeasurable hf]
    exact MeasureTheory.isFiniteMeasureZero
#align measure_theory.measure.is_finite_measure_map MeasureTheory.Measure.isFiniteMeasure_map

@[simp]
theorem measureUnivNNReal_eq_zero [IsFiniteMeasure μ] : measureUnivNNReal μ = 0 ↔ μ = 0 := by
  rw [← MeasureTheory.Measure.measure_univ_eq_zero, ← coe_measureUnivNNReal]
  norm_cast
#align measure_theory.measure_univ_nnreal_eq_zero MeasureTheory.measureUnivNNReal_eq_zero

theorem measureUnivNNReal_pos [IsFiniteMeasure μ] (hμ : μ ≠ 0) : 0 < measureUnivNNReal μ := by
  contrapose! hμ
  simpa [measureUnivNNReal_eq_zero, Nat.le_zero] using hμ
#align measure_theory.measure_univ_nnreal_pos MeasureTheory.measureUnivNNReal_pos

/-- `le_of_add_le_add_left` is normally applicable to `OrderedCancelAddCommMonoid`,
but it holds for measures with the additional assumption that μ is finite. -/
theorem Measure.le_of_add_le_add_left [IsFiniteMeasure μ] (A2 : μ + ν₁ ≤ μ + ν₂) : ν₁ ≤ ν₂ :=
  fun S => ENNReal.le_of_add_le_add_left (MeasureTheory.measure_ne_top μ S) (A2 S)
#align measure_theory.measure.le_of_add_le_add_left MeasureTheory.Measure.le_of_add_le_add_left

theorem summable_measure_toReal [hμ : IsFiniteMeasure μ] {f : ℕ → Set α}
    (hf₁ : ∀ i : ℕ, MeasurableSet (f i)) (hf₂ : Pairwise (Disjoint on f)) :
    Summable fun x => (μ (f x)).toReal := by
  apply ENNReal.summable_toReal
  rw [← MeasureTheory.measure_iUnion hf₂ hf₁]
  exact ne_of_lt (measure_lt_top _ _)
#align measure_theory.summable_measure_to_real MeasureTheory.summable_measure_toReal

@[simp]
lemma _root_.Finset.sum_toReal_measure_singleton {s : Finset α} [MeasurableSingletonClass α]
    [IsFiniteMeasure μ] :
    ∑ x in s, (μ {x}).toReal = (μ s).toReal := by
  rw [← ENNReal.toReal_sum (fun _ _ ↦ measure_ne_top _ _)]
  simp

theorem ae_eq_univ_iff_measure_eq [IsFiniteMeasure μ] (hs : NullMeasurableSet s μ) :
    s =ᵐ[μ] univ ↔ μ s = μ univ := by
  refine' ⟨measure_congr, fun h => _⟩
  obtain ⟨t, -, ht₁, ht₂⟩ := hs.exists_measurable_subset_ae_eq
  exact
    ht₂.symm.trans
      (ae_eq_of_subset_of_measure_ge (subset_univ t) (Eq.le ((measure_congr ht₂).trans h).symm) ht₁
        (measure_ne_top μ univ))
#align measure_theory.ae_eq_univ_iff_measure_eq MeasureTheory.ae_eq_univ_iff_measure_eq

theorem ae_iff_measure_eq [IsFiniteMeasure μ] {p : α → Prop}
    (hp : NullMeasurableSet { a | p a } μ) : (∀ᵐ a ∂μ, p a) ↔ μ { a | p a } = μ univ := by
  rw [← ae_eq_univ_iff_measure_eq hp, eventuallyEq_univ, eventually_iff]
#align measure_theory.ae_iff_measure_eq MeasureTheory.ae_iff_measure_eq

theorem ae_mem_iff_measure_eq [IsFiniteMeasure μ] {s : Set α} (hs : NullMeasurableSet s μ) :
    (∀ᵐ a ∂μ, a ∈ s) ↔ μ s = μ univ :=
  ae_iff_measure_eq hs
#align measure_theory.ae_mem_iff_measure_eq MeasureTheory.ae_mem_iff_measure_eq

open scoped symmDiff

theorem abs_toReal_measure_sub_le_measure_symmDiff'
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hs' : μ s ≠ ∞) (ht' : μ t ≠ ∞) :
    |(μ s).toReal - (μ t).toReal| ≤ (μ (s ∆ t)).toReal := by
  have hst : μ (s \ t) ≠ ∞ := (measure_lt_top_of_subset (diff_subset s t) hs').ne
  have hts : μ (t \ s) ≠ ∞ := (measure_lt_top_of_subset (diff_subset t s) ht').ne
  suffices (μ s).toReal - (μ t).toReal = (μ (s \ t)).toReal - (μ (t \ s)).toReal by
    rw [this, measure_symmDiff_eq hs ht, ENNReal.toReal_add hst hts]
    convert abs_sub (μ (s \ t)).toReal (μ (t \ s)).toReal <;> simp
  rw [measure_diff' s ht ht', measure_diff' t hs hs',
    ENNReal.toReal_sub_of_le measure_le_measure_union_right (measure_union_ne_top hs' ht'),
    ENNReal.toReal_sub_of_le measure_le_measure_union_right (measure_union_ne_top ht' hs'),
    union_comm t s]
  abel

theorem abs_toReal_measure_sub_le_measure_symmDiff [IsFiniteMeasure μ]
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    |(μ s).toReal - (μ t).toReal| ≤ (μ (s ∆ t)).toReal :=
  abs_toReal_measure_sub_le_measure_symmDiff' hs ht (measure_ne_top μ s) (measure_ne_top μ t)

end IsFiniteMeasure

section IsProbabilityMeasure

/-- A measure `μ` is called a probability measure if `μ univ = 1`. -/
class IsProbabilityMeasure (μ : Measure α) : Prop where
  measure_univ : μ univ = 1
#align measure_theory.is_probability_measure MeasureTheory.IsProbabilityMeasure
#align measure_theory.is_probability_measure.measure_univ MeasureTheory.IsProbabilityMeasure.measure_univ

export MeasureTheory.IsProbabilityMeasure (measure_univ)

attribute [simp] IsProbabilityMeasure.measure_univ

lemma isProbabilityMeasure_iff : IsProbabilityMeasure μ ↔ μ univ = 1 :=
  ⟨fun _ ↦ measure_univ, IsProbabilityMeasure.mk⟩

instance (priority := 100) IsProbabilityMeasure.toIsFiniteMeasure (μ : Measure α)
    [IsProbabilityMeasure μ] : IsFiniteMeasure μ :=
  ⟨by simp only [measure_univ, ENNReal.one_lt_top]⟩
#align measure_theory.is_probability_measure.to_is_finite_measure MeasureTheory.IsProbabilityMeasure.toIsFiniteMeasure

theorem IsProbabilityMeasure.ne_zero (μ : Measure α) [IsProbabilityMeasure μ] : μ ≠ 0 :=
  mt measure_univ_eq_zero.2 <| by simp [measure_univ]
#align measure_theory.is_probability_measure.ne_zero MeasureTheory.IsProbabilityMeasure.ne_zero

instance (priority := 100) IsProbabilityMeasure.neZero (μ : Measure α) [IsProbabilityMeasure μ] :
    NeZero μ := ⟨IsProbabilityMeasure.ne_zero μ⟩

-- Porting note: no longer an `instance` because `inferInstance` can find it now
theorem IsProbabilityMeasure.ae_neBot [IsProbabilityMeasure μ] : NeBot μ.ae := inferInstance
#align measure_theory.is_probability_measure.ae_ne_bot MeasureTheory.IsProbabilityMeasure.ae_neBot

theorem prob_add_prob_compl [IsProbabilityMeasure μ] (h : MeasurableSet s) : μ s + μ sᶜ = 1 :=
  (measure_add_measure_compl h).trans measure_univ
#align measure_theory.prob_add_prob_compl MeasureTheory.prob_add_prob_compl

theorem prob_le_one [IsProbabilityMeasure μ] : μ s ≤ 1 :=
  (measure_mono <| Set.subset_univ _).trans_eq measure_univ
#align measure_theory.prob_le_one MeasureTheory.prob_le_one

-- Porting note: made an `instance`, using `NeZero`
instance isProbabilityMeasureSMul [IsFiniteMeasure μ] [NeZero μ] :
    IsProbabilityMeasure ((μ univ)⁻¹ • μ) :=
  ⟨ENNReal.inv_mul_cancel (NeZero.ne (μ univ)) (measure_ne_top _ _)⟩
#align measure_theory.is_probability_measure_smul MeasureTheory.isProbabilityMeasureSMulₓ

variable [IsProbabilityMeasure μ] {p : α → Prop} {f : β → α}

theorem isProbabilityMeasure_map {f : α → β} (hf : AEMeasurable f μ) :
    IsProbabilityMeasure (map f μ) :=
  ⟨by simp [map_apply_of_aemeasurable, hf]⟩
#align measure_theory.is_probability_measure_map MeasureTheory.isProbabilityMeasure_map

@[simp]
theorem one_le_prob_iff : 1 ≤ μ s ↔ μ s = 1 :=
  ⟨fun h => le_antisymm prob_le_one h, fun h => h ▸ le_refl _⟩
#align measure_theory.one_le_prob_iff MeasureTheory.one_le_prob_iff

/-- Note that this is not quite as useful as it looks because the measure takes values in `ℝ≥0∞`.
Thus the subtraction appearing is the truncated subtraction of `ℝ≥0∞`, rather than the
better-behaved subtraction of `ℝ`. -/
lemma prob_compl_eq_one_sub₀ (h : NullMeasurableSet s μ) : μ sᶜ = 1 - μ s := by
  rw [measure_compl₀ h (measure_ne_top _ _), measure_univ]

/-- Note that this is not quite as useful as it looks because the measure takes values in `ℝ≥0∞`.
Thus the subtraction appearing is the truncated subtraction of `ℝ≥0∞`, rather than the
better-behaved subtraction of `ℝ`. -/
theorem prob_compl_eq_one_sub (hs : MeasurableSet s) : μ sᶜ = 1 - μ s :=
  prob_compl_eq_one_sub₀ hs.nullMeasurableSet
#align measure_theory.prob_compl_eq_one_sub MeasureTheory.prob_compl_eq_one_sub

@[simp] lemma prob_compl_eq_zero_iff₀ (hs : NullMeasurableSet s μ) : μ sᶜ = 0 ↔ μ s = 1 := by
  rw [prob_compl_eq_one_sub₀ hs, tsub_eq_zero_iff_le, one_le_prob_iff]

@[simp] lemma prob_compl_eq_zero_iff (hs : MeasurableSet s) : μ sᶜ = 0 ↔ μ s = 1 :=
  prob_compl_eq_zero_iff₀ hs.nullMeasurableSet
#align measure_theory.prob_compl_eq_zero_iff MeasureTheory.prob_compl_eq_zero_iff

@[simp] lemma prob_compl_eq_one_iff₀ (hs : NullMeasurableSet s μ) : μ sᶜ = 1 ↔ μ s = 0 := by
  rw [← prob_compl_eq_zero_iff₀ hs.compl, compl_compl]

@[simp] lemma prob_compl_eq_one_iff (hs : MeasurableSet s) : μ sᶜ = 1 ↔ μ s = 0 :=
  prob_compl_eq_one_iff₀ hs.nullMeasurableSet
#align measure_theory.prob_compl_eq_one_iff MeasureTheory.prob_compl_eq_one_iff

lemma mem_ae_iff_prob_eq_one₀ (hs : NullMeasurableSet s μ) : s ∈ μ.ae ↔ μ s = 1 :=
  mem_ae_iff.trans <| prob_compl_eq_zero_iff₀ hs

lemma mem_ae_iff_prob_eq_one (hs : MeasurableSet s) : s ∈ μ.ae ↔ μ s = 1 :=
  mem_ae_iff.trans <| prob_compl_eq_zero_iff hs

lemma ae_iff_prob_eq_one (hp : Measurable p) : (∀ᵐ a ∂μ, p a) ↔ μ {a | p a} = 1 :=
  mem_ae_iff_prob_eq_one hp.setOf

lemma isProbabilityMeasure_comap (hf : Injective f) (hf' : ∀ᵐ a ∂μ, a ∈ range f)
    (hf'' : ∀ s, MeasurableSet s → MeasurableSet (f '' s)) :
    IsProbabilityMeasure (μ.comap f) where
  measure_univ := by
    rw [comap_apply _ hf hf'' _ MeasurableSet.univ,
      ← mem_ae_iff_prob_eq_one (hf'' _ MeasurableSet.univ)]
    simpa

protected lemma _root_.MeasurableEmbedding.isProbabilityMeasure_comap (hf : MeasurableEmbedding f)
    (hf' : ∀ᵐ a ∂μ, a ∈ range f) : IsProbabilityMeasure (μ.comap f) :=
  isProbabilityMeasure_comap hf.injective hf' hf.measurableSet_image'

instance isProbabilityMeasure_map_up :
    IsProbabilityMeasure (μ.map ULift.up) := isProbabilityMeasure_map measurable_up.aemeasurable

instance isProbabilityMeasure_comap_down : IsProbabilityMeasure (μ.comap ULift.down) :=
  MeasurableEquiv.ulift.measurableEmbedding.isProbabilityMeasure_comap <| ae_of_all _ <| by
    simp [Function.Surjective.range_eq <| EquivLike.surjective _]

end IsProbabilityMeasure

section NoAtoms

/-- Measure `μ` *has no atoms* if the measure of each singleton is zero.

NB: Wikipedia assumes that for any measurable set `s` with positive `μ`-measure,
there exists a measurable `t ⊆ s` such that `0 < μ t < μ s`. While this implies `μ {x} = 0`,
the converse is not true. -/
class NoAtoms {m0 : MeasurableSpace α} (μ : Measure α) : Prop where
  measure_singleton : ∀ x, μ {x} = 0
#align measure_theory.has_no_atoms MeasureTheory.NoAtoms
#align measure_theory.has_no_atoms.measure_singleton MeasureTheory.NoAtoms.measure_singleton

export MeasureTheory.NoAtoms (measure_singleton)

attribute [simp] measure_singleton

variable [NoAtoms μ]

theorem _root_.Set.Subsingleton.measure_zero (hs : s.Subsingleton) (μ : Measure α) [NoAtoms μ] :
    μ s = 0 :=
  hs.induction_on (p := fun s => μ s = 0) measure_empty measure_singleton
#align set.subsingleton.measure_zero Set.Subsingleton.measure_zero

theorem Measure.restrict_singleton' {a : α} : μ.restrict {a} = 0 := by
  simp only [measure_singleton, Measure.restrict_eq_zero]
#align measure_theory.measure.restrict_singleton' MeasureTheory.Measure.restrict_singleton'

instance Measure.restrict.instNoAtoms (s : Set α) : NoAtoms (μ.restrict s) := by
  refine' ⟨fun x => _⟩
  obtain ⟨t, hxt, ht1, ht2⟩ := exists_measurable_superset_of_null (measure_singleton x : μ {x} = 0)
  apply measure_mono_null hxt
  rw [Measure.restrict_apply ht1]
  apply measure_mono_null (inter_subset_left t s) ht2
#align measure_theory.measure.restrict.has_no_atoms MeasureTheory.Measure.restrict.instNoAtoms

theorem _root_.Set.Countable.measure_zero (h : s.Countable) (μ : Measure α) [NoAtoms μ] :
    μ s = 0 := by
  rw [← biUnion_of_singleton s, ← nonpos_iff_eq_zero]
  refine' le_trans (measure_biUnion_le h _) _
  simp
#align set.countable.measure_zero Set.Countable.measure_zero

theorem _root_.Set.Countable.ae_not_mem (h : s.Countable) (μ : Measure α) [NoAtoms μ] :
    ∀ᵐ x ∂μ, x ∉ s := by
  simpa only [ae_iff, Classical.not_not] using h.measure_zero μ
#align set.countable.ae_not_mem Set.Countable.ae_not_mem

lemma _root_.Set.Countable.measure_restrict_compl (h : s.Countable) (μ : Measure α) [NoAtoms μ] :
    μ.restrict sᶜ = μ :=
  restrict_eq_self_of_ae_mem <| h.ae_not_mem μ

@[simp]
lemma restrict_compl_singleton (a : α) : μ.restrict ({a}ᶜ) = μ :=
  (countable_singleton _).measure_restrict_compl μ

theorem _root_.Set.Finite.measure_zero (h : s.Finite) (μ : Measure α) [NoAtoms μ] : μ s = 0 :=
  h.countable.measure_zero μ
#align set.finite.measure_zero Set.Finite.measure_zero

theorem _root_.Finset.measure_zero (s : Finset α) (μ : Measure α) [NoAtoms μ] : μ s = 0 :=
  s.finite_toSet.measure_zero μ
#align finset.measure_zero Finset.measure_zero

theorem insert_ae_eq_self (a : α) (s : Set α) : (insert a s : Set α) =ᵐ[μ] s :=
  union_ae_eq_right.2 <| measure_mono_null (diff_subset _ _) (measure_singleton _)
#align measure_theory.insert_ae_eq_self MeasureTheory.insert_ae_eq_self

section

variable [PartialOrder α] {a b : α}

theorem Iio_ae_eq_Iic : Iio a =ᵐ[μ] Iic a :=
  Iio_ae_eq_Iic' (measure_singleton a)
#align measure_theory.Iio_ae_eq_Iic MeasureTheory.Iio_ae_eq_Iic

theorem Ioi_ae_eq_Ici : Ioi a =ᵐ[μ] Ici a :=
  Ioi_ae_eq_Ici' (measure_singleton a)
#align measure_theory.Ioi_ae_eq_Ici MeasureTheory.Ioi_ae_eq_Ici

theorem Ioo_ae_eq_Ioc : Ioo a b =ᵐ[μ] Ioc a b :=
  Ioo_ae_eq_Ioc' (measure_singleton b)
#align measure_theory.Ioo_ae_eq_Ioc MeasureTheory.Ioo_ae_eq_Ioc

theorem Ioc_ae_eq_Icc : Ioc a b =ᵐ[μ] Icc a b :=
  Ioc_ae_eq_Icc' (measure_singleton a)
#align measure_theory.Ioc_ae_eq_Icc MeasureTheory.Ioc_ae_eq_Icc

theorem Ioo_ae_eq_Ico : Ioo a b =ᵐ[μ] Ico a b :=
  Ioo_ae_eq_Ico' (measure_singleton a)
#align measure_theory.Ioo_ae_eq_Ico MeasureTheory.Ioo_ae_eq_Ico

theorem Ioo_ae_eq_Icc : Ioo a b =ᵐ[μ] Icc a b :=
  Ioo_ae_eq_Icc' (measure_singleton a) (measure_singleton b)
#align measure_theory.Ioo_ae_eq_Icc MeasureTheory.Ioo_ae_eq_Icc

theorem Ico_ae_eq_Icc : Ico a b =ᵐ[μ] Icc a b :=
  Ico_ae_eq_Icc' (measure_singleton b)
#align measure_theory.Ico_ae_eq_Icc MeasureTheory.Ico_ae_eq_Icc

theorem Ico_ae_eq_Ioc : Ico a b =ᵐ[μ] Ioc a b :=
  Ico_ae_eq_Ioc' (measure_singleton a) (measure_singleton b)
#align measure_theory.Ico_ae_eq_Ioc MeasureTheory.Ico_ae_eq_Ioc

theorem restrict_Iio_eq_restrict_Iic : μ.restrict (Iio a) = μ.restrict (Iic a) :=
  restrict_congr_set Iio_ae_eq_Iic

theorem restrict_Ioi_eq_restrict_Ici : μ.restrict (Ioi a) = μ.restrict (Ici a) :=
  restrict_congr_set Ioi_ae_eq_Ici

theorem restrict_Ioo_eq_restrict_Ioc : μ.restrict (Ioo a b) = μ.restrict (Ioc a b) :=
  restrict_congr_set Ioo_ae_eq_Ioc

theorem restrict_Ioc_eq_restrict_Icc : μ.restrict (Ioc a b) = μ.restrict (Icc a b) :=
  restrict_congr_set Ioc_ae_eq_Icc

theorem restrict_Ioo_eq_restrict_Ico : μ.restrict (Ioo a b) = μ.restrict (Ico a b) :=
  restrict_congr_set Ioo_ae_eq_Ico

theorem restrict_Ioo_eq_restrict_Icc : μ.restrict (Ioo a b) = μ.restrict (Icc a b) :=
  restrict_congr_set Ioo_ae_eq_Icc

theorem restrict_Ico_eq_restrict_Icc : μ.restrict (Ico a b) = μ.restrict (Icc a b) :=
  restrict_congr_set Ico_ae_eq_Icc

theorem restrict_Ico_eq_restrict_Ioc : μ.restrict (Ico a b) = μ.restrict (Ioc a b) :=
  restrict_congr_set Ico_ae_eq_Ioc

end

open Interval

theorem uIoc_ae_eq_interval [LinearOrder α] {a b : α} : Ι a b =ᵐ[μ] [[a, b]] :=
  Ioc_ae_eq_Icc
#align measure_theory.uIoc_ae_eq_interval MeasureTheory.uIoc_ae_eq_interval

end NoAtoms

theorem ite_ae_eq_of_measure_zero {γ} (f : α → γ) (g : α → γ) (s : Set α) [DecidablePred (· ∈ s)]
    (hs_zero : μ s = 0) :
    (fun x => ite (x ∈ s) (f x) (g x)) =ᵐ[μ] g := by
  have h_ss : sᶜ ⊆ { a : α | ite (a ∈ s) (f a) (g a) = g a } := fun x hx => by
    simp [(Set.mem_compl_iff _ _).mp hx]
  refine' measure_mono_null _ hs_zero
  conv_rhs => rw [← compl_compl s]
  rwa [Set.compl_subset_compl]
#align measure_theory.ite_ae_eq_of_measure_zero MeasureTheory.ite_ae_eq_of_measure_zero

theorem ite_ae_eq_of_measure_compl_zero {γ} (f : α → γ) (g : α → γ)
    (s : Set α) [DecidablePred (· ∈ s)] (hs_zero : μ sᶜ = 0) :
    (fun x => ite (x ∈ s) (f x) (g x)) =ᵐ[μ] f := by
  change s ∈ μ.ae at hs_zero
  filter_upwards [hs_zero]
  intros
  split_ifs
  rfl
#align measure_theory.ite_ae_eq_of_measure_compl_zero MeasureTheory.ite_ae_eq_of_measure_compl_zero

namespace Measure

/-- A measure is called finite at filter `f` if it is finite at some set `s ∈ f`.
Equivalently, it is eventually finite at `s` in `f.small_sets`. -/
def FiniteAtFilter {_m0 : MeasurableSpace α} (μ : Measure α) (f : Filter α) : Prop :=
  ∃ s ∈ f, μ s < ∞
#align measure_theory.measure.finite_at_filter MeasureTheory.Measure.FiniteAtFilter

theorem finiteAtFilter_of_finite {_m0 : MeasurableSpace α} (μ : Measure α) [IsFiniteMeasure μ]
    (f : Filter α) : μ.FiniteAtFilter f :=
  ⟨univ, univ_mem, measure_lt_top μ univ⟩
#align measure_theory.measure.finite_at_filter_of_finite MeasureTheory.Measure.finiteAtFilter_of_finite

theorem FiniteAtFilter.exists_mem_basis {f : Filter α} (hμ : FiniteAtFilter μ f) {p : ι → Prop}
    {s : ι → Set α} (hf : f.HasBasis p s) : ∃ i, p i ∧ μ (s i) < ∞ :=
  (hf.exists_iff fun {_s _t} hst ht => (measure_mono hst).trans_lt ht).1 hμ
#align measure_theory.measure.finite_at_filter.exists_mem_basis MeasureTheory.Measure.FiniteAtFilter.exists_mem_basis

theorem finiteAtBot {m0 : MeasurableSpace α} (μ : Measure α) : μ.FiniteAtFilter ⊥ :=
  ⟨∅, mem_bot, by simp only [OuterMeasure.empty', zero_lt_top]⟩
#align measure_theory.measure.finite_at_bot MeasureTheory.Measure.finiteAtBot

/-- `μ` has finite spanning sets in `C` if there is a countable sequence of sets in `C` that have
  finite measures. This structure is a type, which is useful if we want to record extra properties
  about the sets, such as that they are monotone.
  `SigmaFinite` is defined in terms of this: `μ` is σ-finite if there exists a sequence of
  finite spanning sets in the collection of all measurable sets. -/
-- @[nolint has_nonempty_instance] -- Porting note: deleted
structure FiniteSpanningSetsIn {m0 : MeasurableSpace α} (μ : Measure α) (C : Set (Set α)) where
  protected set : ℕ → Set α
  protected set_mem : ∀ i, set i ∈ C
  protected finite : ∀ i, μ (set i) < ∞
  protected spanning : ⋃ i, set i = univ
#align measure_theory.measure.finite_spanning_sets_in MeasureTheory.Measure.FiniteSpanningSetsIn
#align measure_theory.measure.finite_spanning_sets_in.set MeasureTheory.Measure.FiniteSpanningSetsIn.set
#align measure_theory.measure.finite_spanning_sets_in.set_mem MeasureTheory.Measure.FiniteSpanningSetsIn.set_mem
#align measure_theory.measure.finite_spanning_sets_in.finite MeasureTheory.Measure.FiniteSpanningSetsIn.finite
#align measure_theory.measure.finite_spanning_sets_in.spanning MeasureTheory.Measure.FiniteSpanningSetsIn.spanning

end Measure

open Measure

section SFinite

/-- A measure is called s-finite if it is a countable sum of finite measures. -/
class SFinite (μ : Measure α) : Prop where
  out' : ∃ m : ℕ → Measure α, (∀ n, IsFiniteMeasure (m n)) ∧ μ = Measure.sum m

/-- A sequence of finite measures such that `μ = sum (sFiniteSeq μ)` (see `sum_sFiniteSeq`). -/
noncomputable
def sFiniteSeq (μ : Measure α) [h : SFinite μ] : ℕ → Measure α := h.1.choose

instance isFiniteMeasure_sFiniteSeq [h : SFinite μ] (n : ℕ) : IsFiniteMeasure (sFiniteSeq μ n) :=
  h.1.choose_spec.1 n

lemma sum_sFiniteSeq (μ : Measure α) [h : SFinite μ] : sum (sFiniteSeq μ) = μ :=
  h.1.choose_spec.2.symm

/-- A countable sum of finite measures is s-finite.
This lemma is superseeded by the instance below. -/
lemma sfinite_sum_of_countable {ι : Type*} [Countable ι]
    (m : ι → Measure α) [∀ n, IsFiniteMeasure (m n)] : SFinite (Measure.sum m) := by
  classical
  obtain ⟨f, hf⟩ : ∃ f : ι → ℕ, Function.Injective f := Countable.exists_injective_nat ι
  refine ⟨_, fun n ↦ ?_, (sum_extend_zero hf m).symm⟩
  rcases em (n ∈ range f) with ⟨i, rfl⟩ | hn
  · rw [hf.extend_apply]
    infer_instance
  · rw [Function.extend_apply' _ _ _ hn, Pi.zero_apply]
    infer_instance

instance {ι : Type*} [Countable ι] (m : ι → Measure α) [∀ n, SFinite (m n)] :
    SFinite (Measure.sum m) := by
  change SFinite (Measure.sum (fun i ↦ m i))
  simp_rw [← sum_sFiniteSeq (m _), Measure.sum_sum]
  apply sfinite_sum_of_countable

end SFinite

/-- A measure `μ` is called σ-finite if there is a countable collection of sets
 `{ A i | i ∈ ℕ }` such that `μ (A i) < ∞` and `⋃ i, A i = s`. -/
class SigmaFinite {m0 : MeasurableSpace α} (μ : Measure α) : Prop where
  out' : Nonempty (μ.FiniteSpanningSetsIn univ)
#align measure_theory.sigma_finite MeasureTheory.SigmaFinite
#align measure_theory.sigma_finite.out' MeasureTheory.SigmaFinite.out'

theorem sigmaFinite_iff : SigmaFinite μ ↔ Nonempty (μ.FiniteSpanningSetsIn univ) :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
#align measure_theory.sigma_finite_iff MeasureTheory.sigmaFinite_iff

theorem SigmaFinite.out (h : SigmaFinite μ) : Nonempty (μ.FiniteSpanningSetsIn univ) :=
  h.1
#align measure_theory.sigma_finite.out MeasureTheory.SigmaFinite.out

/-- If `μ` is σ-finite it has finite spanning sets in the collection of all measurable sets. -/
def Measure.toFiniteSpanningSetsIn (μ : Measure α) [h : SigmaFinite μ] :
    μ.FiniteSpanningSetsIn { s | MeasurableSet s } where
  set n := toMeasurable μ (h.out.some.set n)
  set_mem n := measurableSet_toMeasurable _ _
  finite n := by
    rw [measure_toMeasurable]
    exact h.out.some.finite n
  spanning := eq_univ_of_subset (iUnion_mono fun n => subset_toMeasurable _ _) h.out.some.spanning
#align measure_theory.measure.to_finite_spanning_sets_in MeasureTheory.Measure.toFiniteSpanningSetsIn

/-- A noncomputable way to get a monotone collection of sets that span `univ` and have finite
  measure using `Classical.choose`. This definition satisfies monotonicity in addition to all other
  properties in `SigmaFinite`. -/
def spanningSets (μ : Measure α) [SigmaFinite μ] (i : ℕ) : Set α :=
  Accumulate μ.toFiniteSpanningSetsIn.set i
#align measure_theory.spanning_sets MeasureTheory.spanningSets

theorem monotone_spanningSets (μ : Measure α) [SigmaFinite μ] : Monotone (spanningSets μ) :=
  monotone_accumulate
#align measure_theory.monotone_spanning_sets MeasureTheory.monotone_spanningSets

theorem measurable_spanningSets (μ : Measure α) [SigmaFinite μ] (i : ℕ) :
    MeasurableSet (spanningSets μ i) :=
  MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ => μ.toFiniteSpanningSetsIn.set_mem j
#align measure_theory.measurable_spanning_sets MeasureTheory.measurable_spanningSets

theorem measure_spanningSets_lt_top (μ : Measure α) [SigmaFinite μ] (i : ℕ) :
    μ (spanningSets μ i) < ∞ :=
  measure_biUnion_lt_top (finite_le_nat i) fun j _ => (μ.toFiniteSpanningSetsIn.finite j).ne
#align measure_theory.measure_spanning_sets_lt_top MeasureTheory.measure_spanningSets_lt_top

theorem iUnion_spanningSets (μ : Measure α) [SigmaFinite μ] : ⋃ i : ℕ, spanningSets μ i = univ :=
  by simp_rw [spanningSets, iUnion_accumulate, μ.toFiniteSpanningSetsIn.spanning]
#align measure_theory.Union_spanning_sets MeasureTheory.iUnion_spanningSets

theorem isCountablySpanning_spanningSets (μ : Measure α) [SigmaFinite μ] :
    IsCountablySpanning (range (spanningSets μ)) :=
  ⟨spanningSets μ, mem_range_self, iUnion_spanningSets μ⟩
#align measure_theory.is_countably_spanning_spanning_sets MeasureTheory.isCountablySpanning_spanningSets

open scoped Classical in
/-- `spanningSetsIndex μ x` is the least `n : ℕ` such that `x ∈ spanningSets μ n`. -/
noncomputable def spanningSetsIndex (μ : Measure α) [SigmaFinite μ] (x : α) : ℕ :=
  Nat.find <| iUnion_eq_univ_iff.1 (iUnion_spanningSets μ) x
#align measure_theory.spanning_sets_index MeasureTheory.spanningSetsIndex

open scoped Classical in
theorem measurable_spanningSetsIndex (μ : Measure α) [SigmaFinite μ] :
    Measurable (spanningSetsIndex μ) :=
  measurable_find _ <| measurable_spanningSets μ
#align measure_theory.measurable_spanning_sets_index MeasureTheory.measurable_spanningSetsIndex

open scoped Classical in
theorem preimage_spanningSetsIndex_singleton (μ : Measure α) [SigmaFinite μ] (n : ℕ) :
    spanningSetsIndex μ ⁻¹' {n} = disjointed (spanningSets μ) n :=
  preimage_find_eq_disjointed _ _ _
#align measure_theory.preimage_spanning_sets_index_singleton MeasureTheory.preimage_spanningSetsIndex_singleton

theorem spanningSetsIndex_eq_iff (μ : Measure α) [SigmaFinite μ] {x : α} {n : ℕ} :
    spanningSetsIndex μ x = n ↔ x ∈ disjointed (spanningSets μ) n := by
  convert Set.ext_iff.1 (preimage_spanningSetsIndex_singleton μ n) x
#align measure_theory.spanning_sets_index_eq_iff MeasureTheory.spanningSetsIndex_eq_iff

theorem mem_disjointed_spanningSetsIndex (μ : Measure α) [SigmaFinite μ] (x : α) :
    x ∈ disjointed (spanningSets μ) (spanningSetsIndex μ x) :=
  (spanningSetsIndex_eq_iff μ).1 rfl
#align measure_theory.mem_disjointed_spanning_sets_index MeasureTheory.mem_disjointed_spanningSetsIndex

theorem mem_spanningSetsIndex (μ : Measure α) [SigmaFinite μ] (x : α) :
    x ∈ spanningSets μ (spanningSetsIndex μ x) :=
  disjointed_subset _ _ (mem_disjointed_spanningSetsIndex μ x)
#align measure_theory.mem_spanning_sets_index MeasureTheory.mem_spanningSetsIndex

theorem mem_spanningSets_of_index_le (μ : Measure α) [SigmaFinite μ] (x : α) {n : ℕ}
    (hn : spanningSetsIndex μ x ≤ n) : x ∈ spanningSets μ n :=
  monotone_spanningSets μ hn (mem_spanningSetsIndex μ x)
#align measure_theory.mem_spanning_sets_of_index_le MeasureTheory.mem_spanningSets_of_index_le

theorem eventually_mem_spanningSets (μ : Measure α) [SigmaFinite μ] (x : α) :
    ∀ᶠ n in atTop, x ∈ spanningSets μ n :=
  eventually_atTop.2 ⟨spanningSetsIndex μ x, fun _ => mem_spanningSets_of_index_le μ x⟩
#align measure_theory.eventually_mem_spanning_sets MeasureTheory.eventually_mem_spanningSets

theorem sum_restrict_disjointed_spanningSets (μ : Measure α) [SigmaFinite μ] :
    sum (fun n ↦ μ.restrict (disjointed (spanningSets μ) n)) = μ := by
  rw [← restrict_iUnion (disjoint_disjointed _)
      (MeasurableSet.disjointed (measurable_spanningSets _)),
    iUnion_disjointed, iUnion_spanningSets, restrict_univ]

instance (priority := 100) [SigmaFinite μ] : SFinite μ := by
  have : ∀ n, Fact (μ (disjointed (spanningSets μ) n) < ∞) :=
    fun n ↦ ⟨(measure_mono (disjointed_subset _ _)).trans_lt (measure_spanningSets_lt_top μ n)⟩
  exact ⟨⟨fun n ↦ μ.restrict (disjointed (spanningSets μ) n), fun n ↦ by infer_instance,
    (sum_restrict_disjointed_spanningSets μ).symm⟩⟩

namespace Measure

theorem iSup_restrict_spanningSets [SigmaFinite μ] (hs : MeasurableSet s) :
    ⨆ i, μ.restrict (spanningSets μ i) s = μ s :=
  calc
    ⨆ i, μ.restrict (spanningSets μ i) s = μ.restrict (⋃ i, spanningSets μ i) s :=
      (restrict_iUnion_apply_eq_iSup (monotone_spanningSets μ).directed_le hs).symm
    _ = μ s := by rw [iUnion_spanningSets, restrict_univ]
#align measure_theory.measure.supr_restrict_spanning_sets MeasureTheory.Measure.iSup_restrict_spanningSets

/-- In a σ-finite space, any measurable set of measure `> r` contains a measurable subset of
finite measure `> r`. -/
theorem exists_subset_measure_lt_top [SigmaFinite μ] {r : ℝ≥0∞} (hs : MeasurableSet s)
    (h's : r < μ s) : ∃ t, MeasurableSet t ∧ t ⊆ s ∧ r < μ t ∧ μ t < ∞ := by
  rw [← iSup_restrict_spanningSets hs,
    @lt_iSup_iff _ _ _ r fun i : ℕ => μ.restrict (spanningSets μ i) s] at h's
  rcases h's with ⟨n, hn⟩
  simp only [restrict_apply hs] at hn
  refine'
    ⟨s ∩ spanningSets μ n, hs.inter (measurable_spanningSets _ _), inter_subset_left _ _, hn, _⟩
  exact (measure_mono (inter_subset_right _ _)).trans_lt (measure_spanningSets_lt_top _ _)
#align measure_theory.measure.exists_subset_measure_lt_top MeasureTheory.Measure.exists_subset_measure_lt_top

/-- A set in a σ-finite space has zero measure if and only if its intersection with
all members of the countable family of finite measure spanning sets has zero measure. -/
theorem forall_measure_inter_spanningSets_eq_zero [MeasurableSpace α] {μ : Measure α}
    [SigmaFinite μ] (s : Set α) : (∀ n, μ (s ∩ spanningSets μ n) = 0) ↔ μ s = 0 := by
  nth_rw 2 [show s = ⋃ n, s ∩ spanningSets μ n by
      rw [← inter_iUnion, iUnion_spanningSets, inter_univ] ]
  rw [measure_iUnion_null_iff]
#align measure_theory.measure.forall_measure_inter_spanning_sets_eq_zero MeasureTheory.Measure.forall_measure_inter_spanningSets_eq_zero

/-- A set in a σ-finite space has positive measure if and only if its intersection with
some member of the countable family of finite measure spanning sets has positive measure. -/
theorem exists_measure_inter_spanningSets_pos [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
    (s : Set α) : (∃ n, 0 < μ (s ∩ spanningSets μ n)) ↔ 0 < μ s := by
  rw [← not_iff_not]
  simp only [not_exists, not_lt, nonpos_iff_eq_zero]
  exact forall_measure_inter_spanningSets_eq_zero s
#align measure_theory.measure.exists_measure_inter_spanning_sets_pos MeasureTheory.Measure.exists_measure_inter_spanningSets_pos

/-- If the union of a.e.-disjoint null-measurable sets has finite measure, then there are only
finitely many members of the union whose measure exceeds any given positive number. -/
theorem finite_const_le_meas_of_disjoint_iUnion₀ {ι : Type*} [MeasurableSpace α] (μ : Measure α)
    {ε : ℝ≥0∞} (ε_pos : 0 < ε) {As : ι → Set α} (As_mble : ∀ i : ι, NullMeasurableSet (As i) μ)
    (As_disj : Pairwise (AEDisjoint μ on As)) (Union_As_finite : μ (⋃ i, As i) ≠ ∞) :
    Set.Finite { i : ι | ε ≤ μ (As i) } :=
  ENNReal.finite_const_le_of_tsum_ne_top
    (ne_top_of_le_ne_top Union_As_finite (tsum_meas_le_meas_iUnion_of_disjoint₀ μ As_mble As_disj))
    ε_pos.ne'

/-- If the union of disjoint measurable sets has finite measure, then there are only
finitely many members of the union whose measure exceeds any given positive number. -/
theorem finite_const_le_meas_of_disjoint_iUnion {ι : Type*} [MeasurableSpace α] (μ : Measure α)
    {ε : ℝ≥0∞} (ε_pos : 0 < ε) {As : ι → Set α} (As_mble : ∀ i : ι, MeasurableSet (As i))
    (As_disj : Pairwise (Disjoint on As)) (Union_As_finite : μ (⋃ i, As i) ≠ ∞) :
    Set.Finite { i : ι | ε ≤ μ (As i) } :=
  finite_const_le_meas_of_disjoint_iUnion₀ μ ε_pos (fun i ↦ (As_mble i).nullMeasurableSet)
    (fun _ _ h ↦ Disjoint.aedisjoint (As_disj h)) Union_As_finite
#align measure_theory.measure.finite_const_le_meas_of_disjoint_Union MeasureTheory.Measure.finite_const_le_meas_of_disjoint_iUnion

/-- If all elements of an infinite set have measure uniformly separated from zero,
then the set has infinite measure. -/
theorem _root_.Set.Infinite.meas_eq_top [MeasurableSingletonClass α]
    {s : Set α} (hs : s.Infinite) (h' : ∃ ε, ε ≠ 0 ∧ ∀ x ∈ s, ε ≤ μ {x}) : μ s = ∞ := top_unique <|
  let ⟨ε, hne, hε⟩ := h'; have := hs.to_subtype
  calc
    ∞ = ∑' _ : s, ε := (ENNReal.tsum_const_eq_top_of_ne_zero hne).symm
    _ ≤ ∑' x : s, μ {x.1} := ENNReal.tsum_le_tsum fun x ↦ hε x x.2
    _ ≤ μ (⋃ x : s, {x.1}) := tsum_meas_le_meas_iUnion_of_disjoint _
      (fun _ ↦ MeasurableSet.singleton _) fun x y hne ↦ by simpa [Subtype.val_inj]
    _ = μ s := by simp

/-- If the union of a.e.-disjoint null-measurable sets has finite measure, then there are only
countably many members of the union whose measure is positive. -/
theorem countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top₀ {ι : Type*} {_ : MeasurableSpace α}
    (μ : Measure α) {As : ι → Set α} (As_mble : ∀ i : ι, NullMeasurableSet (As i) μ)
    (As_disj : Pairwise (AEDisjoint μ on As)) (Union_As_finite : μ (⋃ i, As i) ≠ ∞) :
    Set.Countable { i : ι | 0 < μ (As i) } := by
  set posmeas := { i : ι | 0 < μ (As i) } with posmeas_def
  rcases exists_seq_strictAnti_tendsto' (zero_lt_one : (0 : ℝ≥0∞) < 1) with
    ⟨as, _, as_mem, as_lim⟩
  set fairmeas := fun n : ℕ => { i : ι | as n ≤ μ (As i) }
  have countable_union : posmeas = ⋃ n, fairmeas n := by
    have fairmeas_eq : ∀ n, fairmeas n = (fun i => μ (As i)) ⁻¹' Ici (as n) := fun n => by
      simp only [fairmeas]
      rfl
    simpa only [fairmeas_eq, posmeas_def, ← preimage_iUnion,
      iUnion_Ici_eq_Ioi_of_lt_of_tendsto (0 : ℝ≥0∞) (fun n => (as_mem n).1) as_lim]
  rw [countable_union]
  refine' countable_iUnion fun n => Finite.countable _
  exact finite_const_le_meas_of_disjoint_iUnion₀ μ (as_mem n).1 As_mble As_disj Union_As_finite

/-- If the union of disjoint measurable sets has finite measure, then there are only
countably many members of the union whose measure is positive. -/
theorem countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top {ι : Type*} {_ : MeasurableSpace α}
    (μ : Measure α) {As : ι → Set α} (As_mble : ∀ i : ι, MeasurableSet (As i))
    (As_disj : Pairwise (Disjoint on As)) (Union_As_finite : μ (⋃ i, As i) ≠ ∞) :
    Set.Countable { i : ι | 0 < μ (As i) } :=
  countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top₀ μ (fun i ↦ (As_mble i).nullMeasurableSet)
    ((fun _ _ h ↦ Disjoint.aedisjoint (As_disj h))) Union_As_finite
#align measure_theory.measure.countable_meas_pos_of_disjoint_of_meas_Union_ne_top MeasureTheory.Measure.countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top

/-- In an s-finite space, among disjoint null-measurable sets, only countably many can have positive
measure. -/
theorem countable_meas_pos_of_disjoint_iUnion₀ {ι : Type*} { _ : MeasurableSpace α} {μ : Measure α}
    [SFinite μ] {As : ι → Set α} (As_mble : ∀ i : ι, NullMeasurableSet (As i) μ)
    (As_disj : Pairwise (AEDisjoint μ on As)) :
    Set.Countable { i : ι | 0 < μ (As i) } := by
  rw [← sum_sFiniteSeq μ] at As_disj As_mble ⊢
  have obs : { i : ι | 0 < sum (sFiniteSeq μ) (As i) }
      ⊆ ⋃ n, { i : ι | 0 < sFiniteSeq μ n (As i) } := by
    intro i hi
    by_contra con
    simp only [mem_iUnion, mem_setOf_eq, not_exists, not_lt, nonpos_iff_eq_zero] at *
    rw [sum_apply₀] at hi
    · simp_rw [con] at hi
      simp at hi
    · exact As_mble i
  apply Countable.mono obs
  refine countable_iUnion fun n ↦ ?_
  apply countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top₀
  · exact fun i ↦ (As_mble i).mono (le_sum _ _)
  · exact fun i j hij ↦ AEDisjoint.of_le (As_disj hij) (le_sum _ _)
  · exact measure_ne_top _ (⋃ i, As i)

/-- In an s-finite space, among disjoint measurable sets, only countably many can have positive
measure. -/
theorem countable_meas_pos_of_disjoint_iUnion {ι : Type*} {_ : MeasurableSpace α} {μ : Measure α}
    [SFinite μ] {As : ι → Set α} (As_mble : ∀ i : ι, MeasurableSet (As i))
    (As_disj : Pairwise (Disjoint on As)) : Set.Countable { i : ι | 0 < μ (As i) } :=
  countable_meas_pos_of_disjoint_iUnion₀ (fun i ↦ (As_mble i).nullMeasurableSet)
    ((fun _ _ h ↦ Disjoint.aedisjoint (As_disj h)))
#align measure_theory.measure.countable_meas_pos_of_disjoint_Union MeasureTheory.Measure.countable_meas_pos_of_disjoint_iUnion

theorem countable_meas_level_set_pos₀ {α β : Type*} {_ : MeasurableSpace α} {μ : Measure α}
    [SFinite μ] [MeasurableSpace β] [MeasurableSingletonClass β] {g : α → β}
    (g_mble : NullMeasurable g μ) : Set.Countable { t : β | 0 < μ { a : α | g a = t } } := by
  have level_sets_disjoint : Pairwise (Disjoint on fun t : β => { a : α | g a = t }) :=
    fun s t hst => Disjoint.preimage g (disjoint_singleton.mpr hst)
  exact Measure.countable_meas_pos_of_disjoint_iUnion₀
    (fun b => g_mble (‹MeasurableSingletonClass β›.measurableSet_singleton b))
    ((fun _ _ h ↦ Disjoint.aedisjoint (level_sets_disjoint h)))

theorem countable_meas_level_set_pos {α β : Type*} {_ : MeasurableSpace α} {μ : Measure α}
    [SFinite μ] [MeasurableSpace β] [MeasurableSingletonClass β] {g : α → β}
    (g_mble : Measurable g) : Set.Countable { t : β | 0 < μ { a : α | g a = t } } :=
  countable_meas_level_set_pos₀ g_mble.nullMeasurable
#align measure_theory.measure.countable_meas_level_set_pos MeasureTheory.Measure.countable_meas_level_set_pos

/-- If a measure `μ` is the sum of a countable family `mₙ`, and a set `t` has finite measure for
each `mₙ`, then its measurable superset `toMeasurable μ t` (which has the same measure as `t`)
satisfies, for any measurable set `s`, the equality `μ (toMeasurable μ t ∩ s) = μ (t ∩ s)`. -/
theorem measure_toMeasurable_inter_of_sum {s : Set α} (hs : MeasurableSet s) {t : Set α}
    {m : ℕ → Measure α} (hv : ∀ n, m n t ≠ ∞) (hμ : μ = sum m) :
    μ (toMeasurable μ t ∩ s) = μ (t ∩ s) := by
  -- we show that there is a measurable superset of `t` satisfying the conclusion for any
  -- measurable set `s`. It is built for each measure `mₙ` using `toMeasurable`
  -- (which is well behaved for finite measure sets thanks to `measure_toMeasurable_inter`), and
  -- then taking the intersection over `n`.
  have A : ∃ t', t' ⊇ t ∧ MeasurableSet t' ∧ ∀ u, MeasurableSet u → μ (t' ∩ u) = μ (t ∩ u) := by
    let w n := toMeasurable (m n) t
    have T : t ⊆ ⋂ n, w n := subset_iInter (fun i ↦ subset_toMeasurable (m i) t)
    have M : MeasurableSet (⋂ n, w n) :=
      MeasurableSet.iInter (fun i ↦ measurableSet_toMeasurable (m i) t)
    refine ⟨⋂ n, w n, T, M, fun u hu ↦ ?_⟩
    refine le_antisymm ?_ (measure_mono (inter_subset_inter_left _ T))
    rw [hμ, sum_apply _ (M.inter hu)]
    apply le_trans _ (le_sum_apply _ _)
    apply ENNReal.tsum_le_tsum (fun i ↦ ?_)
    calc
    m i ((⋂ n, w n) ∩ u) ≤ m i (w i ∩ u) :=
      measure_mono (inter_subset_inter_left _ (iInter_subset _ _))
    _ = m i (t ∩ u) := measure_toMeasurable_inter hu (hv i)
  -- thanks to the definition of `toMeasurable`, the previous property will also be shared
  -- by `toMeasurable μ t`, which is enough to conclude the proof.
  rw [toMeasurable]
  split_ifs with ht
  · apply measure_congr
    exact ae_eq_set_inter ht.choose_spec.2.2 (ae_eq_refl _)
  · exact A.choose_spec.2.2 s hs

/-- If a set `t` is covered by a countable family of finite measure sets, then its measurable
superset `toMeasurable μ t` (which has the same measure as `t`) satisfies,
for any measurable set `s`, the equality `μ (toMeasurable μ t ∩ s) = μ (t ∩ s)`. -/
theorem measure_toMeasurable_inter_of_cover {s : Set α} (hs : MeasurableSet s) {t : Set α}
    {v : ℕ → Set α} (hv : t ⊆ ⋃ n, v n) (h'v : ∀ n, μ (t ∩ v n) ≠ ∞) :
    μ (toMeasurable μ t ∩ s) = μ (t ∩ s) := by
  -- we show that there is a measurable superset of `t` satisfying the conclusion for any
  -- measurable set `s`. It is built on each member of a spanning family using `toMeasurable`
  -- (which is well behaved for finite measure sets thanks to `measure_toMeasurable_inter`), and
  -- the desired property passes to the union.
  have A : ∃ t', t' ⊇ t ∧ MeasurableSet t' ∧ ∀ u, MeasurableSet u → μ (t' ∩ u) = μ (t ∩ u) := by
    let w n := toMeasurable μ (t ∩ v n)
    have hw : ∀ n, μ (w n) < ∞ := by
      intro n
      simp_rw [w, measure_toMeasurable]
      exact (h'v n).lt_top
    set t' := ⋃ n, toMeasurable μ (t ∩ disjointed w n) with ht'
    have tt' : t ⊆ t' :=
      calc
        t ⊆ ⋃ n, t ∩ disjointed w n := by
          rw [← inter_iUnion, iUnion_disjointed, inter_iUnion]
          intro x hx
          rcases mem_iUnion.1 (hv hx) with ⟨n, hn⟩
          refine' mem_iUnion.2 ⟨n, _⟩
          have : x ∈ t ∩ v n := ⟨hx, hn⟩
          exact ⟨hx, subset_toMeasurable μ _ this⟩
        _ ⊆ ⋃ n, toMeasurable μ (t ∩ disjointed w n) :=
          iUnion_mono fun n => subset_toMeasurable _ _
    refine' ⟨t', tt', MeasurableSet.iUnion fun n => measurableSet_toMeasurable μ _, fun u hu => _⟩
    apply le_antisymm _ (measure_mono (inter_subset_inter tt' Subset.rfl))
    calc
      μ (t' ∩ u) ≤ ∑' n, μ (toMeasurable μ (t ∩ disjointed w n) ∩ u) := by
        rw [ht', iUnion_inter]
        exact measure_iUnion_le _
      _ = ∑' n, μ (t ∩ disjointed w n ∩ u) := by
        congr 1
        ext1 n
        apply measure_toMeasurable_inter hu
        apply ne_of_lt
        calc
          μ (t ∩ disjointed w n) ≤ μ (t ∩ w n) :=
            measure_mono (inter_subset_inter_right _ (disjointed_le w n))
          _ ≤ μ (w n) := (measure_mono (inter_subset_right _ _))
          _ < ∞ := hw n
      _ = ∑' n, μ.restrict (t ∩ u) (disjointed w n) := by
        congr 1
        ext1 n
        rw [restrict_apply, inter_comm t _, inter_assoc]
        refine MeasurableSet.disjointed (fun n => ?_) n
        exact measurableSet_toMeasurable _ _
      _ = μ.restrict (t ∩ u) (⋃ n, disjointed w n) := by
        rw [measure_iUnion]
        · exact disjoint_disjointed _
        · intro i
          refine MeasurableSet.disjointed (fun n => ?_) i
          exact measurableSet_toMeasurable _ _
      _ ≤ μ.restrict (t ∩ u) univ := (measure_mono (subset_univ _))
      _ = μ (t ∩ u) := by rw [restrict_apply MeasurableSet.univ, univ_inter]
  -- thanks to the definition of `toMeasurable`, the previous property will also be shared
  -- by `toMeasurable μ t`, which is enough to conclude the proof.
  rw [toMeasurable]
  split_ifs with ht
  · apply measure_congr
    exact ae_eq_set_inter ht.choose_spec.2.2 (ae_eq_refl _)
  · exact A.choose_spec.2.2 s hs
#align measure_theory.measure.measure_to_measurable_inter_of_cover MeasureTheory.Measure.measure_toMeasurable_inter_of_cover

theorem restrict_toMeasurable_of_cover {s : Set α} {v : ℕ → Set α} (hv : s ⊆ ⋃ n, v n)
    (h'v : ∀ n, μ (s ∩ v n) ≠ ∞) : μ.restrict (toMeasurable μ s) = μ.restrict s :=
  ext fun t ht => by
    simp only [restrict_apply ht, inter_comm t, measure_toMeasurable_inter_of_cover ht hv h'v]
#align measure_theory.measure.restrict_to_measurable_of_cover MeasureTheory.Measure.restrict_toMeasurable_of_cover

/-- The measurable superset `toMeasurable μ t` of `t` (which has the same measure as `t`)
satisfies, for any measurable set `s`, the equality `μ (toMeasurable μ t ∩ s) = μ (t ∩ s)`.
This only holds when `μ` is s-finite -- for example for σ-finite measures. For a version without
this assumption (but requiring that `t` has finite measure), see `measure_toMeasurable_inter`. -/
theorem measure_toMeasurable_inter_of_sFinite [SFinite μ] {s : Set α} (hs : MeasurableSet s)
    (t : Set α) : μ (toMeasurable μ t ∩ s) = μ (t ∩ s) :=
  measure_toMeasurable_inter_of_sum hs (fun _ ↦ measure_ne_top _ t) (sum_sFiniteSeq μ).symm
#align measure_theory.measure.measure_to_measurable_inter_of_sigma_finite MeasureTheory.Measure.measure_toMeasurable_inter_of_sFinite

@[simp]
theorem restrict_toMeasurable_of_sFinite [SFinite μ] (s : Set α) :
    μ.restrict (toMeasurable μ s) = μ.restrict s :=
  ext fun t ht => by
    rw [restrict_apply ht, inter_comm t, measure_toMeasurable_inter_of_sFinite ht,
      restrict_apply ht, inter_comm t]
#align measure_theory.measure.restrict_to_measurable_of_sigma_finite MeasureTheory.Measure.restrict_toMeasurable_of_sFinite

namespace FiniteSpanningSetsIn

variable {C D : Set (Set α)}

/-- If `μ` has finite spanning sets in `C` and `C ∩ {s | μ s < ∞} ⊆ D` then `μ` has finite spanning
sets in `D`. -/
protected def mono' (h : μ.FiniteSpanningSetsIn C) (hC : C ∩ { s | μ s < ∞ } ⊆ D) :
    μ.FiniteSpanningSetsIn D :=
  ⟨h.set, fun i => hC ⟨h.set_mem i, h.finite i⟩, h.finite, h.spanning⟩
#align measure_theory.measure.finite_spanning_sets_in.mono' MeasureTheory.Measure.FiniteSpanningSetsIn.mono'

/-- If `μ` has finite spanning sets in `C` and `C ⊆ D` then `μ` has finite spanning sets in `D`. -/
protected def mono (h : μ.FiniteSpanningSetsIn C) (hC : C ⊆ D) : μ.FiniteSpanningSetsIn D :=
  h.mono' fun _s hs => hC hs.1
#align measure_theory.measure.finite_spanning_sets_in.mono MeasureTheory.Measure.FiniteSpanningSetsIn.mono

/-- If `μ` has finite spanning sets in the collection of measurable sets `C`, then `μ` is σ-finite.
-/
protected theorem sigmaFinite (h : μ.FiniteSpanningSetsIn C) : SigmaFinite μ :=
  ⟨⟨h.mono <| subset_univ C⟩⟩
#align measure_theory.measure.finite_spanning_sets_in.sigma_finite MeasureTheory.Measure.FiniteSpanningSetsIn.sigmaFinite

/-- An extensionality for measures. It is `ext_of_generateFrom_of_iUnion` formulated in terms of
`FiniteSpanningSetsIn`. -/
protected theorem ext {ν : Measure α} {C : Set (Set α)} (hA : ‹_› = generateFrom C)
    (hC : IsPiSystem C) (h : μ.FiniteSpanningSetsIn C) (h_eq : ∀ s ∈ C, μ s = ν s) : μ = ν :=
  ext_of_generateFrom_of_iUnion C _ hA hC h.spanning h.set_mem (fun i => (h.finite i).ne) h_eq
#align measure_theory.measure.finite_spanning_sets_in.ext MeasureTheory.Measure.FiniteSpanningSetsIn.ext

protected theorem isCountablySpanning (h : μ.FiniteSpanningSetsIn C) : IsCountablySpanning C :=
  ⟨h.set, h.set_mem, h.spanning⟩
#align measure_theory.measure.finite_spanning_sets_in.is_countably_spanning MeasureTheory.Measure.FiniteSpanningSetsIn.isCountablySpanning

end FiniteSpanningSetsIn

theorem sigmaFinite_of_countable {S : Set (Set α)} (hc : S.Countable) (hμ : ∀ s ∈ S, μ s < ∞)
    (hU : ⋃₀ S = univ) : SigmaFinite μ := by
  obtain ⟨s, hμ, hs⟩ : ∃ s : ℕ → Set α, (∀ n, μ (s n) < ∞) ∧ ⋃ n, s n = univ
  exact (@exists_seq_cover_iff_countable _ (fun x => μ x < ∞) ⟨∅, by simp⟩).2 ⟨S, hc, hμ, hU⟩
  exact ⟨⟨⟨fun n => s n, fun _ => trivial, hμ, hs⟩⟩⟩
#align measure_theory.measure.sigma_finite_of_countable MeasureTheory.Measure.sigmaFinite_of_countable

/-- Given measures `μ`, `ν` where `ν ≤ μ`, `FiniteSpanningSetsIn.ofLe` provides the induced
`FiniteSpanningSet` with respect to `ν` from a `FiniteSpanningSet` with respect to `μ`. -/
def FiniteSpanningSetsIn.ofLE (h : ν ≤ μ) {C : Set (Set α)} (S : μ.FiniteSpanningSetsIn C) :
    ν.FiniteSpanningSetsIn C where
  set := S.set
  set_mem := S.set_mem
  finite n := lt_of_le_of_lt (le_iff'.1 h _) (S.finite n)
  spanning := S.spanning
#align measure_theory.measure.finite_spanning_sets_in.of_le MeasureTheory.Measure.FiniteSpanningSetsIn.ofLE

theorem sigmaFinite_of_le (μ : Measure α) [hs : SigmaFinite μ] (h : ν ≤ μ) : SigmaFinite ν :=
  ⟨hs.out.map <| FiniteSpanningSetsIn.ofLE h⟩
#align measure_theory.measure.sigma_finite_of_le MeasureTheory.Measure.sigmaFinite_of_le

@[simp] lemma add_right_inj (μ ν₁ ν₂ : Measure α) [SigmaFinite μ] :
    μ + ν₁ = μ + ν₂ ↔ ν₁ = ν₂ := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]⟩
  rw [ext_iff_of_iUnion_eq_univ (iUnion_spanningSets μ)]
  intro i
  ext s hs
  rw [← ENNReal.add_right_inj (measure_mono (inter_subset_right s _) |>.trans_lt <|
    measure_spanningSets_lt_top μ i).ne]
  simp only [ext_iff', add_toOuterMeasure, OuterMeasure.coe_add, Pi.add_apply] at h
  simp [hs, h]

@[simp] lemma add_left_inj (μ ν₁ ν₂ : Measure α) [SigmaFinite μ] :
    ν₁ + μ = ν₂ + μ ↔ ν₁ = ν₂ := by rw [add_comm _ μ, add_comm _ μ, μ.add_right_inj]

end Measure

/-- Every finite measure is σ-finite. -/
instance (priority := 100) IsFiniteMeasure.toSigmaFinite {_m0 : MeasurableSpace α} (μ : Measure α)
    [IsFiniteMeasure μ] : SigmaFinite μ :=
  ⟨⟨⟨fun _ => univ, fun _ => trivial, fun _ => measure_lt_top μ _, iUnion_const _⟩⟩⟩
#align measure_theory.is_finite_measure.to_sigma_finite MeasureTheory.IsFiniteMeasure.toSigmaFinite

theorem sigmaFinite_bot_iff (μ : @Measure α ⊥) : SigmaFinite μ ↔ IsFiniteMeasure μ := by
  refine'
    ⟨fun h => ⟨_⟩, fun h => by
      haveI := h
      infer_instance⟩
  haveI : SigmaFinite μ := h
  let s := spanningSets μ
  have hs_univ : ⋃ i, s i = Set.univ := iUnion_spanningSets μ
  have hs_meas : ∀ i, MeasurableSet[⊥] (s i) := measurable_spanningSets μ
  simp_rw [MeasurableSpace.measurableSet_bot_iff] at hs_meas
  by_cases h_univ_empty : (Set.univ : Set α) = ∅
  · rw [h_univ_empty, @measure_empty α ⊥]
    exact ENNReal.zero_ne_top.lt_top
  obtain ⟨i, hsi⟩ : ∃ i, s i = Set.univ := by
    by_contra! h_not_univ
    have h_empty : ∀ i, s i = ∅ := by simpa [h_not_univ] using hs_meas
    simp only [h_empty, iUnion_empty] at hs_univ
    exact h_univ_empty hs_univ.symm
  rw [← hsi]
  exact measure_spanningSets_lt_top μ i
#align measure_theory.sigma_finite_bot_iff MeasureTheory.sigmaFinite_bot_iff

instance Restrict.sigmaFinite (μ : Measure α) [SigmaFinite μ] (s : Set α) :
    SigmaFinite (μ.restrict s) := by
  refine' ⟨⟨⟨spanningSets μ, fun _ => trivial, fun i => _, iUnion_spanningSets μ⟩⟩⟩
  rw [Measure.restrict_apply (measurable_spanningSets μ i)]
  exact (measure_mono <| inter_subset_left _ _).trans_lt (measure_spanningSets_lt_top μ i)
#align measure_theory.restrict.sigma_finite MeasureTheory.Restrict.sigmaFinite

instance sum.sigmaFinite {ι} [Finite ι] (μ : ι → Measure α) [∀ i, SigmaFinite (μ i)] :
    SigmaFinite (sum μ) := by
  cases nonempty_fintype ι
  have : ∀ n, MeasurableSet (⋂ i : ι, spanningSets (μ i) n) := fun n =>
    MeasurableSet.iInter fun i => measurable_spanningSets (μ i) n
  refine' ⟨⟨⟨fun n => ⋂ i, spanningSets (μ i) n, fun _ => trivial, fun n => _, _⟩⟩⟩
  · rw [sum_apply _ (this n), tsum_fintype, ENNReal.sum_lt_top_iff]
    rintro i -
    exact (measure_mono <| iInter_subset _ i).trans_lt (measure_spanningSets_lt_top (μ i) n)
  · rw [iUnion_iInter_of_monotone]
    simp_rw [iUnion_spanningSets, iInter_univ]
    exact fun i => monotone_spanningSets (μ i)
#align measure_theory.sum.sigma_finite MeasureTheory.sum.sigmaFinite

instance Add.sigmaFinite (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    SigmaFinite (μ + ν) := by
  rw [← sum_cond]
  refine' @sum.sigmaFinite _ _ _ _ _ (Bool.rec _ _) <;> simpa
#align measure_theory.add.sigma_finite MeasureTheory.Add.sigmaFinite

instance SMul.sigmaFinite {μ : Measure α} [SigmaFinite μ] (c : ℝ≥0) :
    MeasureTheory.SigmaFinite (c • μ) where
  out' :=
  ⟨{  set := spanningSets μ
      set_mem := fun _ ↦ trivial
      finite := by
        intro i
        simp only [smul_toOuterMeasure, OuterMeasure.coe_smul, Pi.smul_apply,
          nnreal_smul_coe_apply]
        exact ENNReal.mul_lt_top ENNReal.coe_ne_top (measure_spanningSets_lt_top μ i).ne
      spanning := iUnion_spanningSets μ }⟩

theorem SigmaFinite.of_map (μ : Measure α) {f : α → β} (hf : AEMeasurable f μ)
    (h : SigmaFinite (μ.map f)) : SigmaFinite μ :=
  ⟨⟨⟨fun n => f ⁻¹' spanningSets (μ.map f) n, fun _ => trivial, fun n => by
        simp only [← map_apply_of_aemeasurable hf, measurable_spanningSets,
          measure_spanningSets_lt_top],
        by rw [← preimage_iUnion, iUnion_spanningSets, preimage_univ]⟩⟩⟩
#align measure_theory.sigma_finite.of_map MeasureTheory.SigmaFinite.of_map

theorem _root_.MeasurableEquiv.sigmaFinite_map {μ : Measure α} (f : α ≃ᵐ β) (h : SigmaFinite μ) :
    SigmaFinite (μ.map f) := by
  refine' SigmaFinite.of_map _ f.symm.measurable.aemeasurable _
  rwa [map_map f.symm.measurable f.measurable, f.symm_comp_self, Measure.map_id]
#align measurable_equiv.sigma_finite_map MeasurableEquiv.sigmaFinite_map

/-- Similar to `ae_of_forall_measure_lt_top_ae_restrict`, but where you additionally get the
  hypothesis that another σ-finite measure has finite values on `s`. -/
theorem ae_of_forall_measure_lt_top_ae_restrict' {μ : Measure α} (ν : Measure α) [SigmaFinite μ]
    [SigmaFinite ν] (P : α → Prop)
    (h : ∀ s, MeasurableSet s → μ s < ∞ → ν s < ∞ → ∀ᵐ x ∂μ.restrict s, P x) : ∀ᵐ x ∂μ, P x := by
  have : ∀ n, ∀ᵐ x ∂μ, x ∈ spanningSets (μ + ν) n → P x := by
    intro n
    have := h
      (spanningSets (μ + ν) n) (measurable_spanningSets _ _)
      ((self_le_add_right _ _).trans_lt (measure_spanningSets_lt_top (μ + ν) _))
      ((self_le_add_left _ _).trans_lt (measure_spanningSets_lt_top (μ + ν) _))
    exact (ae_restrict_iff' (measurable_spanningSets _ _)).mp this
  filter_upwards [ae_all_iff.2 this] with _ hx using hx _ (mem_spanningSetsIndex _ _)
#align measure_theory.ae_of_forall_measure_lt_top_ae_restrict' MeasureTheory.ae_of_forall_measure_lt_top_ae_restrict'

/-- To prove something for almost all `x` w.r.t. a σ-finite measure, it is sufficient to show that
  this holds almost everywhere in sets where the measure has finite value. -/
theorem ae_of_forall_measure_lt_top_ae_restrict {μ : Measure α} [SigmaFinite μ] (P : α → Prop)
    (h : ∀ s, MeasurableSet s → μ s < ∞ → ∀ᵐ x ∂μ.restrict s, P x) : ∀ᵐ x ∂μ, P x :=
  ae_of_forall_measure_lt_top_ae_restrict' μ P fun s hs h2s _ => h s hs h2s
#align measure_theory.ae_of_forall_measure_lt_top_ae_restrict MeasureTheory.ae_of_forall_measure_lt_top_ae_restrict

/-- A measure is called locally finite if it is finite in some neighborhood of each point. -/
class IsLocallyFiniteMeasure [TopologicalSpace α] (μ : Measure α) : Prop where
  finiteAtNhds : ∀ x, μ.FiniteAtFilter (𝓝 x)
#align measure_theory.is_locally_finite_measure MeasureTheory.IsLocallyFiniteMeasure
#align measure_theory.is_locally_finite_measure.finite_at_nhds MeasureTheory.IsLocallyFiniteMeasure.finiteAtNhds

-- see Note [lower instance priority]
instance (priority := 100) IsFiniteMeasure.toIsLocallyFiniteMeasure [TopologicalSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] : IsLocallyFiniteMeasure μ :=
  ⟨fun _ => finiteAtFilter_of_finite _ _⟩
#align measure_theory.is_finite_measure.to_is_locally_finite_measure MeasureTheory.IsFiniteMeasure.toIsLocallyFiniteMeasure

theorem Measure.finiteAt_nhds [TopologicalSpace α] (μ : Measure α) [IsLocallyFiniteMeasure μ]
    (x : α) : μ.FiniteAtFilter (𝓝 x) :=
  IsLocallyFiniteMeasure.finiteAtNhds x
#align measure_theory.measure.finite_at_nhds MeasureTheory.Measure.finiteAt_nhds

theorem Measure.smul_finite (μ : Measure α) [IsFiniteMeasure μ] {c : ℝ≥0∞} (hc : c ≠ ∞) :
    IsFiniteMeasure (c • μ) := by
  lift c to ℝ≥0 using hc
  exact MeasureTheory.isFiniteMeasureSMulNNReal
#align measure_theory.measure.smul_finite MeasureTheory.Measure.smul_finite

theorem Measure.exists_isOpen_measure_lt_top [TopologicalSpace α] (μ : Measure α)
    [IsLocallyFiniteMeasure μ] (x : α) : ∃ s : Set α, x ∈ s ∧ IsOpen s ∧ μ s < ∞ := by
  simpa only [and_assoc] using (μ.finiteAt_nhds x).exists_mem_basis (nhds_basis_opens x)
#align measure_theory.measure.exists_is_open_measure_lt_top MeasureTheory.Measure.exists_isOpen_measure_lt_top

instance isLocallyFiniteMeasureSMulNNReal [TopologicalSpace α] (μ : Measure α)
    [IsLocallyFiniteMeasure μ] (c : ℝ≥0) : IsLocallyFiniteMeasure (c • μ) := by
  refine' ⟨fun x => _⟩
  rcases μ.exists_isOpen_measure_lt_top x with ⟨o, xo, o_open, μo⟩
  refine' ⟨o, o_open.mem_nhds xo, _⟩
  apply ENNReal.mul_lt_top _ μo.ne
  simp
#align measure_theory.is_locally_finite_measure_smul_nnreal MeasureTheory.isLocallyFiniteMeasureSMulNNReal

protected theorem Measure.isTopologicalBasis_isOpen_lt_top [TopologicalSpace α]
    (μ : Measure α) [IsLocallyFiniteMeasure μ] :
    TopologicalSpace.IsTopologicalBasis { s | IsOpen s ∧ μ s < ∞ } := by
  refine' TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds (fun s hs => hs.1) _
  intro x s xs hs
  rcases μ.exists_isOpen_measure_lt_top x with ⟨v, xv, hv, μv⟩
  refine' ⟨v ∩ s, ⟨hv.inter hs, lt_of_le_of_lt _ μv⟩, ⟨xv, xs⟩, inter_subset_right _ _⟩
  exact measure_mono (inter_subset_left _ _)
#align measure_theory.measure.is_topological_basis_is_open_lt_top MeasureTheory.Measure.isTopologicalBasis_isOpen_lt_top

/-- A measure `μ` is finite on compacts if any compact set `K` satisfies `μ K < ∞`. -/
class IsFiniteMeasureOnCompacts [TopologicalSpace α] (μ : Measure α) : Prop where
  protected lt_top_of_isCompact : ∀ ⦃K : Set α⦄, IsCompact K → μ K < ∞
#align measure_theory.is_finite_measure_on_compacts MeasureTheory.IsFiniteMeasureOnCompacts
#align measure_theory.is_finite_measure_on_compacts.lt_top_of_is_compact MeasureTheory.IsFiniteMeasureOnCompacts.lt_top_of_isCompact

/-- A compact subset has finite measure for a measure which is finite on compacts. -/
theorem _root_.IsCompact.measure_lt_top [TopologicalSpace α] {μ : Measure α}
    [IsFiniteMeasureOnCompacts μ] ⦃K : Set α⦄ (hK : IsCompact K) : μ K < ∞ :=
  IsFiniteMeasureOnCompacts.lt_top_of_isCompact hK
#align is_compact.measure_lt_top IsCompact.measure_lt_top

/-- A compact subset has finite measure for a measure which is finite on compacts. -/
theorem _root_.IsCompact.measure_ne_top [TopologicalSpace α] {μ : Measure α}
    [IsFiniteMeasureOnCompacts μ] ⦃K : Set α⦄ (hK : IsCompact K) : μ K ≠ ∞ :=
  hK.measure_lt_top.ne

/-- A bounded subset has finite measure for a measure which is finite on compact sets, in a
proper space. -/
theorem _root_.Bornology.IsBounded.measure_lt_top [PseudoMetricSpace α] [ProperSpace α]
    {μ : Measure α} [IsFiniteMeasureOnCompacts μ] ⦃s : Set α⦄ (hs : Bornology.IsBounded s) :
    μ s < ∞ :=
  calc
    μ s ≤ μ (closure s) := measure_mono subset_closure
    _ < ∞ := (Metric.isCompact_of_isClosed_isBounded isClosed_closure hs.closure).measure_lt_top
#align metric.bounded.measure_lt_top Bornology.IsBounded.measure_lt_top

theorem measure_closedBall_lt_top [PseudoMetricSpace α] [ProperSpace α] {μ : Measure α}
    [IsFiniteMeasureOnCompacts μ] {x : α} {r : ℝ} : μ (Metric.closedBall x r) < ∞ :=
  Metric.isBounded_closedBall.measure_lt_top
#align measure_theory.measure_closed_ball_lt_top MeasureTheory.measure_closedBall_lt_top

theorem measure_ball_lt_top [PseudoMetricSpace α] [ProperSpace α] {μ : Measure α}
    [IsFiniteMeasureOnCompacts μ] {x : α} {r : ℝ} : μ (Metric.ball x r) < ∞ :=
  Metric.isBounded_ball.measure_lt_top
#align measure_theory.measure_ball_lt_top MeasureTheory.measure_ball_lt_top

protected theorem IsFiniteMeasureOnCompacts.smul [TopologicalSpace α] (μ : Measure α)
    [IsFiniteMeasureOnCompacts μ] {c : ℝ≥0∞} (hc : c ≠ ∞) : IsFiniteMeasureOnCompacts (c • μ) :=
  ⟨fun _K hK => ENNReal.mul_lt_top hc hK.measure_lt_top.ne⟩
#align measure_theory.is_finite_measure_on_compacts.smul MeasureTheory.IsFiniteMeasureOnCompacts.smul

instance IsFiniteMeasureOnCompacts.smul_nnreal [TopologicalSpace α] (μ : Measure α)
    [IsFiniteMeasureOnCompacts μ] (c : ℝ≥0) : IsFiniteMeasureOnCompacts (c • μ) :=
  IsFiniteMeasureOnCompacts.smul μ coe_ne_top

instance instIsFiniteMeasureOnCompactsRestrict [TopologicalSpace α] {μ : Measure α}
    [IsFiniteMeasureOnCompacts μ] {s : Set α} : IsFiniteMeasureOnCompacts (μ.restrict s) :=
  ⟨fun _k hk ↦ (restrict_apply_le _ _).trans_lt hk.measure_lt_top⟩

instance (priority := 100) CompactSpace.isFiniteMeasure [TopologicalSpace α] [CompactSpace α]
    [IsFiniteMeasureOnCompacts μ] : IsFiniteMeasure μ :=
  ⟨IsFiniteMeasureOnCompacts.lt_top_of_isCompact isCompact_univ⟩
#align measure_theory.compact_space.is_finite_measure MeasureTheory.CompactSpace.isFiniteMeasure

instance (priority := 100) SigmaFinite.of_isFiniteMeasureOnCompacts [TopologicalSpace α]
    [SigmaCompactSpace α] (μ : Measure α) [IsFiniteMeasureOnCompacts μ] : SigmaFinite μ :=
  ⟨⟨{   set := compactCovering α
        set_mem := fun _ => trivial
        finite := fun n => (isCompact_compactCovering α n).measure_lt_top
        spanning := iUnion_compactCovering α }⟩⟩

-- see Note [lower instance priority]
instance (priority := 100) sigmaFinite_of_locallyFinite [TopologicalSpace α]
    [SecondCountableTopology α] [IsLocallyFiniteMeasure μ] : SigmaFinite μ := by
  choose s hsx hsμ using μ.finiteAt_nhds
  rcases TopologicalSpace.countable_cover_nhds hsx with ⟨t, htc, htU⟩
  refine' Measure.sigmaFinite_of_countable (htc.image s) (forall_mem_image.2 fun x _ => hsμ x) _
  rwa [sUnion_image]
#align measure_theory.sigma_finite_of_locally_finite MeasureTheory.sigmaFinite_of_locallyFinite

/-- A measure which is finite on compact sets in a locally compact space is locally finite. -/
instance (priority := 100) isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts [TopologicalSpace α]
    [WeaklyLocallyCompactSpace α] [IsFiniteMeasureOnCompacts μ] : IsLocallyFiniteMeasure μ :=
  ⟨fun x ↦
    let ⟨K, K_compact, K_mem⟩ := exists_compact_mem_nhds x
    ⟨K, K_mem, K_compact.measure_lt_top⟩⟩
#align measure_theory.is_locally_finite_measure_of_is_finite_measure_on_compacts MeasureTheory.isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts

theorem exists_pos_measure_of_cover [Countable ι] {U : ι → Set α} (hU : ⋃ i, U i = univ)
    (hμ : μ ≠ 0) : ∃ i, 0 < μ (U i) := by
  contrapose! hμ with H
  rw [← measure_univ_eq_zero, ← hU]
  exact measure_iUnion_null fun i => nonpos_iff_eq_zero.1 (H i)
#align measure_theory.exists_pos_measure_of_cover MeasureTheory.exists_pos_measure_of_cover

theorem exists_pos_preimage_ball [PseudoMetricSpace δ] (f : α → δ) (x : δ) (hμ : μ ≠ 0) :
    ∃ n : ℕ, 0 < μ (f ⁻¹' Metric.ball x n) :=
  exists_pos_measure_of_cover (by rw [← preimage_iUnion, Metric.iUnion_ball_nat, preimage_univ]) hμ
#align measure_theory.exists_pos_preimage_ball MeasureTheory.exists_pos_preimage_ball

theorem exists_pos_ball [PseudoMetricSpace α] (x : α) (hμ : μ ≠ 0) :
    ∃ n : ℕ, 0 < μ (Metric.ball x n) :=
  exists_pos_preimage_ball id x hμ
#align measure_theory.exists_pos_ball MeasureTheory.exists_pos_ball

/-- If a set has zero measure in a neighborhood of each of its points, then it has zero measure
in a second-countable space. -/
theorem null_of_locally_null [TopologicalSpace α] [SecondCountableTopology α] (s : Set α)
    (hs : ∀ x ∈ s, ∃ u ∈ 𝓝[s] x, μ u = 0) : μ s = 0 :=
  μ.toOuterMeasure.null_of_locally_null s hs
#align measure_theory.null_of_locally_null MeasureTheory.null_of_locally_null

theorem exists_mem_forall_mem_nhdsWithin_pos_measure [TopologicalSpace α]
    [SecondCountableTopology α] {s : Set α} (hs : μ s ≠ 0) : ∃ x ∈ s, ∀ t ∈ 𝓝[s] x, 0 < μ t :=
  μ.toOuterMeasure.exists_mem_forall_mem_nhds_within_pos hs
#align measure_theory.exists_mem_forall_mem_nhds_within_pos_measure MeasureTheory.exists_mem_forall_mem_nhdsWithin_pos_measure

theorem exists_ne_forall_mem_nhds_pos_measure_preimage {β} [TopologicalSpace β] [T1Space β]
    [SecondCountableTopology β] [Nonempty β] {f : α → β} (h : ∀ b, ∃ᵐ x ∂μ, f x ≠ b) :
    ∃ a b : β, a ≠ b ∧ (∀ s ∈ 𝓝 a, 0 < μ (f ⁻¹' s)) ∧ ∀ t ∈ 𝓝 b, 0 < μ (f ⁻¹' t) := by
  -- We use an `OuterMeasure` so that the proof works without `Measurable f`
  set m : OuterMeasure β := OuterMeasure.map f μ.toOuterMeasure
  replace h : ∀ b : β, m {b}ᶜ ≠ 0 := fun b => not_eventually.mpr (h b)
  inhabit β
  have : m univ ≠ 0 := ne_bot_of_le_ne_bot (h default) (m.mono' <| subset_univ _)
  rcases m.exists_mem_forall_mem_nhds_within_pos this with ⟨b, -, hb⟩
  simp only [nhdsWithin_univ] at hb
  rcases m.exists_mem_forall_mem_nhds_within_pos (h b) with ⟨a, hab : a ≠ b, ha⟩
  simp only [isOpen_compl_singleton.nhdsWithin_eq hab] at ha
  exact ⟨a, b, hab, ha, hb⟩
#align measure_theory.exists_ne_forall_mem_nhds_pos_measure_preimage MeasureTheory.exists_ne_forall_mem_nhds_pos_measure_preimage

/-- If two finite measures give the same mass to the whole space and coincide on a π-system made
of measurable sets, then they coincide on all sets in the σ-algebra generated by the π-system. -/
theorem ext_on_measurableSpace_of_generate_finite {α} (m₀ : MeasurableSpace α) {μ ν : Measure α}
    [IsFiniteMeasure μ] (C : Set (Set α)) (hμν : ∀ s ∈ C, μ s = ν s) {m : MeasurableSpace α}
    (h : m ≤ m₀) (hA : m = MeasurableSpace.generateFrom C) (hC : IsPiSystem C)
    (h_univ : μ Set.univ = ν Set.univ) {s : Set α} (hs : MeasurableSet[m] s) : μ s = ν s := by
  haveI : IsFiniteMeasure ν := by
    constructor
    rw [← h_univ]
    apply IsFiniteMeasure.measure_univ_lt_top
  refine' induction_on_inter hA hC (by simp) hμν _ _ hs
  · intro t h1t h2t
    have h1t_ : @MeasurableSet α m₀ t := h _ h1t
    rw [@measure_compl α m₀ μ t h1t_ (@measure_ne_top α m₀ μ _ t),
      @measure_compl α m₀ ν t h1t_ (@measure_ne_top α m₀ ν _ t), h_univ, h2t]
  · intro f h1f h2f h3f
    have h2f_ : ∀ i : ℕ, @MeasurableSet α m₀ (f i) := fun i => h _ (h2f i)
    simp [measure_iUnion, h1f, h3f, h2f_]
#align measure_theory.ext_on_measurable_space_of_generate_finite MeasureTheory.ext_on_measurableSpace_of_generate_finite

/-- Two finite measures are equal if they are equal on the π-system generating the σ-algebra
  (and `univ`). -/
theorem ext_of_generate_finite (C : Set (Set α)) (hA : m0 = generateFrom C) (hC : IsPiSystem C)
    [IsFiniteMeasure μ] (hμν : ∀ s ∈ C, μ s = ν s) (h_univ : μ univ = ν univ) : μ = ν :=
  Measure.ext fun _s hs =>
    ext_on_measurableSpace_of_generate_finite m0 C hμν le_rfl hA hC h_univ hs
#align measure_theory.ext_of_generate_finite MeasureTheory.ext_of_generate_finite

namespace Measure

section disjointed

/-- Given `S : μ.FiniteSpanningSetsIn {s | MeasurableSet s}`,
`FiniteSpanningSetsIn.disjointed` provides a `FiniteSpanningSetsIn {s | MeasurableSet s}`
such that its underlying sets are pairwise disjoint. -/
protected def FiniteSpanningSetsIn.disjointed {μ : Measure α}
    (S : μ.FiniteSpanningSetsIn { s | MeasurableSet s }) :
    μ.FiniteSpanningSetsIn { s | MeasurableSet s } :=
  ⟨disjointed S.set, MeasurableSet.disjointed S.set_mem, fun n =>
    lt_of_le_of_lt (measure_mono (disjointed_subset S.set n)) (S.finite _),
    S.spanning ▸ iUnion_disjointed⟩
#align measure_theory.measure.finite_spanning_sets_in.disjointed MeasureTheory.Measure.FiniteSpanningSetsIn.disjointed

theorem FiniteSpanningSetsIn.disjointed_set_eq {μ : Measure α}
    (S : μ.FiniteSpanningSetsIn { s | MeasurableSet s }) : S.disjointed.set = disjointed S.set :=
  rfl
#align measure_theory.measure.finite_spanning_sets_in.disjointed_set_eq MeasureTheory.Measure.FiniteSpanningSetsIn.disjointed_set_eq

theorem exists_eq_disjoint_finiteSpanningSetsIn (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    ∃ (S : μ.FiniteSpanningSetsIn { s | MeasurableSet s })
      (T : ν.FiniteSpanningSetsIn { s | MeasurableSet s }),
      S.set = T.set ∧ Pairwise (Disjoint on S.set) :=
  let S := (μ + ν).toFiniteSpanningSetsIn.disjointed
  ⟨S.ofLE (Measure.le_add_right le_rfl), S.ofLE (Measure.le_add_left le_rfl), rfl,
    disjoint_disjointed _⟩
#align measure_theory.measure.exists_eq_disjoint_finite_spanning_sets_in MeasureTheory.Measure.exists_eq_disjoint_finiteSpanningSetsIn

end disjointed

namespace FiniteAtFilter

variable {f g : Filter α}

theorem filter_mono (h : f ≤ g) : μ.FiniteAtFilter g → μ.FiniteAtFilter f := fun ⟨s, hs, hμ⟩ =>
  ⟨s, h hs, hμ⟩
#align measure_theory.measure.finite_at_filter.filter_mono MeasureTheory.Measure.FiniteAtFilter.filter_mono

theorem inf_of_left (h : μ.FiniteAtFilter f) : μ.FiniteAtFilter (f ⊓ g) :=
  h.filter_mono inf_le_left
#align measure_theory.measure.finite_at_filter.inf_of_left MeasureTheory.Measure.FiniteAtFilter.inf_of_left

theorem inf_of_right (h : μ.FiniteAtFilter g) : μ.FiniteAtFilter (f ⊓ g) :=
  h.filter_mono inf_le_right
#align measure_theory.measure.finite_at_filter.inf_of_right MeasureTheory.Measure.FiniteAtFilter.inf_of_right

@[simp]
theorem inf_ae_iff : μ.FiniteAtFilter (f ⊓ μ.ae) ↔ μ.FiniteAtFilter f := by
  refine' ⟨_, fun h => h.filter_mono inf_le_left⟩
  rintro ⟨s, ⟨t, ht, u, hu, rfl⟩, hμ⟩
  suffices μ t ≤ μ (t ∩ u) from ⟨t, ht, this.trans_lt hμ⟩
  exact measure_mono_ae (mem_of_superset hu fun x hu ht => ⟨ht, hu⟩)
#align measure_theory.measure.finite_at_filter.inf_ae_iff MeasureTheory.Measure.FiniteAtFilter.inf_ae_iff

alias ⟨of_inf_ae, _⟩ := inf_ae_iff
#align measure_theory.measure.finite_at_filter.of_inf_ae MeasureTheory.Measure.FiniteAtFilter.of_inf_ae

theorem filter_mono_ae (h : f ⊓ μ.ae ≤ g) (hg : μ.FiniteAtFilter g) : μ.FiniteAtFilter f :=
  inf_ae_iff.1 (hg.filter_mono h)
#align measure_theory.measure.finite_at_filter.filter_mono_ae MeasureTheory.Measure.FiniteAtFilter.filter_mono_ae

protected theorem measure_mono (h : μ ≤ ν) : ν.FiniteAtFilter f → μ.FiniteAtFilter f :=
  fun ⟨s, hs, hν⟩ => ⟨s, hs, (Measure.le_iff'.1 h s).trans_lt hν⟩
#align measure_theory.measure.finite_at_filter.measure_mono MeasureTheory.Measure.FiniteAtFilter.measure_mono

@[mono]
protected theorem mono (hf : f ≤ g) (hμ : μ ≤ ν) : ν.FiniteAtFilter g → μ.FiniteAtFilter f :=
  fun h => (h.filter_mono hf).measure_mono hμ
#align measure_theory.measure.finite_at_filter.mono MeasureTheory.Measure.FiniteAtFilter.mono

protected theorem eventually (h : μ.FiniteAtFilter f) : ∀ᶠ s in f.smallSets, μ s < ∞ :=
  (eventually_smallSets' fun _s _t hst ht => (measure_mono hst).trans_lt ht).2 h
#align measure_theory.measure.finite_at_filter.eventually MeasureTheory.Measure.FiniteAtFilter.eventually

theorem filterSup : μ.FiniteAtFilter f → μ.FiniteAtFilter g → μ.FiniteAtFilter (f ⊔ g) :=
  fun ⟨s, hsf, hsμ⟩ ⟨t, htg, htμ⟩ =>
  ⟨s ∪ t, union_mem_sup hsf htg, (measure_union_le s t).trans_lt (ENNReal.add_lt_top.2 ⟨hsμ, htμ⟩)⟩
#align measure_theory.measure.finite_at_filter.filter_sup MeasureTheory.Measure.FiniteAtFilter.filterSup

end FiniteAtFilter

theorem finiteAt_nhdsWithin [TopologicalSpace α] {_m0 : MeasurableSpace α} (μ : Measure α)
    [IsLocallyFiniteMeasure μ] (x : α) (s : Set α) : μ.FiniteAtFilter (𝓝[s] x) :=
  (finiteAt_nhds μ x).inf_of_left
#align measure_theory.measure.finite_at_nhds_within MeasureTheory.Measure.finiteAt_nhdsWithin

@[simp]
theorem finiteAt_principal : μ.FiniteAtFilter (𝓟 s) ↔ μ s < ∞ :=
  ⟨fun ⟨_t, ht, hμ⟩ => (measure_mono ht).trans_lt hμ, fun h => ⟨s, mem_principal_self s, h⟩⟩
#align measure_theory.measure.finite_at_principal MeasureTheory.Measure.finiteAt_principal

theorem isLocallyFiniteMeasure_of_le [TopologicalSpace α] {_m : MeasurableSpace α} {μ ν : Measure α}
    [H : IsLocallyFiniteMeasure μ] (h : ν ≤ μ) : IsLocallyFiniteMeasure ν :=
  let F := H.finiteAtNhds
  ⟨fun x => (F x).measure_mono h⟩
#align measure_theory.measure.is_locally_finite_measure_of_le MeasureTheory.Measure.isLocallyFiniteMeasure_of_le

end Measure

end MeasureTheory

namespace IsCompact

variable [TopologicalSpace α] [MeasurableSpace α] {μ : Measure α} {s : Set α}

/-- If `s` is a compact set and `μ` is finite at `𝓝 x` for every `x ∈ s`, then `s` admits an open
superset of finite measure. -/
theorem exists_open_superset_measure_lt_top' (h : IsCompact s)
    (hμ : ∀ x ∈ s, μ.FiniteAtFilter (𝓝 x)) : ∃ U ⊇ s, IsOpen U ∧ μ U < ∞ := by
  refine' IsCompact.induction_on h _ _ _ _
  · use ∅
    simp [Superset]
  · rintro s t hst ⟨U, htU, hUo, hU⟩
    exact ⟨U, hst.trans htU, hUo, hU⟩
  · rintro s t ⟨U, hsU, hUo, hU⟩ ⟨V, htV, hVo, hV⟩
    refine'
      ⟨U ∪ V, union_subset_union hsU htV, hUo.union hVo,
        (measure_union_le _ _).trans_lt <| ENNReal.add_lt_top.2 ⟨hU, hV⟩⟩
  · intro x hx
    rcases (hμ x hx).exists_mem_basis (nhds_basis_opens _) with ⟨U, ⟨hx, hUo⟩, hU⟩
    exact ⟨U, nhdsWithin_le_nhds (hUo.mem_nhds hx), U, Subset.rfl, hUo, hU⟩
#align is_compact.exists_open_superset_measure_lt_top' IsCompact.exists_open_superset_measure_lt_top'

/-- If `s` is a compact set and `μ` is a locally finite measure, then `s` admits an open superset of
finite measure. -/
theorem exists_open_superset_measure_lt_top (h : IsCompact s) (μ : Measure α)
    [IsLocallyFiniteMeasure μ] : ∃ U ⊇ s, IsOpen U ∧ μ U < ∞ :=
  h.exists_open_superset_measure_lt_top' fun x _ => μ.finiteAt_nhds x
#align is_compact.exists_open_superset_measure_lt_top IsCompact.exists_open_superset_measure_lt_top

theorem measure_lt_top_of_nhdsWithin (h : IsCompact s) (hμ : ∀ x ∈ s, μ.FiniteAtFilter (𝓝[s] x)) :
    μ s < ∞ :=
  IsCompact.induction_on h (by simp) (fun s t hst ht => (measure_mono hst).trans_lt ht)
    (fun s t hs ht => (measure_union_le s t).trans_lt (ENNReal.add_lt_top.2 ⟨hs, ht⟩)) hμ
#align is_compact.measure_lt_top_of_nhds_within IsCompact.measure_lt_top_of_nhdsWithin

theorem measure_zero_of_nhdsWithin (hs : IsCompact s) :
    (∀ a ∈ s, ∃ t ∈ 𝓝[s] a, μ t = 0) → μ s = 0 := by
  simpa only [← compl_mem_ae_iff] using hs.compl_mem_sets_of_nhdsWithin
#align is_compact.measure_zero_of_nhds_within IsCompact.measure_zero_of_nhdsWithin

end IsCompact

-- see Note [lower instance priority]
instance (priority := 100) isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure [TopologicalSpace α]
    {_ : MeasurableSpace α} {μ : Measure α} [IsLocallyFiniteMeasure μ] :
    IsFiniteMeasureOnCompacts μ :=
  ⟨fun _s hs => hs.measure_lt_top_of_nhdsWithin fun _ _ => μ.finiteAt_nhdsWithin _ _⟩
#align is_finite_measure_on_compacts_of_is_locally_finite_measure isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure

theorem isFiniteMeasure_iff_isFiniteMeasureOnCompacts_of_compactSpace [TopologicalSpace α]
    [MeasurableSpace α] {μ : Measure α} [CompactSpace α] :
    IsFiniteMeasure μ ↔ IsFiniteMeasureOnCompacts μ := by
  constructor <;> intros
  · infer_instance
  · exact CompactSpace.isFiniteMeasure
#align is_finite_measure_iff_is_finite_measure_on_compacts_of_compact_space isFiniteMeasure_iff_isFiniteMeasureOnCompacts_of_compactSpace

/-- Compact covering of a `σ`-compact topological space as
`MeasureTheory.Measure.FiniteSpanningSetsIn`. -/
def MeasureTheory.Measure.finiteSpanningSetsInCompact [TopologicalSpace α] [SigmaCompactSpace α]
    {_ : MeasurableSpace α} (μ : Measure α) [IsLocallyFiniteMeasure μ] :
    μ.FiniteSpanningSetsIn { K | IsCompact K } where
  set := compactCovering α
  set_mem := isCompact_compactCovering α
  finite n := (isCompact_compactCovering α n).measure_lt_top
  spanning := iUnion_compactCovering α
#align measure_theory.measure.finite_spanning_sets_in_compact MeasureTheory.Measure.finiteSpanningSetsInCompact

/-- A locally finite measure on a `σ`-compact topological space admits a finite spanning sequence
of open sets. -/
def MeasureTheory.Measure.finiteSpanningSetsInOpen [TopologicalSpace α] [SigmaCompactSpace α]
    {_ : MeasurableSpace α} (μ : Measure α) [IsLocallyFiniteMeasure μ] :
    μ.FiniteSpanningSetsIn { K | IsOpen K } where
  set n := ((isCompact_compactCovering α n).exists_open_superset_measure_lt_top μ).choose
  set_mem n :=
    ((isCompact_compactCovering α n).exists_open_superset_measure_lt_top μ).choose_spec.2.1
  finite n :=
    ((isCompact_compactCovering α n).exists_open_superset_measure_lt_top μ).choose_spec.2.2
  spanning :=
    eq_univ_of_subset
      (iUnion_mono fun n =>
        ((isCompact_compactCovering α n).exists_open_superset_measure_lt_top μ).choose_spec.1)
      (iUnion_compactCovering α)
#align measure_theory.measure.finite_spanning_sets_in_open MeasureTheory.Measure.finiteSpanningSetsInOpen

open TopologicalSpace

/-- A locally finite measure on a second countable topological space admits a finite spanning
sequence of open sets. -/
noncomputable irreducible_def MeasureTheory.Measure.finiteSpanningSetsInOpen' [TopologicalSpace α]
  [SecondCountableTopology α] {m : MeasurableSpace α} (μ : Measure α) [IsLocallyFiniteMeasure μ] :
  μ.FiniteSpanningSetsIn { K | IsOpen K } := by
  suffices H : Nonempty (μ.FiniteSpanningSetsIn { K | IsOpen K }) from H.some
  cases isEmpty_or_nonempty α
  · exact
      ⟨{  set := fun _ => ∅
          set_mem := fun _ => by simp
          finite := fun _ => by simp
          spanning := by simp [eq_iff_true_of_subsingleton] }⟩
  inhabit α
  let S : Set (Set α) := { s | IsOpen s ∧ μ s < ∞ }
  obtain ⟨T, T_count, TS, hT⟩ : ∃ T : Set (Set α), T.Countable ∧ T ⊆ S ∧ ⋃₀ T = ⋃₀ S :=
    isOpen_sUnion_countable S fun s hs => hs.1
  rw [μ.isTopologicalBasis_isOpen_lt_top.sUnion_eq] at hT
  have T_ne : T.Nonempty := by
    by_contra h'T
    rw [not_nonempty_iff_eq_empty.1 h'T, sUnion_empty] at hT
    simpa only [← hT] using mem_univ (default : α)
  obtain ⟨f, hf⟩ : ∃ f : ℕ → Set α, T = range f
  exact T_count.exists_eq_range T_ne
  have fS : ∀ n, f n ∈ S := by
    intro n
    apply TS
    rw [hf]
    exact mem_range_self n
  refine'
    ⟨{  set := f
        set_mem := fun n => (fS n).1
        finite := fun n => (fS n).2
        spanning := _ }⟩
  refine eq_univ_of_forall fun x => ?_
  obtain ⟨t, tT, xt⟩ : ∃ t : Set α, t ∈ range f ∧ x ∈ t := by
    have : x ∈ ⋃₀ T := by simp only [hT, mem_univ]
    simpa only [mem_sUnion, exists_prop, ← hf]
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, f n = t := by simpa only using tT
  exact mem_iUnion_of_mem _ xt
#align measure_theory.measure.finite_spanning_sets_in_open' MeasureTheory.Measure.finiteSpanningSetsInOpen'

section MeasureIxx

variable [Preorder α] [TopologicalSpace α] [CompactIccSpace α] {m : MeasurableSpace α}
  {μ : Measure α} [IsLocallyFiniteMeasure μ] {a b : α}

theorem measure_Icc_lt_top : μ (Icc a b) < ∞ :=
  isCompact_Icc.measure_lt_top
#align measure_Icc_lt_top measure_Icc_lt_top

theorem measure_Ico_lt_top : μ (Ico a b) < ∞ :=
  (measure_mono Ico_subset_Icc_self).trans_lt measure_Icc_lt_top
#align measure_Ico_lt_top measure_Ico_lt_top

theorem measure_Ioc_lt_top : μ (Ioc a b) < ∞ :=
  (measure_mono Ioc_subset_Icc_self).trans_lt measure_Icc_lt_top
#align measure_Ioc_lt_top measure_Ioc_lt_top

theorem measure_Ioo_lt_top : μ (Ioo a b) < ∞ :=
  (measure_mono Ioo_subset_Icc_self).trans_lt measure_Icc_lt_top
#align measure_Ioo_lt_top measure_Ioo_lt_top

end MeasureIxx
