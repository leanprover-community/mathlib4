/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Rémy Degenne
-/
import Mathlib.Probability.Process.Adapted

#align_import probability.process.stopping from "leanprover-community/mathlib"@"ba074af83b6cf54c3104e59402b39410ddbd6dca"

/-!
# Stopping times, stopped processes and stopped values

Definition and properties of stopping times.

## Main definitions

* `MeasureTheory.IsStoppingTime`: a stopping time with respect to some filtration `f` is a
  function `τ` such that for all `i`, the preimage of `{j | j ≤ i}` along `τ` is
  `f i`-measurable
* `MeasureTheory.IsStoppingTime.measurableSpace`: the σ-algebra associated with a stopping time

## Main results

* `ProgMeasurable.stoppedProcess`: the stopped process of a progressively measurable process is
  progressively measurable.
* `memℒp_stoppedProcess`: if a process belongs to `ℒp` at every time in `ℕ`, then its stopped
  process belongs to `ℒp` as well.

## Tags

stopping time, stochastic process

-/


open Filter Order TopologicalSpace

open scoped Classical MeasureTheory NNReal ENNReal Topology BigOperators

namespace MeasureTheory

variable {Ω β ι : Type*} {m : MeasurableSpace Ω}

/-! ### Stopping times -/


/-- A stopping time with respect to some filtration `f` is a function
`τ` such that for all `i`, the preimage of `{j | j ≤ i}` along `τ` is measurable
with respect to `f i`.

Intuitively, the stopping time `τ` describes some stopping rule such that at time
`i`, we may determine it with the information we have at time `i`. -/
def IsStoppingTime [Preorder ι] (f : Filtration ι m) (τ : Ω → ι) :=
  ∀ i : ι, MeasurableSet[f i] <| {ω | τ ω ≤ i}
#align measure_theory.is_stopping_time MeasureTheory.IsStoppingTime

theorem isStoppingTime_const [Preorder ι] (f : Filtration ι m) (i : ι) :
    IsStoppingTime f fun _ => i := fun j => by simp only [MeasurableSet.const]
                                               -- 🎉 no goals
#align measure_theory.is_stopping_time_const MeasureTheory.isStoppingTime_const

section MeasurableSet

section Preorder

variable [Preorder ι] {f : Filtration ι m} {τ : Ω → ι}

protected theorem IsStoppingTime.measurableSet_le (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[f i] {ω | τ ω ≤ i} :=
  hτ i
#align measure_theory.is_stopping_time.measurable_set_le MeasureTheory.IsStoppingTime.measurableSet_le

theorem IsStoppingTime.measurableSet_lt_of_pred [PredOrder ι] (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[f i] {ω | τ ω < i} := by
  by_cases hi_min : IsMin i
  -- ⊢ MeasurableSet {ω | τ ω < i}
  · suffices {ω : Ω | τ ω < i} = ∅ by rw [this]; exact @MeasurableSet.empty _ (f i)
    -- ⊢ {ω | τ ω < i} = ∅
    ext1 ω
    -- ⊢ ω ∈ {ω | τ ω < i} ↔ ω ∈ ∅
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false_iff]
    -- ⊢ ¬τ ω < i
    rw [isMin_iff_forall_not_lt] at hi_min
    -- ⊢ ¬τ ω < i
    exact hi_min (τ ω)
    -- 🎉 no goals
  have : {ω : Ω | τ ω < i} = τ ⁻¹' Set.Iio i := rfl
  -- ⊢ MeasurableSet {ω | τ ω < i}
  rw [this, ← Iic_pred_of_not_isMin hi_min]
  -- ⊢ MeasurableSet (τ ⁻¹' Set.Iic (pred i))
  exact f.mono (pred_le i) _ (hτ.measurableSet_le <| pred i)
  -- 🎉 no goals
#align measure_theory.is_stopping_time.measurable_set_lt_of_pred MeasureTheory.IsStoppingTime.measurableSet_lt_of_pred

end Preorder

section CountableStoppingTime

namespace IsStoppingTime

variable [PartialOrder ι] {τ : Ω → ι} {f : Filtration ι m}

protected theorem measurableSet_eq_of_countable_range (hτ : IsStoppingTime f τ)
    (h_countable : (Set.range τ).Countable) (i : ι) : MeasurableSet[f i] {ω | τ ω = i} := by
  have : {ω | τ ω = i} = {ω | τ ω ≤ i} \ ⋃ (j ∈ Set.range τ) (_ : j < i), {ω | τ ω ≤ j} := by
    ext1 a
    simp only [Set.mem_setOf_eq, Set.mem_range, Set.iUnion_exists, Set.iUnion_iUnion_eq',
      Set.mem_diff, Set.mem_iUnion, exists_prop, not_exists, not_and, not_le]
    constructor <;> intro h
    · simp only [h, lt_iff_le_not_le, le_refl, and_imp, imp_self, imp_true_iff, and_self_iff]
    · have h_lt_or_eq : τ a < i ∨ τ a = i := lt_or_eq_of_le h.1
      rcases h_lt_or_eq with (h_lt | rfl)
      · exfalso
        exact h.2 a h_lt (le_refl (τ a))
      · rfl
  rw [this]
  -- ⊢ MeasurableSet ({ω | τ ω ≤ i} \ ⋃ (j : ι) (_ : j ∈ Set.range τ) (_ : j < i),  …
  refine' (hτ.measurableSet_le i).diff _
  -- ⊢ MeasurableSet (⋃ (j : ι) (_ : j ∈ Set.range τ) (_ : j < i), {ω | τ ω ≤ j})
  refine' MeasurableSet.biUnion h_countable fun j _ => _
  -- ⊢ MeasurableSet (⋃ (_ : j < i), {ω | τ ω ≤ j})
  by_cases hji : j < i
  -- ⊢ MeasurableSet (⋃ (_ : j < i), {ω | τ ω ≤ j})
  · simp only [hji, Set.iUnion_true]
    -- ⊢ MeasurableSet {ω | τ ω ≤ j}
    exact f.mono hji.le _ (hτ.measurableSet_le j)
    -- 🎉 no goals
  · simp only [hji, Set.iUnion_false]
    -- ⊢ MeasurableSet ∅
    exact @MeasurableSet.empty _ (f i)
    -- 🎉 no goals
#align measure_theory.is_stopping_time.measurable_set_eq_of_countable_range MeasureTheory.IsStoppingTime.measurableSet_eq_of_countable_range

protected theorem measurableSet_eq_of_countable [Countable ι] (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[f i] {ω | τ ω = i} :=
  hτ.measurableSet_eq_of_countable_range (Set.to_countable _) i
#align measure_theory.is_stopping_time.measurable_set_eq_of_countable MeasureTheory.IsStoppingTime.measurableSet_eq_of_countable

protected theorem measurableSet_lt_of_countable_range (hτ : IsStoppingTime f τ)
    (h_countable : (Set.range τ).Countable) (i : ι) : MeasurableSet[f i] {ω | τ ω < i} := by
  have : {ω | τ ω < i} = {ω | τ ω ≤ i} \ {ω | τ ω = i} := by ext1 ω; simp [lt_iff_le_and_ne]
  -- ⊢ MeasurableSet {ω | τ ω < i}
  rw [this]
  -- ⊢ MeasurableSet ({ω | τ ω ≤ i} \ {ω | τ ω = i})
  exact (hτ.measurableSet_le i).diff (hτ.measurableSet_eq_of_countable_range h_countable i)
  -- 🎉 no goals
#align measure_theory.is_stopping_time.measurable_set_lt_of_countable_range MeasureTheory.IsStoppingTime.measurableSet_lt_of_countable_range

protected theorem measurableSet_lt_of_countable [Countable ι] (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[f i] {ω | τ ω < i} :=
  hτ.measurableSet_lt_of_countable_range (Set.to_countable _) i
#align measure_theory.is_stopping_time.measurable_set_lt_of_countable MeasureTheory.IsStoppingTime.measurableSet_lt_of_countable

protected theorem measurableSet_ge_of_countable_range {ι} [LinearOrder ι] {τ : Ω → ι}
    {f : Filtration ι m} (hτ : IsStoppingTime f τ) (h_countable : (Set.range τ).Countable) (i : ι) :
    MeasurableSet[f i] {ω | i ≤ τ ω} := by
  have : {ω | i ≤ τ ω} = {ω | τ ω < i}ᶜ := by
    ext1 ω; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_lt]
  rw [this]
  -- ⊢ MeasurableSet {ω | τ ω < i}ᶜ
  exact (hτ.measurableSet_lt_of_countable_range h_countable i).compl
  -- 🎉 no goals
#align measure_theory.is_stopping_time.measurable_set_ge_of_countable_range MeasureTheory.IsStoppingTime.measurableSet_ge_of_countable_range

protected theorem measurableSet_ge_of_countable {ι} [LinearOrder ι] {τ : Ω → ι} {f : Filtration ι m}
    [Countable ι] (hτ : IsStoppingTime f τ) (i : ι) : MeasurableSet[f i] {ω | i ≤ τ ω} :=
  hτ.measurableSet_ge_of_countable_range (Set.to_countable _) i
#align measure_theory.is_stopping_time.measurable_set_ge_of_countable MeasureTheory.IsStoppingTime.measurableSet_ge_of_countable

end IsStoppingTime

end CountableStoppingTime

section LinearOrder

variable [LinearOrder ι] {f : Filtration ι m} {τ : Ω → ι}

theorem IsStoppingTime.measurableSet_gt (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[f i] {ω | i < τ ω} := by
  have : {ω | i < τ ω} = {ω | τ ω ≤ i}ᶜ := by
    ext1 ω; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
  rw [this]
  -- ⊢ MeasurableSet {ω | τ ω ≤ i}ᶜ
  exact (hτ.measurableSet_le i).compl
  -- 🎉 no goals
#align measure_theory.is_stopping_time.measurable_set_gt MeasureTheory.IsStoppingTime.measurableSet_gt

section TopologicalSpace

variable [TopologicalSpace ι] [OrderTopology ι] [FirstCountableTopology ι]

/-- Auxiliary lemma for `is_stopping_time.measurable_set_lt`. -/
theorem IsStoppingTime.measurableSet_lt_of_isLUB (hτ : IsStoppingTime f τ) (i : ι)
    (h_lub : IsLUB (Set.Iio i) i) : MeasurableSet[f i] {ω | τ ω < i} := by
  by_cases hi_min : IsMin i
  -- ⊢ MeasurableSet {ω | τ ω < i}
  · suffices {ω | τ ω < i} = ∅ by rw [this]; exact @MeasurableSet.empty _ (f i)
    -- ⊢ {ω | τ ω < i} = ∅
    ext1 ω
    -- ⊢ ω ∈ {ω | τ ω < i} ↔ ω ∈ ∅
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false_iff]
    -- ⊢ ¬τ ω < i
    exact isMin_iff_forall_not_lt.mp hi_min (τ ω)
    -- 🎉 no goals
  obtain ⟨seq, -, -, h_tendsto, h_bound⟩ :
    ∃ seq : ℕ → ι, Monotone seq ∧ (∀ j, seq j ≤ i) ∧ Tendsto seq atTop (𝓝 i) ∧ ∀ j, seq j < i
  exact h_lub.exists_seq_monotone_tendsto (not_isMin_iff.mp hi_min)
  -- ⊢ MeasurableSet {ω | τ ω < i}
  have h_Ioi_eq_Union : Set.Iio i = ⋃ j, {k | k ≤ seq j} := by
    ext1 k
    simp only [Set.mem_Iio, Set.mem_iUnion, Set.mem_setOf_eq]
    refine' ⟨fun hk_lt_i => _, fun h_exists_k_le_seq => _⟩
    · rw [tendsto_atTop'] at h_tendsto
      have h_nhds : Set.Ici k ∈ 𝓝 i :=
        mem_nhds_iff.mpr ⟨Set.Ioi k, Set.Ioi_subset_Ici le_rfl, isOpen_Ioi, hk_lt_i⟩
      obtain ⟨a, ha⟩ : ∃ a : ℕ, ∀ b : ℕ, b ≥ a → k ≤ seq b := h_tendsto (Set.Ici k) h_nhds
      exact ⟨a, ha a le_rfl⟩
    · obtain ⟨j, hk_seq_j⟩ := h_exists_k_le_seq
      exact hk_seq_j.trans_lt (h_bound j)
  have h_lt_eq_preimage : {ω | τ ω < i} = τ ⁻¹' Set.Iio i := by
    ext1 ω; simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iio]
  rw [h_lt_eq_preimage, h_Ioi_eq_Union]
  -- ⊢ MeasurableSet (τ ⁻¹' ⋃ (j : ℕ), {k | k ≤ seq j})
  simp only [Set.preimage_iUnion, Set.preimage_setOf_eq]
  -- ⊢ MeasurableSet (⋃ (i : ℕ), {a | τ a ≤ seq i})
  exact MeasurableSet.iUnion fun n => f.mono (h_bound n).le _ (hτ.measurableSet_le (seq n))
  -- 🎉 no goals
#align measure_theory.is_stopping_time.measurable_set_lt_of_is_lub MeasureTheory.IsStoppingTime.measurableSet_lt_of_isLUB

theorem IsStoppingTime.measurableSet_lt (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[f i] {ω | τ ω < i} := by
  obtain ⟨i', hi'_lub⟩ : ∃ i', IsLUB (Set.Iio i) i'; exact exists_lub_Iio i
  -- ⊢ ∃ i', IsLUB (Set.Iio i) i'
                                                     -- ⊢ MeasurableSet {ω | τ ω < i}
  cases' lub_Iio_eq_self_or_Iio_eq_Iic i hi'_lub with hi'_eq_i h_Iio_eq_Iic
  -- ⊢ MeasurableSet {ω | τ ω < i}
  · rw [← hi'_eq_i] at hi'_lub ⊢
    -- ⊢ MeasurableSet {ω | τ ω < i'}
    exact hτ.measurableSet_lt_of_isLUB i' hi'_lub
    -- 🎉 no goals
  · have h_lt_eq_preimage : {ω : Ω | τ ω < i} = τ ⁻¹' Set.Iio i := rfl
    -- ⊢ MeasurableSet {ω | τ ω < i}
    rw [h_lt_eq_preimage, h_Iio_eq_Iic]
    -- ⊢ MeasurableSet (τ ⁻¹' Set.Iic i')
    exact f.mono (lub_Iio_le i hi'_lub) _ (hτ.measurableSet_le i')
    -- 🎉 no goals
#align measure_theory.is_stopping_time.measurable_set_lt MeasureTheory.IsStoppingTime.measurableSet_lt

theorem IsStoppingTime.measurableSet_ge (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[f i] {ω | i ≤ τ ω} := by
  have : {ω | i ≤ τ ω} = {ω | τ ω < i}ᶜ := by
    ext1 ω; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_lt]
  rw [this]
  -- ⊢ MeasurableSet {ω | τ ω < i}ᶜ
  exact (hτ.measurableSet_lt i).compl
  -- 🎉 no goals
#align measure_theory.is_stopping_time.measurable_set_ge MeasureTheory.IsStoppingTime.measurableSet_ge

theorem IsStoppingTime.measurableSet_eq (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[f i] {ω | τ ω = i} := by
  have : {ω | τ ω = i} = {ω | τ ω ≤ i} ∩ {ω | τ ω ≥ i} := by
    ext1 ω; simp only [Set.mem_setOf_eq, ge_iff_le, Set.mem_inter_iff, le_antisymm_iff]
  rw [this]
  -- ⊢ MeasurableSet ({ω | τ ω ≤ i} ∩ {ω | τ ω ≥ i})
  exact (hτ.measurableSet_le i).inter (hτ.measurableSet_ge i)
  -- 🎉 no goals
#align measure_theory.is_stopping_time.measurable_set_eq MeasureTheory.IsStoppingTime.measurableSet_eq

theorem IsStoppingTime.measurableSet_eq_le (hτ : IsStoppingTime f τ) {i j : ι} (hle : i ≤ j) :
    MeasurableSet[f j] {ω | τ ω = i} :=
  f.mono hle _ <| hτ.measurableSet_eq i
#align measure_theory.is_stopping_time.measurable_set_eq_le MeasureTheory.IsStoppingTime.measurableSet_eq_le

theorem IsStoppingTime.measurableSet_lt_le (hτ : IsStoppingTime f τ) {i j : ι} (hle : i ≤ j) :
    MeasurableSet[f j] {ω | τ ω < i} :=
  f.mono hle _ <| hτ.measurableSet_lt i
#align measure_theory.is_stopping_time.measurable_set_lt_le MeasureTheory.IsStoppingTime.measurableSet_lt_le

end TopologicalSpace

end LinearOrder

section Countable

theorem isStoppingTime_of_measurableSet_eq [Preorder ι] [Countable ι] {f : Filtration ι m}
    {τ : Ω → ι} (hτ : ∀ i, MeasurableSet[f i] {ω | τ ω = i}) : IsStoppingTime f τ := by
  intro i
  -- ⊢ MeasurableSet {ω | τ ω ≤ i}
  rw [show {ω | τ ω ≤ i} = ⋃ k ≤ i, {ω | τ ω = k} by ext; simp]
  -- ⊢ MeasurableSet (⋃ (k : ι) (_ : k ≤ i), {ω | τ ω = k})
  refine' MeasurableSet.biUnion (Set.to_countable _) fun k hk => _
  -- ⊢ MeasurableSet {ω | τ ω = k}
  exact f.mono hk _ (hτ k)
  -- 🎉 no goals
#align measure_theory.is_stopping_time_of_measurable_set_eq MeasureTheory.isStoppingTime_of_measurableSet_eq

end Countable

end MeasurableSet

namespace IsStoppingTime

protected theorem max [LinearOrder ι] {f : Filtration ι m} {τ π : Ω → ι} (hτ : IsStoppingTime f τ)
    (hπ : IsStoppingTime f π) : IsStoppingTime f fun ω => max (τ ω) (π ω) := by
  intro i
  -- ⊢ MeasurableSet {ω | (fun ω => max (τ ω) (π ω)) ω ≤ i}
  simp_rw [max_le_iff, Set.setOf_and]
  -- ⊢ MeasurableSet ({a | τ a ≤ i} ∩ {a | π a ≤ i})
  exact (hτ i).inter (hπ i)
  -- 🎉 no goals
#align measure_theory.is_stopping_time.max MeasureTheory.IsStoppingTime.max

protected theorem max_const [LinearOrder ι] {f : Filtration ι m} {τ : Ω → ι}
    (hτ : IsStoppingTime f τ) (i : ι) : IsStoppingTime f fun ω => max (τ ω) i :=
  hτ.max (isStoppingTime_const f i)
#align measure_theory.is_stopping_time.max_const MeasureTheory.IsStoppingTime.max_const

protected theorem min [LinearOrder ι] {f : Filtration ι m} {τ π : Ω → ι} (hτ : IsStoppingTime f τ)
    (hπ : IsStoppingTime f π) : IsStoppingTime f fun ω => min (τ ω) (π ω) := by
  intro i
  -- ⊢ MeasurableSet {ω | (fun ω => min (τ ω) (π ω)) ω ≤ i}
  simp_rw [min_le_iff, Set.setOf_or]
  -- ⊢ MeasurableSet ({a | τ a ≤ i} ∪ {a | π a ≤ i})
  exact (hτ i).union (hπ i)
  -- 🎉 no goals
#align measure_theory.is_stopping_time.min MeasureTheory.IsStoppingTime.min

protected theorem min_const [LinearOrder ι] {f : Filtration ι m} {τ : Ω → ι}
    (hτ : IsStoppingTime f τ) (i : ι) : IsStoppingTime f fun ω => min (τ ω) i :=
  hτ.min (isStoppingTime_const f i)
#align measure_theory.is_stopping_time.min_const MeasureTheory.IsStoppingTime.min_const

theorem add_const [AddGroup ι] [Preorder ι] [CovariantClass ι ι (Function.swap (· + ·)) (· ≤ ·)]
    [CovariantClass ι ι (· + ·) (· ≤ ·)] {f : Filtration ι m} {τ : Ω → ι} (hτ : IsStoppingTime f τ)
    {i : ι} (hi : 0 ≤ i) : IsStoppingTime f fun ω => τ ω + i := by
  intro j
  -- ⊢ MeasurableSet {ω | (fun ω => τ ω + i) ω ≤ j}
  simp_rw [← le_sub_iff_add_le]
  -- ⊢ MeasurableSet {ω | τ ω ≤ j - i}
  exact f.mono (sub_le_self j hi) _ (hτ (j - i))
  -- 🎉 no goals
#align measure_theory.is_stopping_time.add_const MeasureTheory.IsStoppingTime.add_const

theorem add_const_nat {f : Filtration ℕ m} {τ : Ω → ℕ} (hτ : IsStoppingTime f τ) {i : ℕ} :
    IsStoppingTime f fun ω => τ ω + i := by
  refine' isStoppingTime_of_measurableSet_eq fun j => _
  -- ⊢ MeasurableSet {ω | τ ω + i = j}
  by_cases hij : i ≤ j
  -- ⊢ MeasurableSet {ω | τ ω + i = j}
  · simp_rw [eq_comm, ← Nat.sub_eq_iff_eq_add hij, eq_comm]
    -- ⊢ MeasurableSet {ω | τ ω = j - i}
    exact f.mono (j.sub_le i) _ (hτ.measurableSet_eq (j - i))
    -- 🎉 no goals
  · rw [not_le] at hij
    -- ⊢ MeasurableSet {ω | τ ω + i = j}
    convert @MeasurableSet.empty _ (f.1 j)
    -- ⊢ {ω | τ ω + i = j} = ∅
    ext ω
    -- ⊢ ω ∈ {ω | τ ω + i = j} ↔ ω ∈ ∅
    simp only [Set.mem_empty_iff_false, iff_false_iff]
    -- ⊢ ¬ω ∈ {ω | τ ω + i = j}
    rintro (hx : τ ω + i = j)
    -- ⊢ False
    linarith
    -- 🎉 no goals
#align measure_theory.is_stopping_time.add_const_nat MeasureTheory.IsStoppingTime.add_const_nat

-- generalize to certain countable type?
theorem add {f : Filtration ℕ m} {τ π : Ω → ℕ} (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) :
    IsStoppingTime f (τ + π) := by
  intro i
  -- ⊢ MeasurableSet {ω | (τ + π) ω ≤ i}
  rw [(_ : {ω | (τ + π) ω ≤ i} = ⋃ k ≤ i, {ω | π ω = k} ∩ {ω | τ ω + k ≤ i})]
  -- ⊢ MeasurableSet (⋃ (k : ℕ) (_ : k ≤ i), {ω | π ω = k} ∩ {ω | τ ω + k ≤ i})
  · exact MeasurableSet.iUnion fun k =>
      MeasurableSet.iUnion fun hk => (hπ.measurableSet_eq_le hk).inter (hτ.add_const_nat i)
  ext ω
  -- ⊢ ω ∈ {ω | (τ + π) ω ≤ i} ↔ ω ∈ ⋃ (k : ℕ) (_ : k ≤ i), {ω | π ω = k} ∩ {ω | τ  …
  simp only [Pi.add_apply, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, exists_prop]
  -- ⊢ τ ω + π ω ≤ i ↔ ∃ i_1, i_1 ≤ i ∧ π ω = i_1 ∧ τ ω + i_1 ≤ i
  refine' ⟨fun h => ⟨π ω, by linarith, rfl, h⟩, _⟩
  -- ⊢ (∃ i_1, i_1 ≤ i ∧ π ω = i_1 ∧ τ ω + i_1 ≤ i) → τ ω + π ω ≤ i
  rintro ⟨j, hj, rfl, h⟩
  -- ⊢ τ ω + π ω ≤ i
  assumption
  -- 🎉 no goals
#align measure_theory.is_stopping_time.add MeasureTheory.IsStoppingTime.add

section Preorder

variable [Preorder ι] {f : Filtration ι m} {τ π : Ω → ι}

/-- The associated σ-algebra with a stopping time. -/
protected def measurableSpace (hτ : IsStoppingTime f τ) : MeasurableSpace Ω where
  MeasurableSet' s := ∀ i : ι, MeasurableSet[f i] (s ∩ {ω | τ ω ≤ i})
  measurableSet_empty i := (Set.empty_inter {ω | τ ω ≤ i}).symm ▸ @MeasurableSet.empty _ (f i)
  measurableSet_compl s hs i := by
    rw [(_ : sᶜ ∩ {ω | τ ω ≤ i} = (sᶜ ∪ {ω | τ ω ≤ i}ᶜ) ∩ {ω | τ ω ≤ i})]
    -- ⊢ MeasurableSet ((sᶜ ∪ {ω | τ ω ≤ i}ᶜ) ∩ {ω | τ ω ≤ i})
    · refine' MeasurableSet.inter _ _
      -- ⊢ MeasurableSet (sᶜ ∪ {ω | τ ω ≤ i}ᶜ)
      · rw [← Set.compl_inter]
        -- ⊢ MeasurableSet (s ∩ {ω | τ ω ≤ i})ᶜ
        exact (hs i).compl
        -- 🎉 no goals
      · exact hτ i
        -- 🎉 no goals
    · rw [Set.union_inter_distrib_right]
      -- ⊢ sᶜ ∩ {ω | τ ω ≤ i} = sᶜ ∩ {ω | τ ω ≤ i} ∪ {ω | τ ω ≤ i}ᶜ ∩ {ω | τ ω ≤ i}
      simp only [Set.compl_inter_self, Set.union_empty]
      -- 🎉 no goals
  measurableSet_iUnion s hs i := by
    rw [forall_swap] at hs
    -- ⊢ MeasurableSet ((⋃ (i : ℕ), s i) ∩ {ω | τ ω ≤ i})
    rw [Set.iUnion_inter]
    -- ⊢ MeasurableSet (⋃ (i_1 : ℕ), s i_1 ∩ {ω | τ ω ≤ i})
    exact MeasurableSet.iUnion (hs i)
    -- 🎉 no goals
#align measure_theory.is_stopping_time.measurable_space MeasureTheory.IsStoppingTime.measurableSpace

protected theorem measurableSet (hτ : IsStoppingTime f τ) (s : Set Ω) :
    MeasurableSet[hτ.measurableSpace] s ↔ ∀ i : ι, MeasurableSet[f i] (s ∩ {ω | τ ω ≤ i}) :=
  Iff.rfl
#align measure_theory.is_stopping_time.measurable_set MeasureTheory.IsStoppingTime.measurableSet

theorem measurableSpace_mono (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) (hle : τ ≤ π) :
    hτ.measurableSpace ≤ hπ.measurableSpace := by
  intro s hs i
  -- ⊢ MeasurableSet (s ∩ {ω | π ω ≤ i})
  rw [(_ : s ∩ {ω | π ω ≤ i} = s ∩ {ω | τ ω ≤ i} ∩ {ω | π ω ≤ i})]
  -- ⊢ MeasurableSet (s ∩ {ω | τ ω ≤ i} ∩ {ω | π ω ≤ i})
  · exact (hs i).inter (hπ i)
    -- 🎉 no goals
  · ext
    -- ⊢ x✝ ∈ s ∩ {ω | π ω ≤ i} ↔ x✝ ∈ s ∩ {ω | τ ω ≤ i} ∩ {ω | π ω ≤ i}
    simp only [Set.mem_inter_iff, iff_self_and, and_congr_left_iff, Set.mem_setOf_eq]
    -- ⊢ π x✝ ≤ i → x✝ ∈ s → τ x✝ ≤ i
    intro hle' _
    -- ⊢ τ x✝ ≤ i
    exact le_trans (hle _) hle'
    -- 🎉 no goals
#align measure_theory.is_stopping_time.measurable_space_mono MeasureTheory.IsStoppingTime.measurableSpace_mono

theorem measurableSpace_le_of_countable [Countable ι] (hτ : IsStoppingTime f τ) :
    hτ.measurableSpace ≤ m := by
  intro s hs
  -- ⊢ MeasurableSet s
  change ∀ i, MeasurableSet[f i] (s ∩ {ω | τ ω ≤ i}) at hs
  -- ⊢ MeasurableSet s
  rw [(_ : s = ⋃ i, s ∩ {ω | τ ω ≤ i})]
  -- ⊢ MeasurableSet (⋃ (i : ι), s ∩ {ω | τ ω ≤ i})
  · exact MeasurableSet.iUnion fun i => f.le i _ (hs i)
    -- 🎉 no goals
  · ext ω; constructor <;> rw [Set.mem_iUnion]
    -- ⊢ ω ∈ s ↔ ω ∈ ⋃ (i : ι), s ∩ {ω | τ ω ≤ i}
           -- ⊢ ω ∈ s → ω ∈ ⋃ (i : ι), s ∩ {ω | τ ω ≤ i}
                           -- ⊢ ω ∈ s → ∃ i, ω ∈ s ∩ {ω | τ ω ≤ i}
                           -- ⊢ (∃ i, ω ∈ s ∩ {ω | τ ω ≤ i}) → ω ∈ s
    · exact fun hx => ⟨τ ω, hx, le_rfl⟩
      -- 🎉 no goals
    · rintro ⟨_, hx, _⟩
      -- ⊢ ω ∈ s
      exact hx
      -- 🎉 no goals
#align measure_theory.is_stopping_time.measurable_space_le_of_countable MeasureTheory.IsStoppingTime.measurableSpace_le_of_countable

theorem measurableSpace_le' [IsCountablyGenerated (atTop : Filter ι)] [(atTop : Filter ι).NeBot]
    (hτ : IsStoppingTime f τ) : hτ.measurableSpace ≤ m := by
  intro s hs
  -- ⊢ MeasurableSet s
  change ∀ i, MeasurableSet[f i] (s ∩ {ω | τ ω ≤ i}) at hs
  -- ⊢ MeasurableSet s
  obtain ⟨seq : ℕ → ι, h_seq_tendsto⟩ := (atTop : Filter ι).exists_seq_tendsto
  -- ⊢ MeasurableSet s
  rw [(_ : s = ⋃ n, s ∩ {ω | τ ω ≤ seq n})]
  -- ⊢ MeasurableSet (⋃ (n : ℕ), s ∩ {ω | τ ω ≤ seq n})
  · exact MeasurableSet.iUnion fun i => f.le (seq i) _ (hs (seq i))
    -- 🎉 no goals
  · ext ω; constructor <;> rw [Set.mem_iUnion]
    -- ⊢ ω ∈ s ↔ ω ∈ ⋃ (n : ℕ), s ∩ {ω | τ ω ≤ seq n}
           -- ⊢ ω ∈ s → ω ∈ ⋃ (n : ℕ), s ∩ {ω | τ ω ≤ seq n}
                           -- ⊢ ω ∈ s → ∃ i, ω ∈ s ∩ {ω | τ ω ≤ seq i}
                           -- ⊢ (∃ i, ω ∈ s ∩ {ω | τ ω ≤ seq i}) → ω ∈ s
    · intro hx
      -- ⊢ ∃ i, ω ∈ s ∩ {ω | τ ω ≤ seq i}
      suffices : ∃ i, τ ω ≤ seq i; exact ⟨this.choose, hx, this.choose_spec⟩
      -- ⊢ ∃ i, ω ∈ s ∩ {ω | τ ω ≤ seq i}
                                   -- ⊢ ∃ i, τ ω ≤ seq i
      rw [tendsto_atTop] at h_seq_tendsto
      -- ⊢ ∃ i, τ ω ≤ seq i
      exact (h_seq_tendsto (τ ω)).exists
      -- 🎉 no goals
    · rintro ⟨_, hx, _⟩
      -- ⊢ ω ∈ s
      exact hx
      -- 🎉 no goals
#align measure_theory.is_stopping_time.measurable_space_le' MeasureTheory.IsStoppingTime.measurableSpace_le'

theorem measurableSpace_le {ι} [SemilatticeSup ι] {f : Filtration ι m} {τ : Ω → ι}
    [IsCountablyGenerated (atTop : Filter ι)] (hτ : IsStoppingTime f τ) :
    hτ.measurableSpace ≤ m := by
  cases isEmpty_or_nonempty ι
  -- ⊢ IsStoppingTime.measurableSpace hτ ≤ m
  · haveI : IsEmpty Ω := ⟨fun ω => IsEmpty.false (τ ω)⟩
    -- ⊢ IsStoppingTime.measurableSpace hτ ≤ m
    intro s _
    -- ⊢ MeasurableSet s
    suffices hs : s = ∅; · rw [hs]; exact MeasurableSet.empty
    -- ⊢ MeasurableSet s
                           -- ⊢ MeasurableSet ∅
                                    -- 🎉 no goals
    haveI : Unique (Set Ω) := Set.uniqueEmpty
    -- ⊢ s = ∅
    rw [Unique.eq_default s, Unique.eq_default ∅]
    -- 🎉 no goals
  exact measurableSpace_le' hτ
  -- 🎉 no goals
#align measure_theory.is_stopping_time.measurable_space_le MeasureTheory.IsStoppingTime.measurableSpace_le

example {f : Filtration ℕ m} {τ : Ω → ℕ} (hτ : IsStoppingTime f τ) : hτ.measurableSpace ≤ m :=
  hτ.measurableSpace_le

example {f : Filtration ℝ m} {τ : Ω → ℝ} (hτ : IsStoppingTime f τ) : hτ.measurableSpace ≤ m :=
  hτ.measurableSpace_le

@[simp]
theorem measurableSpace_const (f : Filtration ι m) (i : ι) :
    (isStoppingTime_const f i).measurableSpace = f i := by
  ext1 s
  -- ⊢ MeasurableSet s ↔ MeasurableSet s
  change MeasurableSet[(isStoppingTime_const f i).measurableSpace] s ↔ MeasurableSet[f i] s
  -- ⊢ MeasurableSet s ↔ MeasurableSet s
  rw [IsStoppingTime.measurableSet]
  -- ⊢ (∀ (i_1 : ι), MeasurableSet (s ∩ {ω | i ≤ i_1})) ↔ MeasurableSet s
  constructor <;> intro h
  -- ⊢ (∀ (i_1 : ι), MeasurableSet (s ∩ {ω | i ≤ i_1})) → MeasurableSet s
                  -- ⊢ MeasurableSet s
                  -- ⊢ ∀ (i_1 : ι), MeasurableSet (s ∩ {ω | i ≤ i_1})
  · specialize h i
    -- ⊢ MeasurableSet s
    simpa only [le_refl, Set.setOf_true, Set.inter_univ] using h
    -- 🎉 no goals
  · intro j
    -- ⊢ MeasurableSet (s ∩ {ω | i ≤ j})
    by_cases hij : i ≤ j
    -- ⊢ MeasurableSet (s ∩ {ω | i ≤ j})
    · simp only [hij, Set.setOf_true, Set.inter_univ]
      -- ⊢ MeasurableSet s
      exact f.mono hij _ h
      -- 🎉 no goals
    · simp only [hij, Set.setOf_false, Set.inter_empty, @MeasurableSet.empty _ (f.1 j)]
      -- 🎉 no goals
#align measure_theory.is_stopping_time.measurable_space_const MeasureTheory.IsStoppingTime.measurableSpace_const

theorem measurableSet_inter_eq_iff (hτ : IsStoppingTime f τ) (s : Set Ω) (i : ι) :
    MeasurableSet[hτ.measurableSpace] (s ∩ {ω | τ ω = i}) ↔
      MeasurableSet[f i] (s ∩ {ω | τ ω = i}) := by
  have : ∀ j, {ω : Ω | τ ω = i} ∩ {ω : Ω | τ ω ≤ j} = {ω : Ω | τ ω = i} ∩ {_ω | i ≤ j} := by
    intro j
    ext1 ω
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, and_congr_right_iff]
    intro hxi
    rw [hxi]
  constructor <;> intro h
  -- ⊢ MeasurableSet (s ∩ {ω | τ ω = i}) → MeasurableSet (s ∩ {ω | τ ω = i})
                  -- ⊢ MeasurableSet (s ∩ {ω | τ ω = i})
                  -- ⊢ MeasurableSet (s ∩ {ω | τ ω = i})
  · specialize h i
    -- ⊢ MeasurableSet (s ∩ {ω | τ ω = i})
    simpa only [Set.inter_assoc, this, le_refl, Set.setOf_true, Set.inter_univ] using h
    -- 🎉 no goals
  · intro j
    -- ⊢ MeasurableSet (s ∩ {ω | τ ω = i} ∩ {ω | τ ω ≤ j})
    rw [Set.inter_assoc, this]
    -- ⊢ MeasurableSet (s ∩ ({ω | τ ω = i} ∩ {_ω | i ≤ j}))
    by_cases hij : i ≤ j
    -- ⊢ MeasurableSet (s ∩ ({ω | τ ω = i} ∩ {_ω | i ≤ j}))
    · simp only [hij, Set.setOf_true, Set.inter_univ]
      -- ⊢ MeasurableSet (s ∩ {ω | τ ω = i})
      exact f.mono hij _ h
      -- 🎉 no goals
    · simp [hij]; convert @MeasurableSet.empty _ (Filtration.seq f j)
      -- ⊢ MeasurableSet ∅
                  -- 🎉 no goals
#align measure_theory.is_stopping_time.measurable_set_inter_eq_iff MeasureTheory.IsStoppingTime.measurableSet_inter_eq_iff

theorem measurableSpace_le_of_le_const (hτ : IsStoppingTime f τ) {i : ι} (hτ_le : ∀ ω, τ ω ≤ i) :
    hτ.measurableSpace ≤ f i :=
  (measurableSpace_mono hτ _ hτ_le).trans (measurableSpace_const _ _).le
#align measure_theory.is_stopping_time.measurable_space_le_of_le_const MeasureTheory.IsStoppingTime.measurableSpace_le_of_le_const

theorem measurableSpace_le_of_le (hτ : IsStoppingTime f τ) {n : ι} (hτ_le : ∀ ω, τ ω ≤ n) :
    hτ.measurableSpace ≤ m :=
  (hτ.measurableSpace_le_of_le_const hτ_le).trans (f.le n)
#align measure_theory.is_stopping_time.measurable_space_le_of_le MeasureTheory.IsStoppingTime.measurableSpace_le_of_le

theorem le_measurableSpace_of_const_le (hτ : IsStoppingTime f τ) {i : ι} (hτ_le : ∀ ω, i ≤ τ ω) :
    f i ≤ hτ.measurableSpace :=
  (measurableSpace_const _ _).symm.le.trans (measurableSpace_mono _ hτ hτ_le)
#align measure_theory.is_stopping_time.le_measurable_space_of_const_le MeasureTheory.IsStoppingTime.le_measurableSpace_of_const_le

end Preorder

instance sigmaFinite_stopping_time {ι} [SemilatticeSup ι] [OrderBot ι]
    [(Filter.atTop : Filter ι).IsCountablyGenerated] {μ : Measure Ω} {f : Filtration ι m}
    {τ : Ω → ι} [SigmaFiniteFiltration μ f] (hτ : IsStoppingTime f τ) :
    SigmaFinite (μ.trim hτ.measurableSpace_le) := by
  refine @sigmaFiniteTrim_mono _ _ ?_ _ _ _ ?_ ?_
  · exact f ⊥
    -- 🎉 no goals
  · exact hτ.le_measurableSpace_of_const_le fun _ => bot_le
    -- 🎉 no goals
  · infer_instance
    -- 🎉 no goals
#align measure_theory.is_stopping_time.sigma_finite_stopping_time MeasureTheory.IsStoppingTime.sigmaFinite_stopping_time

instance sigmaFinite_stopping_time_of_le {ι} [SemilatticeSup ι] [OrderBot ι] {μ : Measure Ω}
    {f : Filtration ι m} {τ : Ω → ι} [SigmaFiniteFiltration μ f] (hτ : IsStoppingTime f τ) {n : ι}
    (hτ_le : ∀ ω, τ ω ≤ n) : SigmaFinite (μ.trim (hτ.measurableSpace_le_of_le hτ_le)) := by
  refine @sigmaFiniteTrim_mono _ _ ?_ _ _ _ ?_ ?_
  · exact f ⊥
    -- 🎉 no goals
  · exact hτ.le_measurableSpace_of_const_le fun _ => bot_le
    -- 🎉 no goals
  · infer_instance
    -- 🎉 no goals
#align measure_theory.is_stopping_time.sigma_finite_stopping_time_of_le MeasureTheory.IsStoppingTime.sigmaFinite_stopping_time_of_le

section LinearOrder

variable [LinearOrder ι] {f : Filtration ι m} {τ π : Ω → ι}

protected theorem measurableSet_le' (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[hτ.measurableSpace] {ω | τ ω ≤ i} := by
  intro j
  -- ⊢ MeasurableSet ({ω | τ ω ≤ i} ∩ {ω | τ ω ≤ j})
  have : {ω : Ω | τ ω ≤ i} ∩ {ω : Ω | τ ω ≤ j} = {ω : Ω | τ ω ≤ min i j} := by
    ext1 ω; simp only [Set.mem_inter_iff, Set.mem_setOf_eq, le_min_iff]
  rw [this]
  -- ⊢ MeasurableSet {ω | τ ω ≤ min i j}
  exact f.mono (min_le_right i j) _ (hτ _)
  -- 🎉 no goals
#align measure_theory.is_stopping_time.measurable_set_le' MeasureTheory.IsStoppingTime.measurableSet_le'

protected theorem measurableSet_gt' (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[hτ.measurableSpace] {ω | i < τ ω} := by
  have : {ω : Ω | i < τ ω} = {ω : Ω | τ ω ≤ i}ᶜ := by ext1 ω; simp
  -- ⊢ MeasurableSet {ω | i < τ ω}
  rw [this]
  -- ⊢ MeasurableSet {ω | τ ω ≤ i}ᶜ
  exact (hτ.measurableSet_le' i).compl
  -- 🎉 no goals
#align measure_theory.is_stopping_time.measurable_set_gt' MeasureTheory.IsStoppingTime.measurableSet_gt'

protected theorem measurableSet_eq' [TopologicalSpace ι] [OrderTopology ι]
    [FirstCountableTopology ι] (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[hτ.measurableSpace] {ω | τ ω = i} := by
  rw [← Set.univ_inter {ω | τ ω = i}, measurableSet_inter_eq_iff, Set.univ_inter]
  -- ⊢ MeasurableSet {ω | τ ω = i}
  exact hτ.measurableSet_eq i
  -- 🎉 no goals
#align measure_theory.is_stopping_time.measurable_set_eq' MeasureTheory.IsStoppingTime.measurableSet_eq'

protected theorem measurableSet_ge' [TopologicalSpace ι] [OrderTopology ι]
    [FirstCountableTopology ι] (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[hτ.measurableSpace] {ω | i ≤ τ ω} := by
  have : {ω | i ≤ τ ω} = {ω | τ ω = i} ∪ {ω | i < τ ω} := by
    ext1 ω
    simp only [le_iff_lt_or_eq, Set.mem_setOf_eq, Set.mem_union]
    rw [@eq_comm _ i, or_comm]
  rw [this]
  -- ⊢ MeasurableSet ({ω | τ ω = i} ∪ {ω | i < τ ω})
  exact (hτ.measurableSet_eq' i).union (hτ.measurableSet_gt' i)
  -- 🎉 no goals
#align measure_theory.is_stopping_time.measurable_set_ge' MeasureTheory.IsStoppingTime.measurableSet_ge'

protected theorem measurableSet_lt' [TopologicalSpace ι] [OrderTopology ι]
    [FirstCountableTopology ι] (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[hτ.measurableSpace] {ω | τ ω < i} := by
  have : {ω | τ ω < i} = {ω | τ ω ≤ i} \ {ω | τ ω = i} := by
    ext1 ω
    simp only [lt_iff_le_and_ne, Set.mem_setOf_eq, Set.mem_diff]
  rw [this]
  -- ⊢ MeasurableSet ({ω | τ ω ≤ i} \ {ω | τ ω = i})
  exact (hτ.measurableSet_le' i).diff (hτ.measurableSet_eq' i)
  -- 🎉 no goals
#align measure_theory.is_stopping_time.measurable_set_lt' MeasureTheory.IsStoppingTime.measurableSet_lt'

section Countable

protected theorem measurableSet_eq_of_countable_range' (hτ : IsStoppingTime f τ)
    (h_countable : (Set.range τ).Countable) (i : ι) :
    MeasurableSet[hτ.measurableSpace] {ω | τ ω = i} := by
  rw [← Set.univ_inter {ω | τ ω = i}, measurableSet_inter_eq_iff, Set.univ_inter]
  -- ⊢ MeasurableSet {ω | τ ω = i}
  exact hτ.measurableSet_eq_of_countable_range h_countable i
  -- 🎉 no goals
#align measure_theory.is_stopping_time.measurable_set_eq_of_countable_range' MeasureTheory.IsStoppingTime.measurableSet_eq_of_countable_range'

protected theorem measurableSet_eq_of_countable' [Countable ι] (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[hτ.measurableSpace] {ω | τ ω = i} :=
  hτ.measurableSet_eq_of_countable_range' (Set.to_countable _) i
#align measure_theory.is_stopping_time.measurable_set_eq_of_countable' MeasureTheory.IsStoppingTime.measurableSet_eq_of_countable'

protected theorem measurableSet_ge_of_countable_range' (hτ : IsStoppingTime f τ)
    (h_countable : (Set.range τ).Countable) (i : ι) :
    MeasurableSet[hτ.measurableSpace] {ω | i ≤ τ ω} := by
  have : {ω | i ≤ τ ω} = {ω | τ ω = i} ∪ {ω | i < τ ω} := by
    ext1 ω
    simp only [le_iff_lt_or_eq, Set.mem_setOf_eq, Set.mem_union]
    rw [@eq_comm _ i, or_comm]
  rw [this]
  -- ⊢ MeasurableSet ({ω | τ ω = i} ∪ {ω | i < τ ω})
  exact (hτ.measurableSet_eq_of_countable_range' h_countable i).union (hτ.measurableSet_gt' i)
  -- 🎉 no goals
#align measure_theory.is_stopping_time.measurable_set_ge_of_countable_range' MeasureTheory.IsStoppingTime.measurableSet_ge_of_countable_range'

protected theorem measurableSet_ge_of_countable' [Countable ι] (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[hτ.measurableSpace] {ω | i ≤ τ ω} :=
  hτ.measurableSet_ge_of_countable_range' (Set.to_countable _) i
#align measure_theory.is_stopping_time.measurable_set_ge_of_countable' MeasureTheory.IsStoppingTime.measurableSet_ge_of_countable'

protected theorem measurableSet_lt_of_countable_range' (hτ : IsStoppingTime f τ)
    (h_countable : (Set.range τ).Countable) (i : ι) :
    MeasurableSet[hτ.measurableSpace] {ω | τ ω < i} := by
  have : {ω | τ ω < i} = {ω | τ ω ≤ i} \ {ω | τ ω = i} := by
    ext1 ω
    simp only [lt_iff_le_and_ne, Set.mem_setOf_eq, Set.mem_diff]
  rw [this]
  -- ⊢ MeasurableSet ({ω | τ ω ≤ i} \ {ω | τ ω = i})
  exact (hτ.measurableSet_le' i).diff (hτ.measurableSet_eq_of_countable_range' h_countable i)
  -- 🎉 no goals
#align measure_theory.is_stopping_time.measurable_set_lt_of_countable_range' MeasureTheory.IsStoppingTime.measurableSet_lt_of_countable_range'

protected theorem measurableSet_lt_of_countable' [Countable ι] (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[hτ.measurableSpace] {ω | τ ω < i} :=
  hτ.measurableSet_lt_of_countable_range' (Set.to_countable _) i
#align measure_theory.is_stopping_time.measurable_set_lt_of_countable' MeasureTheory.IsStoppingTime.measurableSet_lt_of_countable'

protected theorem measurableSpace_le_of_countable_range (hτ : IsStoppingTime f τ)
    (h_countable : (Set.range τ).Countable) : hτ.measurableSpace ≤ m := by
  intro s hs
  -- ⊢ MeasurableSet s
  change ∀ i, MeasurableSet[f i] (s ∩ {ω | τ ω ≤ i}) at hs
  -- ⊢ MeasurableSet s
  rw [(_ : s = ⋃ i ∈ Set.range τ, s ∩ {ω | τ ω ≤ i})]
  -- ⊢ MeasurableSet (⋃ (i : ι) (_ : i ∈ Set.range τ), s ∩ {ω | τ ω ≤ i})
  · exact MeasurableSet.biUnion h_countable fun i _ => f.le i _ (hs i)
    -- 🎉 no goals
  · ext ω
    -- ⊢ ω ∈ s ↔ ω ∈ ⋃ (i : ι) (_ : i ∈ Set.range τ), s ∩ {ω | τ ω ≤ i}
    constructor <;> rw [Set.mem_iUnion]
    -- ⊢ ω ∈ s → ω ∈ ⋃ (i : ι) (_ : i ∈ Set.range τ), s ∩ {ω | τ ω ≤ i}
                    -- ⊢ ω ∈ s → ∃ i, ω ∈ ⋃ (_ : i ∈ Set.range τ), s ∩ {ω | τ ω ≤ i}
                    -- ⊢ (∃ i, ω ∈ ⋃ (_ : i ∈ Set.range τ), s ∩ {ω | τ ω ≤ i}) → ω ∈ s
    · exact fun hx => ⟨τ ω, by simpa using hx⟩
      -- 🎉 no goals
    · rintro ⟨i, hx⟩
      -- ⊢ ω ∈ s
      simp only [Set.mem_range, Set.iUnion_exists, Set.mem_iUnion, Set.mem_inter_iff,
        Set.mem_setOf_eq, exists_prop, exists_and_right] at hx
      exact hx.2.1
      -- 🎉 no goals
#align measure_theory.is_stopping_time.measurable_space_le_of_countable_range MeasureTheory.IsStoppingTime.measurableSpace_le_of_countable_range

end Countable

protected theorem measurable [TopologicalSpace ι] [MeasurableSpace ι] [BorelSpace ι]
    [OrderTopology ι] [SecondCountableTopology ι] (hτ : IsStoppingTime f τ) :
    Measurable[hτ.measurableSpace] τ :=
  @measurable_of_Iic ι Ω _ _ _ hτ.measurableSpace _ _ _ _ fun i => hτ.measurableSet_le' i
#align measure_theory.is_stopping_time.measurable MeasureTheory.IsStoppingTime.measurable

protected theorem measurable_of_le [TopologicalSpace ι] [MeasurableSpace ι] [BorelSpace ι]
    [OrderTopology ι] [SecondCountableTopology ι] (hτ : IsStoppingTime f τ) {i : ι}
    (hτ_le : ∀ ω, τ ω ≤ i) : Measurable[f i] τ :=
  hτ.measurable.mono (measurableSpace_le_of_le_const _ hτ_le) le_rfl
#align measure_theory.is_stopping_time.measurable_of_le MeasureTheory.IsStoppingTime.measurable_of_le

theorem measurableSpace_min (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) :
    (hτ.min hπ).measurableSpace = hτ.measurableSpace ⊓ hπ.measurableSpace := by
  refine' le_antisymm _ _
  -- ⊢ IsStoppingTime.measurableSpace (_ : IsStoppingTime f fun ω => min (τ ω) (π ω …
  · exact le_inf (measurableSpace_mono _ hτ fun _ => min_le_left _ _)
      (measurableSpace_mono _ hπ fun _ => min_le_right _ _)
  · intro s
    -- ⊢ MeasurableSet s → MeasurableSet s
    change MeasurableSet[hτ.measurableSpace] s ∧ MeasurableSet[hπ.measurableSpace] s →
      MeasurableSet[(hτ.min hπ).measurableSpace] s
    simp_rw [IsStoppingTime.measurableSet]
    -- ⊢ ((∀ (i : ι), MeasurableSet (s ∩ {ω | τ ω ≤ i})) ∧ ∀ (i : ι), MeasurableSet ( …
    have : ∀ i, {ω | min (τ ω) (π ω) ≤ i} = {ω | τ ω ≤ i} ∪ {ω | π ω ≤ i} := by
      intro i; ext1 ω; simp
    simp_rw [this, Set.inter_union_distrib_left]
    -- ⊢ ((∀ (i : ι), MeasurableSet (s ∩ {ω | τ ω ≤ i})) ∧ ∀ (i : ι), MeasurableSet ( …
    exact fun h i => (h.left i).union (h.right i)
    -- 🎉 no goals
#align measure_theory.is_stopping_time.measurable_space_min MeasureTheory.IsStoppingTime.measurableSpace_min

theorem measurableSet_min_iff (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) (s : Set Ω) :
    MeasurableSet[(hτ.min hπ).measurableSpace] s ↔
      MeasurableSet[hτ.measurableSpace] s ∧ MeasurableSet[hπ.measurableSpace] s := by
  rw [measurableSpace_min hτ hπ]; rfl
  -- ⊢ MeasurableSet s ↔ MeasurableSet s ∧ MeasurableSet s
                                  -- 🎉 no goals
#align measure_theory.is_stopping_time.measurable_set_min_iff MeasureTheory.IsStoppingTime.measurableSet_min_iff

theorem measurableSpace_min_const (hτ : IsStoppingTime f τ) {i : ι} :
    (hτ.min_const i).measurableSpace = hτ.measurableSpace ⊓ f i := by
  rw [hτ.measurableSpace_min (isStoppingTime_const _ i), measurableSpace_const]
  -- 🎉 no goals
#align measure_theory.is_stopping_time.measurable_space_min_const MeasureTheory.IsStoppingTime.measurableSpace_min_const

theorem measurableSet_min_const_iff (hτ : IsStoppingTime f τ) (s : Set Ω) {i : ι} :
    MeasurableSet[(hτ.min_const i).measurableSpace] s ↔
      MeasurableSet[hτ.measurableSpace] s ∧ MeasurableSet[f i] s := by
  rw [measurableSpace_min_const hτ]; apply MeasurableSpace.measurableSet_inf
  -- ⊢ MeasurableSet s ↔ MeasurableSet s ∧ MeasurableSet s
                                     -- 🎉 no goals
#align measure_theory.is_stopping_time.measurable_set_min_const_iff MeasureTheory.IsStoppingTime.measurableSet_min_const_iff

theorem measurableSet_inter_le [TopologicalSpace ι] [SecondCountableTopology ι] [OrderTopology ι]
    [MeasurableSpace ι] [BorelSpace ι] (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π)
    (s : Set Ω) (hs : MeasurableSet[hτ.measurableSpace] s) :
    MeasurableSet[(hτ.min hπ).measurableSpace] (s ∩ {ω | τ ω ≤ π ω}) := by
  simp_rw [IsStoppingTime.measurableSet] at hs ⊢
  -- ⊢ ∀ (i : ι), MeasurableSet (s ∩ {ω | τ ω ≤ π ω} ∩ {ω | min (τ ω) (π ω) ≤ i})
  intro i
  -- ⊢ MeasurableSet (s ∩ {ω | τ ω ≤ π ω} ∩ {ω | min (τ ω) (π ω) ≤ i})
  have : s ∩ {ω | τ ω ≤ π ω} ∩ {ω | min (τ ω) (π ω) ≤ i} =
      s ∩ {ω | τ ω ≤ i} ∩ {ω | min (τ ω) (π ω) ≤ i} ∩
        {ω | min (τ ω) i ≤ min (min (τ ω) (π ω)) i} := by
    ext1 ω
    simp only [min_le_iff, Set.mem_inter_iff, Set.mem_setOf_eq, le_min_iff, le_refl, true_and_iff,
      and_true_iff, true_or_iff, or_true_iff]
    by_cases hτi : τ ω ≤ i
    · simp only [hτi, true_or_iff, and_true_iff, and_congr_right_iff]
      intro
      constructor <;> intro h
      · exact Or.inl h
      · cases' h with h h
        · exact h
        · exact hτi.trans h
    simp only [hτi, false_or_iff, and_false_iff, false_and_iff, iff_false_iff, not_and, not_le,
      and_imp]
    refine' fun _ hτ_le_π => lt_of_lt_of_le _ hτ_le_π
    rw [← not_le]
    exact hτi
  rw [this]
  -- ⊢ MeasurableSet (s ∩ {ω | τ ω ≤ i} ∩ {ω | min (τ ω) (π ω) ≤ i} ∩ {ω | min (τ ω …
  refine' ((hs i).inter ((hτ.min hπ) i)).inter _
  -- ⊢ MeasurableSet {ω | min (τ ω) i ≤ min (min (τ ω) (π ω)) i}
  apply @measurableSet_le _ _ _ _ _ (Filtration.seq f i) _ _ _ _ _ ?_ ?_
  -- ⊢ Measurable fun a => min (τ a) i
  · exact (hτ.min_const i).measurable_of_le fun _ => min_le_right _ _
    -- 🎉 no goals
  · exact ((hτ.min hπ).min_const i).measurable_of_le fun _ => min_le_right _ _
    -- 🎉 no goals
#align measure_theory.is_stopping_time.measurable_set_inter_le MeasureTheory.IsStoppingTime.measurableSet_inter_le

theorem measurableSet_inter_le_iff [TopologicalSpace ι] [SecondCountableTopology ι]
    [OrderTopology ι] [MeasurableSpace ι] [BorelSpace ι] (hτ : IsStoppingTime f τ)
    (hπ : IsStoppingTime f π) (s : Set Ω) :
    MeasurableSet[hτ.measurableSpace] (s ∩ {ω | τ ω ≤ π ω}) ↔
      MeasurableSet[(hτ.min hπ).measurableSpace] (s ∩ {ω | τ ω ≤ π ω}) := by
  constructor <;> intro h
  -- ⊢ MeasurableSet (s ∩ {ω | τ ω ≤ π ω}) → MeasurableSet (s ∩ {ω | τ ω ≤ π ω})
                  -- ⊢ MeasurableSet (s ∩ {ω | τ ω ≤ π ω})
                  -- ⊢ MeasurableSet (s ∩ {ω | τ ω ≤ π ω})
  · have : s ∩ {ω | τ ω ≤ π ω} = s ∩ {ω | τ ω ≤ π ω} ∩ {ω | τ ω ≤ π ω} := by
      rw [Set.inter_assoc, Set.inter_self]
    rw [this]
    -- ⊢ MeasurableSet (s ∩ {ω | τ ω ≤ π ω} ∩ {ω | τ ω ≤ π ω})
    exact measurableSet_inter_le _ hπ _ h
    -- 🎉 no goals
  · rw [measurableSet_min_iff hτ hπ] at h
    -- ⊢ MeasurableSet (s ∩ {ω | τ ω ≤ π ω})
    exact h.1
    -- 🎉 no goals
#align measure_theory.is_stopping_time.measurable_set_inter_le_iff MeasureTheory.IsStoppingTime.measurableSet_inter_le_iff

theorem measurableSet_inter_le_const_iff (hτ : IsStoppingTime f τ) (s : Set Ω) (i : ι) :
    MeasurableSet[hτ.measurableSpace] (s ∩ {ω | τ ω ≤ i}) ↔
      MeasurableSet[(hτ.min_const i).measurableSpace] (s ∩ {ω | τ ω ≤ i}) := by
  rw [IsStoppingTime.measurableSet_min_iff hτ (isStoppingTime_const _ i),
    IsStoppingTime.measurableSpace_const, IsStoppingTime.measurableSet]
  refine' ⟨fun h => ⟨h, _⟩, fun h j => h.1 j⟩
  -- ⊢ MeasurableSet (s ∩ {ω | τ ω ≤ i})
  specialize h i
  -- ⊢ MeasurableSet (s ∩ {ω | τ ω ≤ i})
  rwa [Set.inter_assoc, Set.inter_self] at h
  -- 🎉 no goals
#align measure_theory.is_stopping_time.measurable_set_inter_le_const_iff MeasureTheory.IsStoppingTime.measurableSet_inter_le_const_iff

theorem measurableSet_le_stopping_time [TopologicalSpace ι] [SecondCountableTopology ι]
    [OrderTopology ι] [MeasurableSpace ι] [BorelSpace ι] (hτ : IsStoppingTime f τ)
    (hπ : IsStoppingTime f π) : MeasurableSet[hτ.measurableSpace] {ω | τ ω ≤ π ω} := by
  rw [hτ.measurableSet]
  -- ⊢ ∀ (i : ι), MeasurableSet ({ω | τ ω ≤ π ω} ∩ {ω | τ ω ≤ i})
  intro j
  -- ⊢ MeasurableSet ({ω | τ ω ≤ π ω} ∩ {ω | τ ω ≤ j})
  have : {ω | τ ω ≤ π ω} ∩ {ω | τ ω ≤ j} = {ω | min (τ ω) j ≤ min (π ω) j} ∩ {ω | τ ω ≤ j} := by
    ext1 ω
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, min_le_iff, le_min_iff, le_refl, and_true_iff,
      and_congr_left_iff]
    intro h
    simp only [h, or_self_iff, and_true_iff]
    by_cases hj : j ≤ π ω
    · simp only [hj, h.trans hj, or_self_iff]
    · simp only [hj, or_false_iff]
  rw [this]
  -- ⊢ MeasurableSet ({ω | min (τ ω) j ≤ min (π ω) j} ∩ {ω | τ ω ≤ j})
  refine' MeasurableSet.inter _ (hτ.measurableSet_le j)
  -- ⊢ MeasurableSet {ω | min (τ ω) j ≤ min (π ω) j}
  apply @measurableSet_le _ _ _ _ _ (Filtration.seq f j) _ _ _ _ _ ?_ ?_
  -- ⊢ Measurable fun a => min (τ a) j
  · exact (hτ.min_const j).measurable_of_le fun _ => min_le_right _ _
    -- 🎉 no goals
  · exact (hπ.min_const j).measurable_of_le fun _ => min_le_right _ _
    -- 🎉 no goals
#align measure_theory.is_stopping_time.measurable_set_le_stopping_time MeasureTheory.IsStoppingTime.measurableSet_le_stopping_time

theorem measurableSet_stopping_time_le [TopologicalSpace ι] [SecondCountableTopology ι]
    [OrderTopology ι] [MeasurableSpace ι] [BorelSpace ι] (hτ : IsStoppingTime f τ)
    (hπ : IsStoppingTime f π) : MeasurableSet[hπ.measurableSpace] {ω | τ ω ≤ π ω} := by
  suffices MeasurableSet[(hτ.min hπ).measurableSpace] {ω : Ω | τ ω ≤ π ω} by
    rw [measurableSet_min_iff hτ hπ] at this; exact this.2
  rw [← Set.univ_inter {ω : Ω | τ ω ≤ π ω}, ← hτ.measurableSet_inter_le_iff hπ, Set.univ_inter]
  -- ⊢ MeasurableSet {ω | τ ω ≤ π ω}
  exact measurableSet_le_stopping_time hτ hπ
  -- 🎉 no goals
#align measure_theory.is_stopping_time.measurable_set_stopping_time_le MeasureTheory.IsStoppingTime.measurableSet_stopping_time_le

theorem measurableSet_eq_stopping_time [AddGroup ι] [TopologicalSpace ι] [MeasurableSpace ι]
    [BorelSpace ι] [OrderTopology ι] [MeasurableSingletonClass ι] [SecondCountableTopology ι]
    [MeasurableSub₂ ι] (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) :
    MeasurableSet[hτ.measurableSpace] {ω | τ ω = π ω} := by
  rw [hτ.measurableSet]
  -- ⊢ ∀ (i : ι), MeasurableSet ({ω | τ ω = π ω} ∩ {ω | τ ω ≤ i})
  intro j
  -- ⊢ MeasurableSet ({ω | τ ω = π ω} ∩ {ω | τ ω ≤ j})
  have : {ω | τ ω = π ω} ∩ {ω | τ ω ≤ j} =
      {ω | min (τ ω) j = min (π ω) j} ∩ {ω | τ ω ≤ j} ∩ {ω | π ω ≤ j} := by
    ext1 ω
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    refine' ⟨fun h => ⟨⟨_, h.2⟩, _⟩, fun h => ⟨_, h.1.2⟩⟩
    · rw [h.1]
    · rw [← h.1]; exact h.2
    · cases' h with h' hσ_le
      cases' h' with h_eq hτ_le
      rwa [min_eq_left hτ_le, min_eq_left hσ_le] at h_eq
  rw [this]
  -- ⊢ MeasurableSet ({ω | min (τ ω) j = min (π ω) j} ∩ {ω | τ ω ≤ j} ∩ {ω | π ω ≤  …
  refine'
    MeasurableSet.inter (MeasurableSet.inter _ (hτ.measurableSet_le j)) (hπ.measurableSet_le j)
  apply measurableSet_eq_fun
  -- ⊢ Measurable fun x => min (τ x) j
  · exact (hτ.min_const j).measurable_of_le fun _ => min_le_right _ _
    -- 🎉 no goals
  · exact (hπ.min_const j).measurable_of_le fun _ => min_le_right _ _
    -- 🎉 no goals
#align measure_theory.is_stopping_time.measurable_set_eq_stopping_time MeasureTheory.IsStoppingTime.measurableSet_eq_stopping_time

theorem measurableSet_eq_stopping_time_of_countable [Countable ι] [TopologicalSpace ι]
    [MeasurableSpace ι] [BorelSpace ι] [OrderTopology ι] [MeasurableSingletonClass ι]
    [SecondCountableTopology ι] (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) :
    MeasurableSet[hτ.measurableSpace] {ω | τ ω = π ω} := by
  rw [hτ.measurableSet]
  -- ⊢ ∀ (i : ι), MeasurableSet ({ω | τ ω = π ω} ∩ {ω | τ ω ≤ i})
  intro j
  -- ⊢ MeasurableSet ({ω | τ ω = π ω} ∩ {ω | τ ω ≤ j})
  have : {ω | τ ω = π ω} ∩ {ω | τ ω ≤ j} =
      {ω | min (τ ω) j = min (π ω) j} ∩ {ω | τ ω ≤ j} ∩ {ω | π ω ≤ j} := by
    ext1 ω
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    refine' ⟨fun h => ⟨⟨_, h.2⟩, _⟩, fun h => ⟨_, h.1.2⟩⟩
    · rw [h.1]
    · rw [← h.1]; exact h.2
    · cases' h with h' hπ_le
      cases' h' with h_eq hτ_le
      rwa [min_eq_left hτ_le, min_eq_left hπ_le] at h_eq
  rw [this]
  -- ⊢ MeasurableSet ({ω | min (τ ω) j = min (π ω) j} ∩ {ω | τ ω ≤ j} ∩ {ω | π ω ≤  …
  refine'
    MeasurableSet.inter (MeasurableSet.inter _ (hτ.measurableSet_le j)) (hπ.measurableSet_le j)
  apply measurableSet_eq_fun_of_countable
  -- ⊢ Measurable fun x => min (τ x) j
  · exact (hτ.min_const j).measurable_of_le fun _ => min_le_right _ _
    -- 🎉 no goals
  · exact (hπ.min_const j).measurable_of_le fun _ => min_le_right _ _
    -- 🎉 no goals
#align measure_theory.is_stopping_time.measurable_set_eq_stopping_time_of_countable MeasureTheory.IsStoppingTime.measurableSet_eq_stopping_time_of_countable

end LinearOrder

end IsStoppingTime

section LinearOrder

/-! ## Stopped value and stopped process -/


/-- Given a map `u : ι → Ω → E`, its stopped value with respect to the stopping
time `τ` is the map `x ↦ u (τ ω) ω`. -/
def stoppedValue (u : ι → Ω → β) (τ : Ω → ι) : Ω → β := fun ω => u (τ ω) ω
#align measure_theory.stopped_value MeasureTheory.stoppedValue

theorem stoppedValue_const (u : ι → Ω → β) (i : ι) : (stoppedValue u fun _ => i) = u i :=
  rfl
#align measure_theory.stopped_value_const MeasureTheory.stoppedValue_const

variable [LinearOrder ι]

/-- Given a map `u : ι → Ω → E`, the stopped process with respect to `τ` is `u i ω` if
`i ≤ τ ω`, and `u (τ ω) ω` otherwise.

Intuitively, the stopped process stops evolving once the stopping time has occured. -/
def stoppedProcess (u : ι → Ω → β) (τ : Ω → ι) : ι → Ω → β := fun i ω => u (min i (τ ω)) ω
#align measure_theory.stopped_process MeasureTheory.stoppedProcess

theorem stoppedProcess_eq_stoppedValue {u : ι → Ω → β} {τ : Ω → ι} :
    stoppedProcess u τ = fun i => stoppedValue u fun ω => min i (τ ω) :=
  rfl
#align measure_theory.stopped_process_eq_stopped_value MeasureTheory.stoppedProcess_eq_stoppedValue

theorem stoppedValue_stoppedProcess {u : ι → Ω → β} {τ σ : Ω → ι} :
    stoppedValue (stoppedProcess u τ) σ = stoppedValue u fun ω => min (σ ω) (τ ω) :=
  rfl
#align measure_theory.stopped_value_stopped_process MeasureTheory.stoppedValue_stoppedProcess

theorem stoppedProcess_eq_of_le {u : ι → Ω → β} {τ : Ω → ι} {i : ι} {ω : Ω} (h : i ≤ τ ω) :
    stoppedProcess u τ i ω = u i ω := by simp [stoppedProcess, min_eq_left h]
                                         -- 🎉 no goals
#align measure_theory.stopped_process_eq_of_le MeasureTheory.stoppedProcess_eq_of_le

theorem stoppedProcess_eq_of_ge {u : ι → Ω → β} {τ : Ω → ι} {i : ι} {ω : Ω} (h : τ ω ≤ i) :
    stoppedProcess u τ i ω = u (τ ω) ω := by simp [stoppedProcess, min_eq_right h]
                                             -- 🎉 no goals
#align measure_theory.stopped_process_eq_of_ge MeasureTheory.stoppedProcess_eq_of_ge

section ProgMeasurable

variable [MeasurableSpace ι] [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι]
  [BorelSpace ι] [TopologicalSpace β] {u : ι → Ω → β} {τ : Ω → ι} {f : Filtration ι m}

theorem progMeasurable_min_stopping_time [MetrizableSpace ι] (hτ : IsStoppingTime f τ) :
    ProgMeasurable f fun i ω => min i (τ ω) := by
  intro i
  -- ⊢ StronglyMeasurable fun p => (fun i ω => min i (τ ω)) (↑p.fst) p.snd
  let m_prod : MeasurableSpace (Set.Iic i × Ω) := Subtype.instMeasurableSpace.prod (f i)
  -- ⊢ StronglyMeasurable fun p => (fun i ω => min i (τ ω)) (↑p.fst) p.snd
  let m_set : ∀ t : Set (Set.Iic i × Ω), MeasurableSpace t := fun _ =>
    @Subtype.instMeasurableSpace (Set.Iic i × Ω) _ m_prod
  let s := {p : Set.Iic i × Ω | τ p.2 ≤ i}
  -- ⊢ StronglyMeasurable fun p => (fun i ω => min i (τ ω)) (↑p.fst) p.snd
  have hs : MeasurableSet[m_prod] s := @measurable_snd (Set.Iic i) Ω _ (f i) _ (hτ i)
  -- ⊢ StronglyMeasurable fun p => (fun i ω => min i (τ ω)) (↑p.fst) p.snd
  have h_meas_fst : ∀ t : Set (Set.Iic i × Ω),
      Measurable[m_set t] fun x : t => ((x : Set.Iic i × Ω).fst : ι) :=
    fun t => (@measurable_subtype_coe (Set.Iic i × Ω) m_prod _).fst.subtype_val
  apply Measurable.stronglyMeasurable
  -- ⊢ Measurable fun p => (fun i ω => min i (τ ω)) (↑p.fst) p.snd
  refine' measurable_of_restrict_of_restrict_compl hs _ _
  -- ⊢ Measurable (Set.restrict s fun p => (fun i ω => min i (τ ω)) (↑p.fst) p.snd)
  · refine @Measurable.min _ _ _ _ _ (m_set s) _ _ _ _ _ (h_meas_fst s) ?_
    -- ⊢ Measurable fun a => τ (↑a).snd
    refine' @measurable_of_Iic ι s _ _ _ (m_set s) _ _ _ _ fun j => _
    -- ⊢ MeasurableSet ((fun a => τ (↑a).snd) ⁻¹' Set.Iic j)
    have h_set_eq : (fun x : s => τ (x : Set.Iic i × Ω).snd) ⁻¹' Set.Iic j =
        (fun x : s => (x : Set.Iic i × Ω).snd) ⁻¹' {ω | τ ω ≤ min i j} := by
      ext1 ω
      simp only [Set.mem_preimage, Set.mem_Iic, iff_and_self, le_min_iff, Set.mem_setOf_eq]
      exact fun _ => ω.prop
    rw [h_set_eq]
    -- ⊢ MeasurableSet ((fun x => (↑x).snd) ⁻¹' {ω | τ ω ≤ min i j})
    suffices h_meas : @Measurable _ _ (m_set s) (f i) fun x : s => (x : Set.Iic i × Ω).snd
    -- ⊢ MeasurableSet ((fun x => (↑x).snd) ⁻¹' {ω | τ ω ≤ min i j})
    exact h_meas (f.mono (min_le_left _ _) _ (hτ.measurableSet_le (min i j)))
    -- ⊢ Measurable fun x => (↑x).snd
    exact measurable_snd.comp (@measurable_subtype_coe _ m_prod _)
    -- 🎉 no goals
  · letI sc := sᶜ
    -- ⊢ Measurable (Set.restrict sᶜ fun p => (fun i ω => min i (τ ω)) (↑p.fst) p.snd)
    suffices h_min_eq_left :
      (fun x : sc => min (↑(x : Set.Iic i × Ω).fst) (τ (x : Set.Iic i × Ω).snd)) = fun x : sc =>
        ↑(x : Set.Iic i × Ω).fst
    · simp_rw [Set.restrict, h_min_eq_left]
      -- ⊢ Measurable fun x => ↑(↑x).fst
      exact h_meas_fst _
      -- 🎉 no goals
    ext1 ω
    -- ⊢ min (↑(↑ω).fst) (τ (↑ω).snd) = ↑(↑ω).fst
    rw [min_eq_left]
    -- ⊢ ↑(↑ω).fst ≤ τ (↑ω).snd
    have hx_fst_le : ↑(ω : Set.Iic i × Ω).fst ≤ i := (ω : Set.Iic i × Ω).fst.prop
    -- ⊢ ↑(↑ω).fst ≤ τ (↑ω).snd
    refine' hx_fst_le.trans (le_of_lt _)
    -- ⊢ i < τ (↑ω).snd
    convert ω.prop
    -- ⊢ i < τ (↑ω).snd ↔ ↑ω ∈ sc
    simp only [not_le, Set.mem_compl_iff, Set.mem_setOf_eq]
    -- 🎉 no goals
#align measure_theory.prog_measurable_min_stopping_time MeasureTheory.progMeasurable_min_stopping_time

theorem ProgMeasurable.stoppedProcess [MetrizableSpace ι] (h : ProgMeasurable f u)
    (hτ : IsStoppingTime f τ) : ProgMeasurable f (stoppedProcess u τ) :=
  h.comp (progMeasurable_min_stopping_time hτ) fun _ _ => min_le_left _ _
#align measure_theory.prog_measurable.stopped_process MeasureTheory.ProgMeasurable.stoppedProcess

theorem ProgMeasurable.adapted_stoppedProcess [MetrizableSpace ι] (h : ProgMeasurable f u)
    (hτ : IsStoppingTime f τ) : Adapted f (MeasureTheory.stoppedProcess u τ) :=
  (h.stoppedProcess hτ).adapted
#align measure_theory.prog_measurable.adapted_stopped_process MeasureTheory.ProgMeasurable.adapted_stoppedProcess

theorem ProgMeasurable.stronglyMeasurable_stoppedProcess [MetrizableSpace ι]
    (hu : ProgMeasurable f u) (hτ : IsStoppingTime f τ) (i : ι) :
    StronglyMeasurable (MeasureTheory.stoppedProcess u τ i) :=
  (hu.adapted_stoppedProcess hτ i).mono (f.le _)
#align measure_theory.prog_measurable.strongly_measurable_stopped_process MeasureTheory.ProgMeasurable.stronglyMeasurable_stoppedProcess

theorem stronglyMeasurable_stoppedValue_of_le (h : ProgMeasurable f u) (hτ : IsStoppingTime f τ)
    {n : ι} (hτ_le : ∀ ω, τ ω ≤ n) : StronglyMeasurable[f n] (stoppedValue u τ) := by
  have : stoppedValue u τ =
      (fun p : Set.Iic n × Ω => u (↑p.fst) p.snd) ∘ fun ω => (⟨τ ω, hτ_le ω⟩, ω) := by
    ext1 ω; simp only [stoppedValue, Function.comp_apply, Subtype.coe_mk]
  rw [this]
  -- ⊢ StronglyMeasurable ((fun p => u (↑p.fst) p.snd) ∘ fun ω => ({ val := τ ω, pr …
  refine' StronglyMeasurable.comp_measurable (h n) _
  -- ⊢ Measurable fun ω => ({ val := τ ω, property := (_ : τ ω ≤ n) }, ω)
  exact (hτ.measurable_of_le hτ_le).subtype_mk.prod_mk measurable_id
  -- 🎉 no goals
#align measure_theory.strongly_measurable_stopped_value_of_le MeasureTheory.stronglyMeasurable_stoppedValue_of_le

theorem measurable_stoppedValue [MetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
    (hf_prog : ProgMeasurable f u) (hτ : IsStoppingTime f τ) :
    Measurable[hτ.measurableSpace] (stoppedValue u τ) := by
  have h_str_meas : ∀ i, StronglyMeasurable[f i] (stoppedValue u fun ω => min (τ ω) i) := fun i =>
    stronglyMeasurable_stoppedValue_of_le hf_prog (hτ.min_const i) fun _ => min_le_right _ _
  intro t ht i
  -- ⊢ MeasurableSet (stoppedValue u τ ⁻¹' t ∩ {ω | τ ω ≤ i})
  suffices stoppedValue u τ ⁻¹' t ∩ {ω : Ω | τ ω ≤ i} =
      (stoppedValue u fun ω => min (τ ω) i) ⁻¹' t ∩ {ω : Ω | τ ω ≤ i} by
    rw [this]; exact ((h_str_meas i).measurable ht).inter (hτ.measurableSet_le i)
  ext1 ω
  -- ⊢ ω ∈ stoppedValue u τ ⁻¹' t ∩ {ω | τ ω ≤ i} ↔ ω ∈ (stoppedValue u fun ω => mi …
  simp only [stoppedValue, Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq,
    and_congr_left_iff]
  intro h
  -- ⊢ u (τ ω) ω ∈ t ↔ u (min (τ ω) i) ω ∈ t
  rw [min_eq_left h]
  -- 🎉 no goals
#align measure_theory.measurable_stopped_value MeasureTheory.measurable_stoppedValue

end ProgMeasurable

end LinearOrder

section StoppedValueOfMemFinset

variable {μ : Measure Ω} {τ σ : Ω → ι} {E : Type*} {p : ℝ≥0∞} {u : ι → Ω → E}

theorem stoppedValue_eq_of_mem_finset [AddCommMonoid E] {s : Finset ι} (hbdd : ∀ ω, τ ω ∈ s) :
    stoppedValue u τ = ∑ i in s, Set.indicator {ω | τ ω = i} (u i) := by
  ext y
  -- ⊢ stoppedValue u τ y = Finset.sum s (fun i => Set.indicator {ω | τ ω = i} (u i …
  rw [stoppedValue, Finset.sum_apply, Finset.sum_indicator_eq_sum_filter]
  -- ⊢ u (τ y) y = ∑ i in Finset.filter (fun i => y ∈ {ω | τ ω = i}) s, u i y
  suffices Finset.filter (fun i => y ∈ {ω : Ω | τ ω = i}) s = ({τ y} : Finset ι) by
    rw [this, Finset.sum_singleton]
  ext1 ω
  -- ⊢ ω ∈ Finset.filter (fun i => y ∈ {ω | τ ω = i}) s ↔ ω ∈ {τ y}
  simp only [Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_singleton]
  -- ⊢ ω ∈ s ∧ τ y = ω ↔ ω = τ y
  constructor <;> intro h
  -- ⊢ ω ∈ s ∧ τ y = ω → ω = τ y
                  -- ⊢ ω = τ y
                  -- ⊢ ω ∈ s ∧ τ y = ω
  · exact h.2.symm
    -- 🎉 no goals
  · refine' ⟨_, h.symm⟩; rw [h]; exact hbdd y
    -- ⊢ ω ∈ s
                         -- ⊢ τ y ∈ s
                                 -- 🎉 no goals
#align measure_theory.stopped_value_eq_of_mem_finset MeasureTheory.stoppedValue_eq_of_mem_finset

theorem stoppedValue_eq' [Preorder ι] [LocallyFiniteOrderBot ι] [AddCommMonoid E] {N : ι}
    (hbdd : ∀ ω, τ ω ≤ N) :
    stoppedValue u τ = ∑ i in Finset.Iic N, Set.indicator {ω | τ ω = i} (u i) :=
  stoppedValue_eq_of_mem_finset fun ω => Finset.mem_Iic.mpr (hbdd ω)
#align measure_theory.stopped_value_eq' MeasureTheory.stoppedValue_eq'

theorem stoppedProcess_eq_of_mem_finset [LinearOrder ι] [AddCommMonoid E] {s : Finset ι} (n : ι)
    (hbdd : ∀ ω, τ ω < n → τ ω ∈ s) : stoppedProcess u τ n = Set.indicator {a | n ≤ τ a} (u n) +
      ∑ i in s.filter (· < n), Set.indicator {ω | τ ω = i} (u i) := by
  ext ω
  -- ⊢ stoppedProcess u τ n ω = (Set.indicator {a | n ≤ τ a} (u n) + ∑ i in Finset. …
  rw [Pi.add_apply, Finset.sum_apply]
  -- ⊢ stoppedProcess u τ n ω = Set.indicator {a | n ≤ τ a} (u n) ω + ∑ c in Finset …
  cases' le_or_lt n (τ ω) with h h
  -- ⊢ stoppedProcess u τ n ω = Set.indicator {a | n ≤ τ a} (u n) ω + ∑ c in Finset …
  · rw [stoppedProcess_eq_of_le h, Set.indicator_of_mem, Finset.sum_eq_zero, add_zero]
    -- ⊢ ∀ (x : ι), x ∈ Finset.filter (fun x => x < n) s → Set.indicator {ω | τ ω = x …
    · intro m hm
      -- ⊢ Set.indicator {ω | τ ω = m} (u m) ω = 0
      refine' Set.indicator_of_not_mem _ _
      -- ⊢ ¬ω ∈ {ω | τ ω = m}
      rw [Finset.mem_filter] at hm
      -- ⊢ ¬ω ∈ {ω | τ ω = m}
      exact (hm.2.trans_le h).ne'
      -- 🎉 no goals
    · exact h
      -- 🎉 no goals
  · rw [stoppedProcess_eq_of_ge (le_of_lt h), Finset.sum_eq_single_of_mem (τ ω)]
    · rw [Set.indicator_of_not_mem, zero_add, Set.indicator_of_mem]
      -- ⊢ ω ∈ {ω_1 | τ ω_1 = τ ω}
      · exact rfl
        -- 🎉 no goals
      -- refl does not work
      · exact not_le.2 h
        -- 🎉 no goals
    · rw [Finset.mem_filter]
      -- ⊢ τ ω ∈ s ∧ τ ω < n
      exact ⟨hbdd ω h, h⟩
      -- 🎉 no goals
    · intro b _ hneq
      -- ⊢ Set.indicator {ω | τ ω = b} (u b) ω = 0
      rw [Set.indicator_of_not_mem]
      -- ⊢ ¬ω ∈ {ω | τ ω = b}
      exact hneq.symm
      -- 🎉 no goals
#align measure_theory.stopped_process_eq_of_mem_finset MeasureTheory.stoppedProcess_eq_of_mem_finset

theorem stoppedProcess_eq'' [LinearOrder ι] [LocallyFiniteOrderBot ι] [AddCommMonoid E] (n : ι) :
    stoppedProcess u τ n = Set.indicator {a | n ≤ τ a} (u n) +
      ∑ i in Finset.Iio n, Set.indicator {ω | τ ω = i} (u i) := by
  have h_mem : ∀ ω, τ ω < n → τ ω ∈ Finset.Iio n := fun ω h => Finset.mem_Iio.mpr h
  -- ⊢ stoppedProcess u τ n = Set.indicator {a | n ≤ τ a} (u n) + ∑ i in Finset.Iio …
  rw [stoppedProcess_eq_of_mem_finset n h_mem]
  -- ⊢ Set.indicator {a | n ≤ τ a} (u n) + ∑ i in Finset.filter (fun x => x < n) (F …
  congr with i
  -- ⊢ i ∈ Finset.filter (fun x => x < n) (Finset.Iio n) ↔ i ∈ Finset.Iio n
  simp
  -- 🎉 no goals
#align measure_theory.stopped_process_eq'' MeasureTheory.stoppedProcess_eq''

section StoppedValue

variable [PartialOrder ι] {ℱ : Filtration ι m} [NormedAddCommGroup E]

theorem memℒp_stoppedValue_of_mem_finset (hτ : IsStoppingTime ℱ τ) (hu : ∀ n, Memℒp (u n) p μ)
    {s : Finset ι} (hbdd : ∀ ω, τ ω ∈ s) : Memℒp (stoppedValue u τ) p μ := by
  rw [stoppedValue_eq_of_mem_finset hbdd]
  -- ⊢ Memℒp (∑ i in s, Set.indicator {ω | τ ω = i} (u i)) p
  refine' memℒp_finset_sum' _ fun i _ => Memℒp.indicator _ (hu i)
  -- ⊢ MeasurableSet {ω | τ ω = i}
  refine' ℱ.le i {a : Ω | τ a = i} (hτ.measurableSet_eq_of_countable_range _ i)
  -- ⊢ Set.Countable (Set.range τ)
  refine' ((Finset.finite_toSet s).subset fun ω hω => _).countable
  -- ⊢ ω ∈ ↑s
  obtain ⟨y, rfl⟩ := hω
  -- ⊢ τ y ∈ ↑s
  exact hbdd y
  -- 🎉 no goals
#align measure_theory.mem_ℒp_stopped_value_of_mem_finset MeasureTheory.memℒp_stoppedValue_of_mem_finset

theorem memℒp_stoppedValue [LocallyFiniteOrderBot ι] (hτ : IsStoppingTime ℱ τ)
    (hu : ∀ n, Memℒp (u n) p μ) {N : ι} (hbdd : ∀ ω, τ ω ≤ N) : Memℒp (stoppedValue u τ) p μ :=
  memℒp_stoppedValue_of_mem_finset hτ hu fun ω => Finset.mem_Iic.mpr (hbdd ω)
#align measure_theory.mem_ℒp_stopped_value MeasureTheory.memℒp_stoppedValue

theorem integrable_stoppedValue_of_mem_finset (hτ : IsStoppingTime ℱ τ)
    (hu : ∀ n, Integrable (u n) μ) {s : Finset ι} (hbdd : ∀ ω, τ ω ∈ s) :
    Integrable (stoppedValue u τ) μ := by
  simp_rw [← memℒp_one_iff_integrable] at hu ⊢
  -- ⊢ Memℒp (stoppedValue u τ) 1
  exact memℒp_stoppedValue_of_mem_finset hτ hu hbdd
  -- 🎉 no goals
#align measure_theory.integrable_stopped_value_of_mem_finset MeasureTheory.integrable_stoppedValue_of_mem_finset

variable (ι)

theorem integrable_stoppedValue [LocallyFiniteOrderBot ι] (hτ : IsStoppingTime ℱ τ)
    (hu : ∀ n, Integrable (u n) μ) {N : ι} (hbdd : ∀ ω, τ ω ≤ N) :
    Integrable (stoppedValue u τ) μ :=
  integrable_stoppedValue_of_mem_finset hτ hu fun ω => Finset.mem_Iic.mpr (hbdd ω)
#align measure_theory.integrable_stopped_value MeasureTheory.integrable_stoppedValue

end StoppedValue

section StoppedProcess

variable [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι] [FirstCountableTopology ι]
  {ℱ : Filtration ι m} [NormedAddCommGroup E]

theorem memℒp_stoppedProcess_of_mem_finset (hτ : IsStoppingTime ℱ τ) (hu : ∀ n, Memℒp (u n) p μ)
    (n : ι) {s : Finset ι} (hbdd : ∀ ω, τ ω < n → τ ω ∈ s) : Memℒp (stoppedProcess u τ n) p μ := by
  rw [stoppedProcess_eq_of_mem_finset n hbdd]
  -- ⊢ Memℒp (Set.indicator {a | n ≤ τ a} (u n) + ∑ i in Finset.filter (fun x => x  …
  refine' Memℒp.add _ _
  -- ⊢ Memℒp (Set.indicator {a | n ≤ τ a} (u n)) p
  · exact Memℒp.indicator (ℱ.le n {a : Ω | n ≤ τ a} (hτ.measurableSet_ge n)) (hu n)
    -- 🎉 no goals
  · suffices Memℒp (fun ω => ∑ i in s.filter (· < n), {a : Ω | τ a = i}.indicator (u i) ω) p μ by
      convert this using 1; ext1 ω; simp only [Finset.sum_apply]
    refine' memℒp_finset_sum _ fun i _ => Memℒp.indicator _ (hu i)
    -- ⊢ MeasurableSet {a | τ a = i}
    exact ℱ.le i {a : Ω | τ a = i} (hτ.measurableSet_eq i)
    -- 🎉 no goals
#align measure_theory.mem_ℒp_stopped_process_of_mem_finset MeasureTheory.memℒp_stoppedProcess_of_mem_finset

theorem memℒp_stoppedProcess [LocallyFiniteOrderBot ι] (hτ : IsStoppingTime ℱ τ)
    (hu : ∀ n, Memℒp (u n) p μ) (n : ι) : Memℒp (stoppedProcess u τ n) p μ :=
  memℒp_stoppedProcess_of_mem_finset hτ hu n fun _ h => Finset.mem_Iio.mpr h
#align measure_theory.mem_ℒp_stopped_process MeasureTheory.memℒp_stoppedProcess

theorem integrable_stoppedProcess_of_mem_finset (hτ : IsStoppingTime ℱ τ)
    (hu : ∀ n, Integrable (u n) μ) (n : ι) {s : Finset ι} (hbdd : ∀ ω, τ ω < n → τ ω ∈ s) :
    Integrable (stoppedProcess u τ n) μ := by
  simp_rw [← memℒp_one_iff_integrable] at hu ⊢
  -- ⊢ Memℒp (stoppedProcess u τ n) 1
  exact memℒp_stoppedProcess_of_mem_finset hτ hu n hbdd
  -- 🎉 no goals
#align measure_theory.integrable_stopped_process_of_mem_finset MeasureTheory.integrable_stoppedProcess_of_mem_finset

theorem integrable_stoppedProcess [LocallyFiniteOrderBot ι] (hτ : IsStoppingTime ℱ τ)
    (hu : ∀ n, Integrable (u n) μ) (n : ι) : Integrable (stoppedProcess u τ n) μ :=
  integrable_stoppedProcess_of_mem_finset hτ hu n fun _ h => Finset.mem_Iio.mpr h
#align measure_theory.integrable_stopped_process MeasureTheory.integrable_stoppedProcess

end StoppedProcess

end StoppedValueOfMemFinset

section AdaptedStoppedProcess

variable [TopologicalSpace β] [PseudoMetrizableSpace β] [LinearOrder ι] [TopologicalSpace ι]
  [SecondCountableTopology ι] [OrderTopology ι] [MeasurableSpace ι] [BorelSpace ι]
  {f : Filtration ι m} {u : ι → Ω → β} {τ : Ω → ι}

/-- The stopped process of an adapted process with continuous paths is adapted. -/
theorem Adapted.stoppedProcess [MetrizableSpace ι] (hu : Adapted f u)
    (hu_cont : ∀ ω, Continuous fun i => u i ω) (hτ : IsStoppingTime f τ) :
    Adapted f (stoppedProcess u τ) :=
  ((hu.progMeasurable_of_continuous hu_cont).stoppedProcess hτ).adapted
#align measure_theory.adapted.stopped_process MeasureTheory.Adapted.stoppedProcess

/-- If the indexing order has the discrete topology, then the stopped process of an adapted process
is adapted. -/
theorem Adapted.stoppedProcess_of_discrete [DiscreteTopology ι] (hu : Adapted f u)
    (hτ : IsStoppingTime f τ) : Adapted f (MeasureTheory.stoppedProcess u τ) :=
  (hu.progMeasurable_of_discrete.stoppedProcess hτ).adapted
#align measure_theory.adapted.stopped_process_of_discrete MeasureTheory.Adapted.stoppedProcess_of_discrete

theorem Adapted.stronglyMeasurable_stoppedProcess [MetrizableSpace ι] (hu : Adapted f u)
    (hu_cont : ∀ ω, Continuous fun i => u i ω) (hτ : IsStoppingTime f τ) (n : ι) :
    StronglyMeasurable (MeasureTheory.stoppedProcess u τ n) :=
  (hu.progMeasurable_of_continuous hu_cont).stronglyMeasurable_stoppedProcess hτ n
#align measure_theory.adapted.strongly_measurable_stopped_process MeasureTheory.Adapted.stronglyMeasurable_stoppedProcess

theorem Adapted.stronglyMeasurable_stoppedProcess_of_discrete [DiscreteTopology ι]
    (hu : Adapted f u) (hτ : IsStoppingTime f τ) (n : ι) :
    StronglyMeasurable (MeasureTheory.stoppedProcess u τ n) :=
  hu.progMeasurable_of_discrete.stronglyMeasurable_stoppedProcess hτ n
#align measure_theory.adapted.strongly_measurable_stopped_process_of_discrete MeasureTheory.Adapted.stronglyMeasurable_stoppedProcess_of_discrete

end AdaptedStoppedProcess

section Nat

/-! ### Filtrations indexed by `ℕ` -/


open Filtration

variable {f : Filtration ℕ m} {u : ℕ → Ω → β} {τ π : Ω → ℕ}

theorem stoppedValue_sub_eq_sum [AddCommGroup β] (hle : τ ≤ π) :
    stoppedValue u π - stoppedValue u τ = fun ω =>
      (∑ i in Finset.Ico (τ ω) (π ω), (u (i + 1) - u i)) ω := by
  ext ω
  -- ⊢ (stoppedValue u π - stoppedValue u τ) ω = Finset.sum (Finset.Ico (τ ω) (π ω) …
  rw [Finset.sum_Ico_eq_sub _ (hle ω), Finset.sum_range_sub, Finset.sum_range_sub]
  -- ⊢ (stoppedValue u π - stoppedValue u τ) ω = (u (π ω) - u 0 - (u (τ ω) - u 0)) ω
  simp [stoppedValue]
  -- 🎉 no goals
#align measure_theory.stopped_value_sub_eq_sum MeasureTheory.stoppedValue_sub_eq_sum

theorem stoppedValue_sub_eq_sum' [AddCommGroup β] (hle : τ ≤ π) {N : ℕ} (hbdd : ∀ ω, π ω ≤ N) :
    stoppedValue u π - stoppedValue u τ = fun ω =>
      (∑ i in Finset.range (N + 1), Set.indicator {ω | τ ω ≤ i ∧ i < π ω} (u (i + 1) - u i)) ω := by
  rw [stoppedValue_sub_eq_sum hle]
  -- ⊢ (fun ω => Finset.sum (Finset.Ico (τ ω) (π ω)) (fun i => u (i + 1) - u i) ω)  …
  ext ω
  -- ⊢ Finset.sum (Finset.Ico (τ ω) (π ω)) (fun i => u (i + 1) - u i) ω = Finset.su …
  simp only [Finset.sum_apply, Finset.sum_indicator_eq_sum_filter]
  -- ⊢ ∑ c in Finset.Ico (τ ω) (π ω), (u (c + 1) - u c) ω = ∑ c in Finset.filter (f …
  refine' Finset.sum_congr _ fun _ _ => rfl
  -- ⊢ Finset.Ico (τ ω) (π ω) = Finset.filter (fun i => ω ∈ {ω | τ ω ≤ i ∧ i < π ω} …
  ext i
  -- ⊢ i ∈ Finset.Ico (τ ω) (π ω) ↔ i ∈ Finset.filter (fun i => ω ∈ {ω | τ ω ≤ i ∧  …
  simp only [Finset.mem_filter, Set.mem_setOf_eq, Finset.mem_range, Finset.mem_Ico]
  -- ⊢ τ ω ≤ i ∧ i < π ω ↔ i < N + 1 ∧ τ ω ≤ i ∧ i < π ω
  exact ⟨fun h => ⟨lt_trans h.2 (Nat.lt_succ_iff.2 <| hbdd _), h⟩, fun h => h.2⟩
  -- 🎉 no goals
#align measure_theory.stopped_value_sub_eq_sum' MeasureTheory.stoppedValue_sub_eq_sum'

section AddCommMonoid

variable [AddCommMonoid β]

theorem stoppedValue_eq {N : ℕ} (hbdd : ∀ ω, τ ω ≤ N) : stoppedValue u τ = fun x =>
    (∑ i in Finset.range (N + 1), Set.indicator {ω | τ ω = i} (u i)) x :=
  stoppedValue_eq_of_mem_finset fun ω => Finset.mem_range_succ_iff.mpr (hbdd ω)
#align measure_theory.stopped_value_eq MeasureTheory.stoppedValue_eq

theorem stoppedProcess_eq (n : ℕ) : stoppedProcess u τ n = Set.indicator {a | n ≤ τ a} (u n) +
    ∑ i in Finset.range n, Set.indicator {ω | τ ω = i} (u i) := by
  rw [stoppedProcess_eq'' n]
  -- ⊢ Set.indicator {a | n ≤ τ a} (u n) + ∑ i in Finset.Iio n, Set.indicator {ω |  …
  congr with i
  -- ⊢ i ∈ Finset.Iio n ↔ i ∈ Finset.range n
  rw [Finset.mem_Iio, Finset.mem_range]
  -- 🎉 no goals
#align measure_theory.stopped_process_eq MeasureTheory.stoppedProcess_eq

theorem stoppedProcess_eq' (n : ℕ) : stoppedProcess u τ n = Set.indicator {a | n + 1 ≤ τ a} (u n) +
    ∑ i in Finset.range (n + 1), Set.indicator {a | τ a = i} (u i) := by
  have : {a | n ≤ τ a}.indicator (u n) =
      {a | n + 1 ≤ τ a}.indicator (u n) + {a | τ a = n}.indicator (u n) := by
    ext x
    rw [add_comm, Pi.add_apply, ← Set.indicator_union_of_not_mem_inter]
    · simp_rw [@eq_comm _ _ n, @le_iff_eq_or_lt _ _ n, Nat.succ_le_iff]
      rfl
    · rintro ⟨h₁, h₂⟩
      exact (Nat.succ_le_iff.1 h₂).ne h₁.symm
  rw [stoppedProcess_eq, this, Finset.sum_range_succ_comm, ← add_assoc]
  -- 🎉 no goals
#align measure_theory.stopped_process_eq' MeasureTheory.stoppedProcess_eq'

end AddCommMonoid

end Nat

section PiecewiseConst

variable [Preorder ι] {𝒢 : Filtration ι m} {τ η : Ω → ι} {i j : ι} {s : Set Ω}
  [DecidablePred (· ∈ s)]

/-- Given stopping times `τ` and `η` which are bounded below, `Set.piecewise s τ η` is also
a stopping time with respect to the same filtration. -/
theorem IsStoppingTime.piecewise_of_le (hτ_st : IsStoppingTime 𝒢 τ) (hη_st : IsStoppingTime 𝒢 η)
    (hτ : ∀ ω, i ≤ τ ω) (hη : ∀ ω, i ≤ η ω) (hs : MeasurableSet[𝒢 i] s) :
    IsStoppingTime 𝒢 (s.piecewise τ η) := by
  intro n
  -- ⊢ MeasurableSet {ω | Set.piecewise s τ η ω ≤ n}
  have : {ω | s.piecewise τ η ω ≤ n} = s ∩ {ω | τ ω ≤ n} ∪ sᶜ ∩ {ω | η ω ≤ n} := by
    ext1 ω
    simp only [Set.piecewise, Set.mem_inter_iff, Set.mem_setOf_eq, and_congr_right_iff]
    by_cases hx : ω ∈ s <;> simp [hx]
  rw [this]
  -- ⊢ MeasurableSet (s ∩ {ω | τ ω ≤ n} ∪ sᶜ ∩ {ω | η ω ≤ n})
  by_cases hin : i ≤ n
  -- ⊢ MeasurableSet (s ∩ {ω | τ ω ≤ n} ∪ sᶜ ∩ {ω | η ω ≤ n})
  · have hs_n : MeasurableSet[𝒢 n] s := 𝒢.mono hin _ hs
    -- ⊢ MeasurableSet (s ∩ {ω | τ ω ≤ n} ∪ sᶜ ∩ {ω | η ω ≤ n})
    exact (hs_n.inter (hτ_st n)).union (hs_n.compl.inter (hη_st n))
    -- 🎉 no goals
  · have hτn : ∀ ω, ¬τ ω ≤ n := fun ω hτn => hin ((hτ ω).trans hτn)
    -- ⊢ MeasurableSet (s ∩ {ω | τ ω ≤ n} ∪ sᶜ ∩ {ω | η ω ≤ n})
    have hηn : ∀ ω, ¬η ω ≤ n := fun ω hηn => hin ((hη ω).trans hηn)
    -- ⊢ MeasurableSet (s ∩ {ω | τ ω ≤ n} ∪ sᶜ ∩ {ω | η ω ≤ n})
    simp [hτn, hηn, @MeasurableSet.empty _ _]
    -- 🎉 no goals
#align measure_theory.is_stopping_time.piecewise_of_le MeasureTheory.IsStoppingTime.piecewise_of_le

theorem isStoppingTime_piecewise_const (hij : i ≤ j) (hs : MeasurableSet[𝒢 i] s) :
    IsStoppingTime 𝒢 (s.piecewise (fun _ => i) fun _ => j) :=
  (isStoppingTime_const 𝒢 i).piecewise_of_le (isStoppingTime_const 𝒢 j) (fun _ => le_rfl)
    (fun _ => hij) hs
#align measure_theory.is_stopping_time_piecewise_const MeasureTheory.isStoppingTime_piecewise_const

theorem stoppedValue_piecewise_const {ι' : Type*} {i j : ι'} {f : ι' → Ω → ℝ} :
    stoppedValue f (s.piecewise (fun _ => i) fun _ => j) = s.piecewise (f i) (f j) := by
  ext ω; rw [stoppedValue]; by_cases hx : ω ∈ s <;> simp [hx]
  -- ⊢ stoppedValue f (Set.piecewise s (fun x => i) fun x => j) ω = Set.piecewise s …
         -- ⊢ f (Set.piecewise s (fun x => i) (fun x => j) ω) ω = Set.piecewise s (f i) (f …
                            -- ⊢ f (Set.piecewise s (fun x => i) (fun x => j) ω) ω = Set.piecewise s (f i) (f …
                                                    -- 🎉 no goals
                                                    -- 🎉 no goals
#align measure_theory.stopped_value_piecewise_const MeasureTheory.stoppedValue_piecewise_const

theorem stoppedValue_piecewise_const' {ι' : Type*} {i j : ι'} {f : ι' → Ω → ℝ} :
    stoppedValue f (s.piecewise (fun _ => i) fun _ => j) =
    s.indicator (f i) + sᶜ.indicator (f j) := by
  ext ω; rw [stoppedValue]; by_cases hx : ω ∈ s <;> simp [hx]
  -- ⊢ stoppedValue f (Set.piecewise s (fun x => i) fun x => j) ω = (Set.indicator  …
         -- ⊢ f (Set.piecewise s (fun x => i) (fun x => j) ω) ω = (Set.indicator s (f i) + …
                            -- ⊢ f (Set.piecewise s (fun x => i) (fun x => j) ω) ω = (Set.indicator s (f i) + …
                                                    -- 🎉 no goals
                                                    -- 🎉 no goals
#align measure_theory.stopped_value_piecewise_const' MeasureTheory.stoppedValue_piecewise_const'

end PiecewiseConst

section Condexp

/-! ### Conditional expectation with respect to the σ-algebra generated by a stopping time -/


variable [LinearOrder ι] {μ : Measure Ω} {ℱ : Filtration ι m} {τ σ : Ω → ι} {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f : Ω → E}

theorem condexp_stopping_time_ae_eq_restrict_eq_of_countable_range [SigmaFiniteFiltration μ ℱ]
    (hτ : IsStoppingTime ℱ τ) (h_countable : (Set.range τ).Countable)
    [SigmaFinite (μ.trim (hτ.measurableSpace_le_of_countable_range h_countable))] (i : ι) :
    μ[f|hτ.measurableSpace] =ᵐ[μ.restrict {x | τ x = i}] μ[f|ℱ i] := by
  refine' condexp_ae_eq_restrict_of_measurableSpace_eq_on
    (hτ.measurableSpace_le_of_countable_range h_countable) (ℱ.le i)
    (hτ.measurableSet_eq_of_countable_range' h_countable i) fun t => _
  rw [Set.inter_comm _ t, IsStoppingTime.measurableSet_inter_eq_iff]
  -- 🎉 no goals
#align measure_theory.condexp_stopping_time_ae_eq_restrict_eq_of_countable_range MeasureTheory.condexp_stopping_time_ae_eq_restrict_eq_of_countable_range

theorem condexp_stopping_time_ae_eq_restrict_eq_of_countable [Countable ι]
    [SigmaFiniteFiltration μ ℱ] (hτ : IsStoppingTime ℱ τ)
    [SigmaFinite (μ.trim hτ.measurableSpace_le_of_countable)] (i : ι) :
    μ[f|hτ.measurableSpace] =ᵐ[μ.restrict {x | τ x = i}] μ[f|ℱ i] :=
  condexp_stopping_time_ae_eq_restrict_eq_of_countable_range hτ (Set.to_countable _) i
#align measure_theory.condexp_stopping_time_ae_eq_restrict_eq_of_countable MeasureTheory.condexp_stopping_time_ae_eq_restrict_eq_of_countable

variable [(Filter.atTop : Filter ι).IsCountablyGenerated]

theorem condexp_min_stopping_time_ae_eq_restrict_le_const (hτ : IsStoppingTime ℱ τ) (i : ι)
    [SigmaFinite (μ.trim (hτ.min_const i).measurableSpace_le)] :
    μ[f|(hτ.min_const i).measurableSpace] =ᵐ[μ.restrict {x | τ x ≤ i}] μ[f|hτ.measurableSpace] := by
  have : SigmaFinite (μ.trim hτ.measurableSpace_le) :=
    haveI h_le : (hτ.min_const i).measurableSpace ≤ hτ.measurableSpace := by
      rw [IsStoppingTime.measurableSpace_min_const]
      exact inf_le_left
    sigmaFiniteTrim_mono _ h_le
  refine' (condexp_ae_eq_restrict_of_measurableSpace_eq_on hτ.measurableSpace_le
    (hτ.min_const i).measurableSpace_le (hτ.measurableSet_le' i) fun t => _).symm
  rw [Set.inter_comm _ t, hτ.measurableSet_inter_le_const_iff]
  -- 🎉 no goals
#align measure_theory.condexp_min_stopping_time_ae_eq_restrict_le_const MeasureTheory.condexp_min_stopping_time_ae_eq_restrict_le_const

variable [TopologicalSpace ι] [OrderTopology ι]

theorem condexp_stopping_time_ae_eq_restrict_eq [FirstCountableTopology ι]
    [SigmaFiniteFiltration μ ℱ] (hτ : IsStoppingTime ℱ τ)
    [SigmaFinite (μ.trim hτ.measurableSpace_le)] (i : ι) :
    μ[f|hτ.measurableSpace] =ᵐ[μ.restrict {x | τ x = i}] μ[f|ℱ i] := by
  refine' condexp_ae_eq_restrict_of_measurableSpace_eq_on hτ.measurableSpace_le (ℱ.le i)
    (hτ.measurableSet_eq' i) fun t => _
  rw [Set.inter_comm _ t, IsStoppingTime.measurableSet_inter_eq_iff]
  -- 🎉 no goals
#align measure_theory.condexp_stopping_time_ae_eq_restrict_eq MeasureTheory.condexp_stopping_time_ae_eq_restrict_eq

theorem condexp_min_stopping_time_ae_eq_restrict_le [MeasurableSpace ι] [SecondCountableTopology ι]
    [BorelSpace ι] (hτ : IsStoppingTime ℱ τ) (hσ : IsStoppingTime ℱ σ)
    [SigmaFinite (μ.trim (hτ.min hσ).measurableSpace_le)] :
    μ[f|(hτ.min hσ).measurableSpace] =ᵐ[μ.restrict {x | τ x ≤ σ x}] μ[f|hτ.measurableSpace] := by
  have : SigmaFinite (μ.trim hτ.measurableSpace_le) :=
    haveI h_le : (hτ.min hσ).measurableSpace ≤ hτ.measurableSpace := by
      rw [IsStoppingTime.measurableSpace_min]
      exact inf_le_left; simp_all only
    sigmaFiniteTrim_mono _ h_le
  refine' (condexp_ae_eq_restrict_of_measurableSpace_eq_on hτ.measurableSpace_le
    (hτ.min hσ).measurableSpace_le (hτ.measurableSet_le_stopping_time hσ) fun t => _).symm
  rw [Set.inter_comm _ t, IsStoppingTime.measurableSet_inter_le_iff]; simp_all only
  -- ⊢ IsStoppingTime ℱ fun ω => σ ω
                                                                      -- 🎉 no goals
#align measure_theory.condexp_min_stopping_time_ae_eq_restrict_le MeasureTheory.condexp_min_stopping_time_ae_eq_restrict_le

end Condexp

end MeasureTheory
