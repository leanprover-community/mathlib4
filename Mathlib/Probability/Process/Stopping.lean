/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Rémy Degenne
-/
import Mathlib.Probability.Process.Adapted
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop

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
* `memLp_stoppedProcess`: if a process belongs to `ℒp` at every time in `ℕ`, then its stopped
  process belongs to `ℒp` as well.

## Tags

stopping time, stochastic process

-/

open Filter Order TopologicalSpace

open scoped MeasureTheory NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω β ι : Type*} {m : MeasurableSpace Ω}

/-! ### Stopping times -/


/-- A stopping time with respect to some filtration `f` is a function
`τ` such that for all `i`, the preimage of `{j | j ≤ i}` along `τ` is measurable
with respect to `f i`.

Intuitively, the stopping time `τ` describes some stopping rule such that at time
`i`, we may determine it with the information we have at time `i`. -/
def IsStoppingTime [Preorder ι] (f : Filtration ι m) (τ : Ω → WithTop ι) :=
  ∀ i : ι, MeasurableSet[f i] <| {ω | τ ω ≤ i}

theorem isStoppingTime_const [Preorder ι] (f : Filtration ι m) (i : ι) :
    IsStoppingTime f fun _ => i := fun j => by simp only [MeasurableSet.const]

section MeasurableSet

section Preorder

variable [Preorder ι] {f : Filtration ι m} {τ : Ω → WithTop ι}

protected theorem IsStoppingTime.measurableSet_le (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[f i] {ω | τ ω ≤ i} :=
  hτ i

theorem IsStoppingTime.measurableSet_lt_of_pred [PredOrder ι] (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[f i] {ω | τ ω < i} := by
  by_cases hi_min : IsMin i
  · suffices {ω : Ω | τ ω < i} = ∅ by rw [this]; exact @MeasurableSet.empty _ (f i)
    ext1 ω
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rw [isMin_iff_forall_not_lt] at hi_min
    cases τ ω with
    | top => simp
    | coe t => exact mod_cast hi_min t
  have : {ω : Ω | τ ω < i} = τ ⁻¹' Set.Iic (pred i : ι) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iic]
    cases τ ω with
    | top => simp
    | coe t =>
      simp only [WithTop.coe_lt_coe, WithTop.coe_le_coe]
      rw [le_pred_iff_of_not_isMin hi_min]
  rw [this]
  exact f.mono (pred_le i) _ (hτ.measurableSet_le <| pred i)

end Preorder

section CountableStoppingTime

namespace IsStoppingTime

variable [PartialOrder ι] {τ : Ω → WithTop ι} {f : Filtration ι m}

protected theorem measurableSet_eq_of_countable_range (hτ : IsStoppingTime f τ)
    (h_countable : (Set.range τ).Countable) (i : ι) : MeasurableSet[f i] {ω | τ ω = i} := by
  have : {ω | τ ω = i} = {ω | τ ω ≤ i} \ ⋃ (j ∈ Set.range τ) (_ : j < i), {ω | τ ω ≤ j} := by
    ext1 a
    simp only [Set.mem_setOf_eq, Set.mem_range, Set.iUnion_exists, Set.iUnion_iUnion_eq',
      Set.mem_diff, Set.mem_iUnion, exists_prop, not_exists, not_and]
    constructor <;> intro h
    · simp only [h, lt_iff_le_not_ge, le_refl, and_imp, imp_self, imp_true_iff, and_self_iff]
    · exact h.1.eq_or_lt.resolve_right fun h_lt => h.2 a h_lt le_rfl
  rw [this]
  refine (hτ.measurableSet_le i).diff ?_
  refine MeasurableSet.biUnion h_countable fun j _ => ?_
  classical
  rw [Set.iUnion_eq_if]
  split_ifs with hji
  · lift j to ι using (ne_top_of_lt hji)
    exact f.mono (mod_cast hji.le) _ (hτ.measurableSet_le j)
  · exact @MeasurableSet.empty _ (f i)

protected theorem measurableSet_eq_of_countable [Countable ι] (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[f i] {ω | τ ω = i} :=
  hτ.measurableSet_eq_of_countable_range (Set.to_countable _) i

protected theorem measurableSet_lt_of_countable_range (hτ : IsStoppingTime f τ)
    (h_countable : (Set.range τ).Countable) (i : ι) : MeasurableSet[f i] {ω | τ ω < i} := by
  have : {ω | τ ω < i} = {ω | τ ω ≤ i} \ {ω | τ ω = i} := by ext1 ω; simp [lt_iff_le_and_ne]
  rw [this]
  exact (hτ.measurableSet_le i).diff (hτ.measurableSet_eq_of_countable_range h_countable i)

protected theorem measurableSet_lt_of_countable [Countable ι] (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[f i] {ω | τ ω < i} :=
  hτ.measurableSet_lt_of_countable_range (Set.to_countable _) i

protected theorem measurableSet_ge_of_countable_range {ι} [LinearOrder ι] {τ : Ω → WithTop ι}
    {f : Filtration ι m} (hτ : IsStoppingTime f τ) (h_countable : (Set.range τ).Countable) (i : ι) :
    MeasurableSet[f i] {ω | i ≤ τ ω} := by
  have : {ω | i ≤ τ ω} = {ω | τ ω < i}ᶜ := by
    ext1 ω; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_lt]
  rw [this]
  exact (hτ.measurableSet_lt_of_countable_range h_countable i).compl

protected theorem measurableSet_ge_of_countable {ι} [LinearOrder ι] {τ : Ω → WithTop ι}
    {f : Filtration ι m} [Countable ι] (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[f i] {ω | i ≤ τ ω} :=
  hτ.measurableSet_ge_of_countable_range (Set.to_countable _) i

end IsStoppingTime

end CountableStoppingTime

section LinearOrder

variable [LinearOrder ι] {f : Filtration ι m} {τ : Ω → WithTop ι}

theorem IsStoppingTime.measurableSet_gt (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[f i] {ω | i < τ ω} := by
  have : {ω | i < τ ω} = {ω | τ ω ≤ i}ᶜ := by
    ext1 ω; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
  rw [this]
  exact (hτ.measurableSet_le i).compl

section TopologicalSpace

variable [TopologicalSpace ι] [OrderTopology ι] [FirstCountableTopology ι]

/-- Auxiliary lemma for `MeasureTheory.IsStoppingTime.measurableSet_lt`. -/
theorem IsStoppingTime.measurableSet_lt_of_isLUB (hτ : IsStoppingTime f τ) (i : ι)
    (h_lub : IsLUB (Set.Iio i) i) : MeasurableSet[f i] {ω | τ ω < i} := by
  by_cases hi_min : IsMin i
  · suffices {ω | τ ω < i} = ∅ by rw [this]; exact @MeasurableSet.empty _ (f i)
    ext1 ω
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    cases τ ω with
    | top => simp
    | coe t => norm_cast; exact isMin_iff_forall_not_lt.mp hi_min t
  obtain ⟨seq, -, -, h_tendsto, h_bound⟩ :
      ∃ seq : ℕ → ι, Monotone seq ∧ (∀ j, seq j ≤ i) ∧ Tendsto seq atTop (𝓝 i) ∧ ∀ j, seq j < i :=
    h_lub.exists_seq_monotone_tendsto (not_isMin_iff.mp hi_min)
  have h_Iio_eq_Union : Set.Iio (i : WithTop ι) = ⋃ j, {k : WithTop ι | k ≤ seq j} := by
    ext1 k
    simp only [Set.mem_Iio, Set.mem_iUnion, Set.mem_setOf_eq]
    refine ⟨fun hk_lt_i => ?_, fun h_exists_k_le_seq => ?_⟩
    · rw [tendsto_atTop'] at h_tendsto
      cases k with
      | top => simp at hk_lt_i
      | coe k =>
        norm_cast at hk_lt_i ⊢
        have h_nhds : Set.Ici k ∈ 𝓝 i :=
          mem_nhds_iff.mpr ⟨Set.Ioi k, Set.Ioi_subset_Ici le_rfl, isOpen_Ioi, hk_lt_i⟩
        obtain ⟨a, ha⟩ : ∃ a : ℕ, ∀ b : ℕ, b ≥ a → k ≤ seq b := h_tendsto (Set.Ici k) h_nhds
        exact ⟨a, ha a le_rfl⟩
    · obtain ⟨j, hk_seq_j⟩ := h_exists_k_le_seq
      exact hk_seq_j.trans_lt (mod_cast h_bound j)
  have h_lt_eq_preimage : {ω | τ ω < i} = τ ⁻¹' Set.Iio i := by
    ext1 ω; simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iio]
  rw [h_lt_eq_preimage, h_Iio_eq_Union]
  simp only [Set.preimage_iUnion, Set.preimage_setOf_eq]
  exact MeasurableSet.iUnion fun n => f.mono (h_bound n).le _ (hτ.measurableSet_le (seq n))

theorem IsStoppingTime.measurableSet_lt (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[f i] {ω | τ ω < i} := by
  obtain ⟨i', hi'_lub⟩ : ∃ i', IsLUB (Set.Iio i) i' := exists_lub_Iio i
  rcases lub_Iio_eq_self_or_Iio_eq_Iic i hi'_lub with hi'_eq_i | h_Iio_eq_Iic
  · rw [← hi'_eq_i] at hi'_lub ⊢
    exact hτ.measurableSet_lt_of_isLUB i' hi'_lub
  · have h_lt_eq_preimage : {ω : Ω | τ ω < i} = τ ⁻¹' Set.Iio i := rfl
    have h_Iio_eq_Iic' : Set.Iio (i : WithTop ι) = Set.Iic (i' : WithTop ι) := by
      rw [← WithTop.image_coe_Iio, ← WithTop.image_coe_Iic, h_Iio_eq_Iic]
    rw [h_lt_eq_preimage, h_Iio_eq_Iic']
    exact f.mono (lub_Iio_le i hi'_lub) _ (hτ.measurableSet_le i')

theorem IsStoppingTime.measurableSet_ge (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[f i] {ω | i ≤ τ ω} := by
  have : {ω | i ≤ τ ω} = {ω | τ ω < i}ᶜ := by
    ext1 ω; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_lt]
  rw [this]
  exact (hτ.measurableSet_lt i).compl

theorem IsStoppingTime.measurableSet_eq (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[f i] {ω | τ ω = i} := by
  have : {ω | τ ω = i} = {ω | τ ω ≤ i} ∩ {ω | τ ω ≥ i} := by
    ext1 ω; simp only [Set.mem_setOf_eq, Set.mem_inter_iff, le_antisymm_iff]
  rw [this]
  exact (hτ.measurableSet_le i).inter (hτ.measurableSet_ge i)

theorem IsStoppingTime.measurableSet_eq_le (hτ : IsStoppingTime f τ) {i j : ι} (hle : i ≤ j) :
    MeasurableSet[f j] {ω | τ ω = i} :=
  f.mono hle _ <| hτ.measurableSet_eq i

theorem IsStoppingTime.measurableSet_lt_le (hτ : IsStoppingTime f τ) {i j : ι} (hle : i ≤ j) :
    MeasurableSet[f j] {ω | τ ω < i} :=
  f.mono hle _ <| hτ.measurableSet_lt i

end TopologicalSpace

end LinearOrder

section Countable

theorem isStoppingTime_of_measurableSet_eq [Preorder ι] [Countable ι] {f : Filtration ι m}
    {τ : Ω → WithTop ι} (hτ : ∀ i, MeasurableSet[f i] {ω | τ ω = i}) : IsStoppingTime f τ := by
  intro i
  have h_eq_iUnion : {ω | τ ω ≤ i} = ⋃ k ≤ i, {ω | τ ω = k} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    cases τ ω with
    | top => simp
    | coe a => norm_cast; simp
  rw [h_eq_iUnion]
  refine MeasurableSet.biUnion (Set.to_countable _) fun k hk => ?_
  exact f.mono hk _ (hτ k)

end Countable

end MeasurableSet

namespace IsStoppingTime

protected theorem max [LinearOrder ι] {f : Filtration ι m} {τ π : Ω → WithTop ι}
    (hτ : IsStoppingTime f τ)
    (hπ : IsStoppingTime f π) : IsStoppingTime f fun ω => max (τ ω) (π ω) := by
  intro i
  simp_rw [max_le_iff, Set.setOf_and]
  exact (hτ i).inter (hπ i)

protected theorem max_const [LinearOrder ι] {f : Filtration ι m} {τ : Ω → WithTop ι}
    (hτ : IsStoppingTime f τ) (i : ι) : IsStoppingTime f fun ω => max (τ ω) i :=
  hτ.max (isStoppingTime_const f i)

protected theorem min [LinearOrder ι] {f : Filtration ι m} {τ π : Ω → WithTop ι}
    (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) :
    IsStoppingTime f fun ω => min (τ ω) (π ω) := by
  intro i
  simp_rw [min_le_iff, Set.setOf_or]
  exact (hτ i).union (hπ i)

protected theorem min_const [LinearOrder ι] {f : Filtration ι m} {τ : Ω → WithTop ι}
    (hτ : IsStoppingTime f τ) (i : ι) : IsStoppingTime f fun ω => min (τ ω) i :=
  hτ.min (isStoppingTime_const f i)

theorem add_const [AddGroup ι] [Preorder ι] [AddRightMono ι]
    [AddLeftMono ι] {f : Filtration ι m} {τ : Ω → WithTop ι} (hτ : IsStoppingTime f τ)
    {i : ι} (hi : 0 ≤ i) : IsStoppingTime f fun ω => τ ω + i := by
  intro j
  simp only
  have h_eq : {ω | τ ω + i ≤ j} = {ω | τ ω ≤ j - i} := by
    ext ω
    simp only [Set.mem_setOf_eq, WithTop.coe_sub]
    cases τ ω with
    | top => simp
    | coe a => norm_cast; simp_rw [← le_sub_iff_add_le]
  rw [h_eq]
  exact f.mono (sub_le_self j hi) _ (hτ (j - i))

theorem add_const_nat {f : Filtration ℕ m} {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime f τ) {i : ℕ} :
    IsStoppingTime f fun ω => τ ω + i := by
  refine isStoppingTime_of_measurableSet_eq fun j => ?_
  by_cases hij : i ≤ j
  · simp only [ENat.some_eq_coe]
    have h_eq : {ω | τ ω + i = j} = {ω | τ ω = (j - i : ℕ)} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      cases τ ω with
      | top => simp
      | coe a =>
        simp only [ENat.some_eq_coe, Nat.cast_inj]
        norm_cast
        simp_rw [eq_comm, ← Nat.sub_eq_iff_eq_add hij, eq_comm]
    rw [h_eq]
    exact f.mono (j.sub_le i) _ (hτ.measurableSet_eq (j - i))
  · rw [not_le] at hij
    convert @MeasurableSet.empty _ (f.1 j)
    ext ω
    simp only [Set.mem_empty_iff_false, iff_false, Set.mem_setOf]
    cases τ ω with
    | top => simp
    | coe a => simp only [ENat.some_eq_coe]; norm_cast; cutsat

-- generalize to certain countable type?
theorem add {f : Filtration ℕ m} {τ π : Ω → WithTop ℕ}
    (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) :
    IsStoppingTime f (τ + π) := by
  intro i
  simp only [ENat.some_eq_coe]
  have h : {ω | (τ + π) ω ≤ i} = ⋃ k ≤ i, {ω | π ω = k} ∩ {ω | τ ω + k ≤ i} := by
    ext ω
    simp only [Pi.add_apply, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, exists_and_left,
      exists_prop]
    cases τ ω with
    | top => simp
    | coe a =>
      cases π ω with
      | top => simp
      | coe b =>
        simp only [ENat.some_eq_coe, Nat.cast_inj, exists_eq_left', iff_and_self]
        norm_cast
        omega
  rw [h]
  exact MeasurableSet.iUnion fun k =>
    MeasurableSet.iUnion fun hk => (hπ.measurableSet_eq_le hk).inter (hτ.add_const_nat i)

section Preorder

variable [Preorder ι] {f : Filtration ι m} {τ π : Ω → WithTop ι}

/-- The associated σ-algebra with a stopping time. -/
protected def measurableSpace (hτ : IsStoppingTime f τ) : MeasurableSpace Ω where
  MeasurableSet' s := MeasurableSet s ∧ ∀ i : ι, MeasurableSet[f i] (s ∩ {ω | τ ω ≤ i})
  measurableSet_empty := by simp
  measurableSet_compl s hs := by
    refine ⟨hs.1.compl, fun i ↦ ?_⟩
    rw [(_ : sᶜ ∩ {ω | τ ω ≤ i} = (sᶜ ∪ {ω | τ ω ≤ i}ᶜ) ∩ {ω | τ ω ≤ i})]
    · refine MeasurableSet.inter ?_ ?_
      · rw [← Set.compl_inter]
        exact (hs.2 i).compl
      · exact hτ i
    · rw [Set.union_inter_distrib_right]
      simp only [Set.compl_inter_self, Set.union_empty]
  measurableSet_iUnion s hs := by
    refine ⟨MeasurableSet.iUnion fun i ↦ (hs i).1, fun i ↦ ?_⟩
    replace hs := fun i ↦ (hs i).2
    rw [forall_swap] at hs
    rw [Set.iUnion_inter]
    exact MeasurableSet.iUnion (hs i)

protected theorem measurableSet (hτ : IsStoppingTime f τ) (s : Set Ω) :
    MeasurableSet[hτ.measurableSpace] s
      ↔ MeasurableSet s ∧ ∀ i : ι, MeasurableSet[f i] (s ∩ {ω | τ ω ≤ i}) :=
  Iff.rfl

theorem measurableSpace_mono (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) (hle : τ ≤ π) :
    hτ.measurableSpace ≤ hπ.measurableSpace := by
  refine fun s hs ↦ ⟨hs.1, fun i ↦ ?_⟩
  rw [(_ : s ∩ {ω | π ω ≤ i} = s ∩ {ω | τ ω ≤ i} ∩ {ω | π ω ≤ i})]
  · exact (hs.2 i).inter (hπ i)
  · ext
    simp only [Set.mem_inter_iff, iff_self_and, and_congr_left_iff, Set.mem_setOf_eq]
    intro hle' _
    exact le_trans (hle _) hle'

theorem measurableSpace_le (hτ : IsStoppingTime f τ) : hτ.measurableSpace ≤ m := fun _ hs ↦ hs.1

@[deprecated (since := "2025-09-08")] alias measurableSpace_le_of_countable := measurableSpace_le
@[deprecated (since := "2025-09-08")] alias measurableSpace_le_of_countable_range :=
    measurableSpace_le

@[simp]
theorem measurableSpace_const (f : Filtration ι m) (i : ι) :
    (isStoppingTime_const f i).measurableSpace = f i := by
  ext1 s
  change MeasurableSet[(isStoppingTime_const f i).measurableSpace] s ↔ MeasurableSet[f i] s
  rw [IsStoppingTime.measurableSet]
  constructor <;> intro h
  · have h' := h.2 i
    simpa only [le_refl, Set.setOf_true, Set.inter_univ] using h'
  · refine ⟨f.le i _ h, fun j ↦ ?_⟩
    by_cases hij : i ≤ j
    · norm_cast
      simp only [hij, Set.setOf_true, Set.inter_univ]
      exact f.mono hij _ h
    · norm_cast
      simp only [hij, Set.setOf_false, Set.inter_empty, @MeasurableSet.empty _ (f.1 j)]

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
  · simpa [Set.inter_assoc, this] using h.2 i
  · refine ⟨f.le i _ h, fun j ↦ ?_⟩
    rw [Set.inter_assoc, this]
    by_cases hij : i ≤ j
    · norm_cast
      simp only [hij, Set.setOf_true, Set.inter_univ]
      exact f.mono hij _ h
    · simp [hij]

theorem measurableSpace_le_of_le_const (hτ : IsStoppingTime f τ) {i : ι} (hτ_le : ∀ ω, τ ω ≤ i) :
    hτ.measurableSpace ≤ f i :=
  (measurableSpace_mono hτ _ hτ_le).trans (measurableSpace_const _ _).le

theorem measurableSpace_le_of_le (hτ : IsStoppingTime f τ) {n : ι} (hτ_le : ∀ ω, τ ω ≤ n) :
    hτ.measurableSpace ≤ m :=
  (hτ.measurableSpace_le_of_le_const hτ_le).trans (f.le n)

theorem le_measurableSpace_of_const_le (hτ : IsStoppingTime f τ) {i : ι} (hτ_le : ∀ ω, i ≤ τ ω) :
    f i ≤ hτ.measurableSpace :=
  (measurableSpace_const _ _).symm.le.trans (measurableSpace_mono _ hτ hτ_le)

end Preorder

instance sigmaFinite_stopping_time {ι} [SemilatticeSup ι] [OrderBot ι]
    {μ : Measure Ω} {f : Filtration ι m}
    {τ : Ω → WithTop ι} [SigmaFiniteFiltration μ f] (hτ : IsStoppingTime f τ) :
    SigmaFinite (μ.trim hτ.measurableSpace_le) := by
  refine @sigmaFiniteTrim_mono _ _ ?_ _ _ _ ?_ ?_
  · exact f ⊥
  · exact hτ.le_measurableSpace_of_const_le fun _ => bot_le
  · infer_instance

instance sigmaFinite_stopping_time_of_le {ι} [SemilatticeSup ι] [OrderBot ι] {μ : Measure Ω}
    {f : Filtration ι m} {τ : Ω → WithTop ι} [SigmaFiniteFiltration μ f]
    (hτ : IsStoppingTime f τ) {n : ι}
    (hτ_le : ∀ ω, τ ω ≤ n) : SigmaFinite (μ.trim (hτ.measurableSpace_le_of_le hτ_le)) := by
  refine @sigmaFiniteTrim_mono _ _ ?_ _ _ _ ?_ ?_
  · exact f ⊥
  · exact hτ.le_measurableSpace_of_const_le fun _ => bot_le
  · infer_instance

section LinearOrder

variable [LinearOrder ι] {f : Filtration ι m} {τ π : Ω → WithTop ι}

protected theorem measurableSet_le' (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[hτ.measurableSpace] {ω | τ ω ≤ i} := by
  refine ⟨f.le i _ (hτ i), fun j ↦ ?_⟩
  have : {ω : Ω | τ ω ≤ i} ∩ {ω : Ω | τ ω ≤ j} = {ω : Ω | τ ω ≤ min i j} := by
    ext1 ω
    simp [Set.mem_inter_iff, Set.mem_setOf_eq]
  rw [this]
  exact f.mono (min_le_right i j) _ (hτ _)

protected theorem measurableSet_gt' (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[hτ.measurableSpace] {ω | i < τ ω} := by
  have : {ω : Ω | i < τ ω} = {ω : Ω | τ ω ≤ i}ᶜ := by ext1 ω; simp
  rw [this]
  exact (hτ.measurableSet_le' i).compl

protected theorem measurableSet_eq' [TopologicalSpace ι] [OrderTopology ι]
    [FirstCountableTopology ι] (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[hτ.measurableSpace] {ω | τ ω = i} := by
  rw [← Set.univ_inter {ω | τ ω = i}, measurableSet_inter_eq_iff, Set.univ_inter]
  exact hτ.measurableSet_eq i

protected theorem measurableSet_ge' [TopologicalSpace ι] [OrderTopology ι]
    [FirstCountableTopology ι] (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[hτ.measurableSpace] {ω | i ≤ τ ω} := by
  have : {ω | i ≤ τ ω} = {ω | τ ω = i} ∪ {ω | i < τ ω} := by
    ext1 ω
    simp only [le_iff_lt_or_eq, Set.mem_setOf_eq, Set.mem_union]
    cases τ ω with
    | top => simp
    | coe a =>
      norm_cast
      rw [@eq_comm _ i, or_comm]
  rw [this]
  exact (hτ.measurableSet_eq' i).union (hτ.measurableSet_gt' i)

protected theorem measurableSet_lt' [TopologicalSpace ι] [OrderTopology ι]
    [FirstCountableTopology ι] (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[hτ.measurableSpace] {ω | τ ω < i} := by
  have : {ω | τ ω < i} = {ω | τ ω ≤ i} \ {ω | τ ω = i} := by
    ext1 ω
    simp only [lt_iff_le_and_ne, Set.mem_setOf_eq, Set.mem_diff]
  rw [this]
  exact (hτ.measurableSet_le' i).diff (hτ.measurableSet_eq' i)

section Countable

protected theorem measurableSet_eq_of_countable_range' (hτ : IsStoppingTime f τ)
    (h_countable : (Set.range τ).Countable) (i : ι) :
    MeasurableSet[hτ.measurableSpace] {ω | τ ω = i} := by
  rw [← Set.univ_inter {ω | τ ω = i}, measurableSet_inter_eq_iff, Set.univ_inter]
  exact hτ.measurableSet_eq_of_countable_range h_countable i

protected theorem measurableSet_eq_of_countable' [Countable ι] (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[hτ.measurableSpace] {ω | τ ω = i} :=
  hτ.measurableSet_eq_of_countable_range' (Set.to_countable _) i

protected theorem measurableSet_ge_of_countable_range' (hτ : IsStoppingTime f τ)
    (h_countable : (Set.range τ).Countable) (i : ι) :
    MeasurableSet[hτ.measurableSpace] {ω | i ≤ τ ω} := by
  have : {ω | i ≤ τ ω} = {ω | τ ω = i} ∪ {ω | i < τ ω} := by
    ext1 ω
    simp only [le_iff_lt_or_eq, Set.mem_setOf_eq, Set.mem_union]
    cases τ ω with
    | top => simp
    | coe a =>
      norm_cast
      rw [@eq_comm _ i, or_comm]
  rw [this]
  exact (hτ.measurableSet_eq_of_countable_range' h_countable i).union (hτ.measurableSet_gt' i)

protected theorem measurableSet_ge_of_countable' [Countable ι] (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[hτ.measurableSpace] {ω | i ≤ τ ω} :=
  hτ.measurableSet_ge_of_countable_range' (Set.to_countable _) i

protected theorem measurableSet_lt_of_countable_range' (hτ : IsStoppingTime f τ)
    (h_countable : (Set.range τ).Countable) (i : ι) :
    MeasurableSet[hτ.measurableSpace] {ω | τ ω < i} := by
  have : {ω | τ ω < i} = {ω | τ ω ≤ i} \ {ω | τ ω = i} := by
    ext1 ω
    simp only [lt_iff_le_and_ne, Set.mem_setOf_eq, Set.mem_diff]
  rw [this]
  exact (hτ.measurableSet_le' i).diff (hτ.measurableSet_eq_of_countable_range' h_countable i)

protected theorem measurableSet_lt_of_countable' [Countable ι] (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[hτ.measurableSpace] {ω | τ ω < i} :=
  hτ.measurableSet_lt_of_countable_range' (Set.to_countable _) i

end Countable

protected theorem measurable [TopologicalSpace ι]
    [OrderTopology ι] [SecondCountableTopology ι] (hτ : IsStoppingTime f τ) :
    Measurable[hτ.measurableSpace] τ := by
  refine measurable_of_Iic fun i ↦ ?_
  cases i with
  | top => simp
  | coe i => exact hτ.measurableSet_le' i

protected theorem measurable' [TopologicalSpace ι]
    [OrderTopology ι] [SecondCountableTopology ι] (hτ : IsStoppingTime f τ) :
    Measurable τ := hτ.measurable.mono (measurableSpace_le hτ) le_rfl

protected lemma measurableSet_eq_top [TopologicalSpace ι]
    [OrderTopology ι] [SecondCountableTopology ι] (hτ : IsStoppingTime f τ) :
    MeasurableSet {ω | τ ω = ⊤} :=
  (measurableSet_singleton _).preimage hτ.measurable'

protected theorem measurable_of_le [TopologicalSpace ι]
    [OrderTopology ι] [SecondCountableTopology ι] (hτ : IsStoppingTime f τ) {i : ι}
    (hτ_le : ∀ ω, τ ω ≤ i) : Measurable[f i] τ :=
  hτ.measurable.mono (measurableSpace_le_of_le_const _ hτ_le) le_rfl

theorem measurableSpace_min (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) :
    (hτ.min hπ).measurableSpace = hτ.measurableSpace ⊓ hπ.measurableSpace := by
  refine le_antisymm ?_ ?_
  · exact le_inf (measurableSpace_mono _ hτ fun _ => min_le_left _ _)
      (measurableSpace_mono _ hπ fun _ => min_le_right _ _)
  · intro s
    change MeasurableSet[hτ.measurableSpace] s ∧ MeasurableSet[hπ.measurableSpace] s →
      MeasurableSet[(hτ.min hπ).measurableSpace] s
    simp_rw [IsStoppingTime.measurableSet]
    have : ∀ i, {ω | min (τ ω) (π ω) ≤ i} = {ω | τ ω ≤ i} ∪ {ω | π ω ≤ i} := by
      intro i; ext1 ω; simp
    simp_rw [this, Set.inter_union_distrib_left]
    exact fun h ↦ ⟨h.1.1, fun i ↦ (h.left.2 i).union (h.right.2 i)⟩

theorem measurableSet_min_iff (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) (s : Set Ω) :
    MeasurableSet[(hτ.min hπ).measurableSpace] s ↔
      MeasurableSet[hτ.measurableSpace] s ∧ MeasurableSet[hπ.measurableSpace] s := by
  rw [measurableSpace_min hτ hπ]; rfl

theorem measurableSpace_min_const (hτ : IsStoppingTime f τ) {i : ι} :
    (hτ.min_const i).measurableSpace = hτ.measurableSpace ⊓ f i := by
  rw [hτ.measurableSpace_min (isStoppingTime_const _ i), measurableSpace_const]

theorem measurableSet_min_const_iff (hτ : IsStoppingTime f τ) (s : Set Ω) {i : ι} :
    MeasurableSet[(hτ.min_const i).measurableSpace] s ↔
      MeasurableSet[hτ.measurableSpace] s ∧ MeasurableSet[f i] s := by
  rw [measurableSpace_min_const hτ]; apply MeasurableSpace.measurableSet_inf

theorem measurableSet_inter_le [TopologicalSpace ι] [SecondCountableTopology ι] [OrderTopology ι]
    (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π)
    (s : Set Ω) (hs : MeasurableSet[hτ.measurableSpace] s) :
    MeasurableSet[(hτ.min hπ).measurableSpace] (s ∩ {ω | τ ω ≤ π ω}) := by
  simp_rw [IsStoppingTime.measurableSet] at hs ⊢
  have h_eq i : s ∩ {ω | τ ω ≤ π ω} ∩ {ω | min (τ ω) (π ω) ≤ i} =
      s ∩ {ω | τ ω ≤ i} ∩ {ω | min (τ ω) (π ω) ≤ i} ∩
        {ω | min (τ ω) i ≤ min (min (τ ω) (π ω)) i} := by
    ext1 ω
    simp only [min_le_iff, Set.mem_inter_iff, Set.mem_setOf_eq, le_min_iff, le_refl, true_and,
      true_or]
    by_cases hτi : τ ω ≤ i
    · simp only [hτi, true_or, and_true, and_congr_right_iff]
      intro
      constructor <;> intro h
      · exact Or.inl h
      · rcases h with h | h
        · exact h
        · exact hτi.trans h
    simp only [hτi, false_or, and_false, false_and, iff_false, not_and, not_le, and_imp]
    refine fun _ hτ_le_π => lt_of_lt_of_le ?_ hτ_le_π
    rw [← not_le]
    exact hτi
  simp_rw [h_eq]
  refine ⟨hs.1.inter (measurableSet_le hτ.measurable' hπ.measurable'), fun i ↦ ?_⟩
  refine ((hs.2 i).inter ((hτ.min hπ) i)).inter ?_
  apply @measurableSet_le _ _ _ _ _ (Filtration.seq f i) _ _ _ _ _ ?_ ?_
  · exact (hτ.min_const i).measurable_of_le fun _ => min_le_right _ _
  · exact ((hτ.min hπ).min_const i).measurable_of_le fun _ => min_le_right _ _

theorem measurableSet_inter_le_iff [TopologicalSpace ι] [SecondCountableTopology ι]
    [OrderTopology ι] (hτ : IsStoppingTime f τ)
    (hπ : IsStoppingTime f π) (s : Set Ω) :
    MeasurableSet[hτ.measurableSpace] (s ∩ {ω | τ ω ≤ π ω}) ↔
      MeasurableSet[(hτ.min hπ).measurableSpace] (s ∩ {ω | τ ω ≤ π ω}) := by
  constructor <;> intro h
  · have : s ∩ {ω | τ ω ≤ π ω} = s ∩ {ω | τ ω ≤ π ω} ∩ {ω | τ ω ≤ π ω} := by
      rw [Set.inter_assoc, Set.inter_self]
    rw [this]
    exact measurableSet_inter_le _ hπ _ h
  · rw [measurableSet_min_iff hτ hπ] at h
    exact h.1

theorem measurableSet_inter_le_const_iff (hτ : IsStoppingTime f τ) (s : Set Ω) (i : ι) :
    MeasurableSet[hτ.measurableSpace] (s ∩ {ω | τ ω ≤ i}) ↔
      MeasurableSet[(hτ.min_const i).measurableSpace] (s ∩ {ω | τ ω ≤ i}) := by
  rw [IsStoppingTime.measurableSet_min_iff hτ (isStoppingTime_const _ i),
    IsStoppingTime.measurableSpace_const, IsStoppingTime.measurableSet]
  refine ⟨fun h => ⟨h, ?_⟩, fun h ↦ h.1⟩
  have h' := h.2 i
  rwa [Set.inter_assoc, Set.inter_self] at h'

theorem measurableSet_le_stopping_time [TopologicalSpace ι] [SecondCountableTopology ι]
    [OrderTopology ι] (hτ : IsStoppingTime f τ)
    (hπ : IsStoppingTime f π) : MeasurableSet[hτ.measurableSpace] {ω | τ ω ≤ π ω} := by
  rw [hτ.measurableSet]
  refine ⟨measurableSet_le hτ.measurable' hπ.measurable', fun j ↦ ?_⟩
  have : {ω | τ ω ≤ π ω} ∩ {ω | τ ω ≤ j} = {ω | min (τ ω) j ≤ min (π ω) j} ∩ {ω | τ ω ≤ j} := by
    ext1 ω
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, min_le_iff, le_min_iff, le_refl,
      and_congr_left_iff]
    intro h
    simp only [h, or_self_iff, and_true]
    rw [Iff.comm, or_iff_left_iff_imp]
    exact h.trans
  rw [this]
  refine MeasurableSet.inter ?_ (hτ.measurableSet_le j)
  apply @measurableSet_le _ _ _ _ _ (Filtration.seq f j) _ _ _ _ _ ?_ ?_
  · exact (hτ.min_const j).measurable_of_le fun _ => min_le_right _ _
  · exact (hπ.min_const j).measurable_of_le fun _ => min_le_right _ _

theorem measurableSet_stopping_time_le_min [TopologicalSpace ι] [SecondCountableTopology ι]
    [OrderTopology ι] (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) :
    MeasurableSet[(hτ.min hπ).measurableSpace] {ω | τ ω ≤ π ω} := by
  rw [← Set.univ_inter {ω : Ω | τ ω ≤ π ω}, ← hτ.measurableSet_inter_le_iff hπ, Set.univ_inter]
  exact measurableSet_le_stopping_time hτ hπ

theorem measurableSet_stopping_time_le [TopologicalSpace ι] [SecondCountableTopology ι]
    [OrderTopology ι] (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) :
    MeasurableSet[hπ.measurableSpace] {ω | τ ω ≤ π ω} := by
  have : MeasurableSet[(hτ.min hπ).measurableSpace] {ω | τ ω ≤ π ω} :=
    measurableSet_stopping_time_le_min hτ hπ
  rw [measurableSet_min_iff hτ hπ] at this; exact (this).2

theorem measurableSet_eq_stopping_time_min [TopologicalSpace ι]
    [OrderTopology ι] [SecondCountableTopology ι]
    (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) :
    MeasurableSet[(hτ.min hπ).measurableSpace] {ω | τ ω = π ω} := by
  have : {ω | τ ω = π ω} = {ω | τ ω ≤ π ω} ∩ {ω | π ω ≤ τ ω} := by
    ext; simp only [Set.mem_setOf_eq, le_antisymm_iff, Set.mem_inter_iff]
  rw [this]
  refine MeasurableSet.inter (measurableSet_stopping_time_le_min hτ hπ) ?_
  convert (measurableSet_stopping_time_le_min hπ hτ) using 3
  rw [min_comm]

theorem measurableSet_eq_stopping_time [TopologicalSpace ι] [OrderTopology ι]
    [SecondCountableTopology ι]
    (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) :
    MeasurableSet[hτ.measurableSpace] {ω | τ ω = π ω} := by
  have h := measurableSet_eq_stopping_time_min hτ hπ
  rw [measurableSet_min_iff hτ hπ] at h
  exact h.1

@[deprecated (since := "2025-09-08")] alias measurableSet_eq_stopping_time_of_countable :=
  measurableSet_eq_stopping_time

end LinearOrder

end IsStoppingTime

section LinearOrder

/-! ## Stopped value and stopped process -/

variable [Nonempty ι]

/-- Given a map `u : ι → Ω → E`, its stopped value with respect to the stopping
time `τ` is the map `x ↦ u (τ ω) ω`. -/
noncomputable
def stoppedValue (u : ι → Ω → β) (τ : Ω → WithTop ι) : Ω → β := fun ω => u (τ ω).untopA ω

theorem stoppedValue_const (u : ι → Ω → β) (i : ι) : (stoppedValue u fun _ => i) = u i :=
  rfl

variable [LinearOrder ι]

/-- Given a map `u : ι → Ω → E`, the stopped process with respect to `τ` is `u i ω` if
`i ≤ τ ω`, and `u (τ ω) ω` otherwise.

Intuitively, the stopped process stops evolving once the stopping time has occurred. -/
noncomputable
def stoppedProcess (u : ι → Ω → β) (τ : Ω → WithTop ι) : ι → Ω → β :=
  fun i ω => u (min (i : WithTop ι) (τ ω)).untopA ω

theorem stoppedProcess_eq_stoppedValue {u : ι → Ω → β} {τ : Ω → WithTop ι} :
    stoppedProcess u τ = fun i : ι => stoppedValue u fun ω => min i (τ ω) := rfl

theorem stoppedValue_stoppedProcess {u : ι → Ω → β} {τ σ : Ω → WithTop ι} :
    stoppedValue (stoppedProcess u τ) σ =
      fun ω ↦ if σ ω ≠ ⊤ then stoppedValue u (fun ω ↦ min (σ ω) (τ ω)) ω
      else stoppedValue u (fun ω ↦ min (Classical.arbitrary ι) (τ ω)) ω := by
  ext ω
  simp only [stoppedValue, stoppedProcess, ne_eq, ite_not]
  cases σ ω <;> cases τ ω <;> simp

theorem stoppedValue_stoppedProcess_ae_eq {u : ι → Ω → β} {τ σ : Ω → WithTop ι} {μ : Measure Ω}
    (hσ : ∀ᵐ ω ∂μ, σ ω ≠ ⊤) :
    stoppedValue (stoppedProcess u τ) σ =ᵐ[μ] stoppedValue u (fun ω ↦ min (σ ω) (τ ω)) := by
  filter_upwards [hσ] with ω hσ using by simp [stoppedValue_stoppedProcess, hσ]

theorem stoppedProcess_eq_of_le {u : ι → Ω → β} {τ : Ω → WithTop ι} {i : ι} {ω : Ω} (h : i ≤ τ ω) :
    stoppedProcess u τ i ω = u i ω := by simp [stoppedProcess, min_eq_left h]

theorem stoppedProcess_eq_of_ge {u : ι → Ω → β} {τ : Ω → WithTop ι} {i : ι} {ω : Ω} (h : τ ω ≤ i) :
    stoppedProcess u τ i ω = u (τ ω).untopA ω := by simp [stoppedProcess, min_eq_right h]

section ProgMeasurable

variable [MeasurableSpace ι] [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι]
  [BorelSpace ι] [TopologicalSpace β] {u : ι → Ω → β} {τ : Ω → WithTop ι} {f : Filtration ι m}

theorem progMeasurable_min_stopping_time [PseudoMetrizableSpace ι] (hτ : IsStoppingTime f τ) :
    ProgMeasurable f fun i ω ↦ (min (i : WithTop ι) (τ ω)).untopA := by
  refine fun i ↦ (Measurable.untopA ?_).stronglyMeasurable
  let m_prod : MeasurableSpace (Set.Iic i × Ω) := Subtype.instMeasurableSpace.prod (f i)
  let m_set : ∀ t : Set (Set.Iic i × Ω), MeasurableSpace t := fun _ =>
    @Subtype.instMeasurableSpace (Set.Iic i × Ω) _ m_prod
  let s := {p : Set.Iic i × Ω | τ p.2 ≤ i}
  have hs : MeasurableSet[m_prod] s := @measurable_snd (Set.Iic i) Ω _ (f i) _ (hτ i)
  have h_meas_fst : ∀ t : Set (Set.Iic i × Ω),
      Measurable[m_set t] fun x : t => ((x : Set.Iic i × Ω).fst : ι) :=
    fun t => (@measurable_subtype_coe (Set.Iic i × Ω) m_prod _).fst.subtype_val
  refine measurable_of_restrict_of_restrict_compl hs ?_ ?_
  · refine Measurable.min (h_meas_fst s).withTop_coe ?_
    refine measurable_of_Iic fun j ↦ ?_
    cases j with
    | top => simp
    | coe j =>
      have h_set_eq : (fun x : s => τ (x : Set.Iic i × Ω).snd) ⁻¹' Set.Iic j =
          (fun x : s => (x : Set.Iic i × Ω).snd) ⁻¹' {ω | τ ω ≤ min i j} := by
        ext1 ω
        simp only [Set.mem_preimage, Set.mem_Iic, WithTop.coe_min, le_inf_iff,
          Set.preimage_setOf_eq, Set.mem_setOf_eq, iff_and_self]
        exact fun _ => ω.prop
      rw [h_set_eq]
      suffices h_meas : @Measurable _ _ (m_set s) (f i) fun x : s ↦ (x : Set.Iic i × Ω).snd from
        h_meas (f.mono (min_le_left _ _) _ (hτ.measurableSet_le (min i j)))
      exact measurable_snd.comp (@measurable_subtype_coe _ m_prod _)
  · letI sc := sᶜ
    suffices h_min_eq_left :
      (fun x : sc => min (↑(x : Set.Iic i × Ω).fst) (τ (x : Set.Iic i × Ω).snd)) = fun x : sc =>
        ↑(x : Set.Iic i × Ω).fst by
      simp +unfoldPartialApp only [sc, Set.restrict, h_min_eq_left]
      exact (h_meas_fst _).withTop_coe
    ext1 ω
    rw [min_eq_left]
    have hx_fst_le : ↑(ω : Set.Iic i × Ω).fst ≤ i := (ω : Set.Iic i × Ω).fst.prop
    by_cases h : τ (ω : Set.Iic i × Ω).2 = ⊤
    · simp [h]
    · lift τ (ω : Set.Iic i × Ω).2 to ι using h with t ht
      norm_cast
      refine hx_fst_le.trans (le_of_lt ?_)
      convert ω.prop
      simp only [sc, s, not_le, Set.mem_compl_iff, Set.mem_setOf_eq, ← ht]
      norm_cast

theorem ProgMeasurable.stoppedProcess [PseudoMetrizableSpace ι] (h : ProgMeasurable f u)
    (hτ : IsStoppingTime f τ) : ProgMeasurable f (stoppedProcess u τ) := by
  have h_meas := progMeasurable_min_stopping_time hτ
  refine h.comp h_meas fun i ω ↦ ?_
  cases τ ω with
  | top => simp
  | coe t =>
    rcases le_total i t with h_it | h_ti
    · simp [(mod_cast h_it : (i : WithTop ι) ≤ t)]
    · simpa [(mod_cast h_ti : t ≤ (i : WithTop ι))]

theorem ProgMeasurable.adapted_stoppedProcess [PseudoMetrizableSpace ι] (h : ProgMeasurable f u)
    (hτ : IsStoppingTime f τ) : Adapted f (MeasureTheory.stoppedProcess u τ) :=
  (h.stoppedProcess hτ).adapted

theorem ProgMeasurable.stronglyMeasurable_stoppedProcess [PseudoMetrizableSpace ι]
    (hu : ProgMeasurable f u) (hτ : IsStoppingTime f τ) (i : ι) :
    StronglyMeasurable (MeasureTheory.stoppedProcess u τ i) :=
  (hu.adapted_stoppedProcess hτ i).mono (f.le _)

theorem stronglyMeasurable_stoppedValue_of_le (h : ProgMeasurable f u) (hτ : IsStoppingTime f τ)
    {n : ι} (hτ_le : ∀ ω, τ ω ≤ n) : StronglyMeasurable[f n] (stoppedValue u τ) := by
  have hτ_le' ω : (τ ω).untopA ≤ n := WithTop.untopA_le (hτ_le ω)
  have : stoppedValue u τ =
      (fun p : Set.Iic n × Ω => u (↑p.fst) p.snd) ∘ fun ω => (⟨(τ ω).untopA, hτ_le' ω⟩, ω) := by
    ext1 ω; simp only [stoppedValue, Function.comp_apply]
  rw [this]
  refine StronglyMeasurable.comp_measurable (h n) ?_
  refine (Measurable.subtype_mk ?_).prodMk measurable_id
  exact (hτ.measurable_of_le hτ_le).untopA

lemma measurableSet_preimage_stoppedValue_inter [PseudoMetrizableSpace β] [MeasurableSpace β]
    [BorelSpace β]
    (hf_prog : ProgMeasurable f u) (hτ : IsStoppingTime f τ)
    {t : Set β} (ht : MeasurableSet t) (i : ι) :
    MeasurableSet[f i] (stoppedValue u τ ⁻¹' t ∩ {ω | τ ω ≤ i}) := by
  have h_str_meas : ∀ i, StronglyMeasurable[f i] (stoppedValue u fun ω => min (τ ω) i) := fun i =>
    stronglyMeasurable_stoppedValue_of_le hf_prog (hτ.min_const i) fun _ => min_le_right _ _
  suffices stoppedValue u τ ⁻¹' t ∩ {ω : Ω | τ ω ≤ i} =
      (stoppedValue u fun ω => min (τ ω) i) ⁻¹' t ∩ {ω : Ω | τ ω ≤ i} by
    rw [this]; exact ((h_str_meas i).measurable ht).inter (hτ.measurableSet_le i)
  ext1 ω
  simp only [stoppedValue, Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq,
    and_congr_left_iff]
  intro h
  rw [min_eq_left h]

theorem measurable_stoppedValue [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
    (hf_prog : ProgMeasurable f u) (hτ : IsStoppingTime f τ) :
    Measurable[hτ.measurableSpace] (stoppedValue u τ) := by
  have h_str_meas : ∀ i, StronglyMeasurable[f i] (stoppedValue u fun ω => min (τ ω) i) := fun i =>
    stronglyMeasurable_stoppedValue_of_le hf_prog (hτ.min_const i) fun _ => min_le_right _ _
  intro t ht
  refine ⟨?_, fun i ↦ measurableSet_preimage_stoppedValue_inter hf_prog hτ ht i⟩
  obtain ⟨seq : ℕ → ι, h_seq_tendsto⟩ := (atTop : Filter ι).exists_seq_tendsto
  have : stoppedValue u τ ⁻¹' t
      = (⋃ n, stoppedValue u τ ⁻¹' t ∩ {ω | τ ω ≤ seq n})
        ∪ (stoppedValue u τ ⁻¹' t ∩ {ω | τ ω = ⊤}) := by
    ext1 ω
    simp only [Set.mem_preimage, Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq,
      exists_and_left]
    rw [← and_or_left, iff_self_and]
    intro _
    by_cases h : τ ω = ⊤
    · exact .inr h
    · lift τ ω to ι using h with t
      simp only [WithTop.coe_le_coe, WithTop.coe_ne_top, or_false]
      rw [tendsto_atTop] at h_seq_tendsto
      exact (h_seq_tendsto t).exists
  rw [this]
  refine MeasurableSet.union ?_ ?_
  · exact MeasurableSet.iUnion fun i ↦ f.le (seq i) _
      (measurableSet_preimage_stoppedValue_inter hf_prog hτ ht (seq i))
  · have : stoppedValue u τ ⁻¹' t ∩ {ω | τ ω = ⊤}
       = (fun ω ↦ u (Classical.arbitrary ι) ω) ⁻¹' t ∩ {ω | τ ω = ⊤} := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_preimage, stoppedValue, WithTop.untopA,
        Set.mem_setOf_eq, and_congr_left_iff]
      intro h
      simp [h]
    rw [this]
    refine MeasurableSet.inter (ht.preimage ?_) hτ.measurableSet_eq_top
    exact (hf_prog.adapted (Classical.arbitrary ι)).measurable.mono
      (f.le (Classical.arbitrary ι)) le_rfl

end ProgMeasurable

end LinearOrder

section StoppedValueOfMemFinset

variable [Nonempty ι] {μ : Measure Ω} {τ : Ω → WithTop ι} {E : Type*} {p : ℝ≥0∞} {u : ι → Ω → E}

theorem stoppedValue_eq_of_mem_finset [AddCommMonoid E] {s : Finset ι}
   (hbdd : ∀ ω, τ ω ∈ (WithTop.some '' s)) :
    stoppedValue u τ = ∑ i ∈ s, Set.indicator {ω | τ ω = i} (u i) := by
  ext y
  classical
  rw [stoppedValue, Finset.sum_apply, Finset.sum_indicator_eq_sum_filter]
  suffices {i ∈ s | y ∈ {ω : Ω | τ ω = (i : ι)}} = ({(τ y).untopA} : Finset ι) by
    rw [this, Finset.sum_singleton]
  ext1 ω
  simp only [Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_singleton]
  constructor <;> intro h
  · simp [h.2]
  · simp only [h]
    specialize hbdd y
    have : τ y ≠ ⊤ := fun h_contra ↦ by simp [h_contra] at hbdd
    lift τ y to ι using this with i hi
    simpa using hbdd

theorem stoppedValue_eq' [Preorder ι] [LocallyFiniteOrderBot ι] [AddCommMonoid E] {N : ι}
    (hbdd : ∀ ω, τ ω ≤ N) :
    stoppedValue u τ = ∑ i ∈ Finset.Iic N, Set.indicator {ω | τ ω = i} (u i) := by
  refine stoppedValue_eq_of_mem_finset fun ω ↦ ?_
  simp only [Finset.coe_Iic, Set.mem_image]
  specialize hbdd ω
  have h_top : τ ω ≠ ⊤ := fun h_contra ↦ by simp [h_contra] at hbdd
  lift τ ω to ι using h_top with i hi
  norm_cast at hbdd ⊢
  have h' := Finset.mem_Iic.mpr hbdd
  exact ⟨i, by simpa using h', rfl⟩

theorem stoppedProcess_eq_of_mem_finset [LinearOrder ι] [AddCommMonoid E] {s : Finset ι} (n : ι)
    (hbdd : ∀ ω, τ ω < n → τ ω ∈ WithTop.some '' s) :
    stoppedProcess u τ n = Set.indicator {a | n ≤ τ a} (u n) +
      ∑ i ∈ s with i < n, Set.indicator {ω | τ ω = i} (u i) := by
  ext ω
  rw [Pi.add_apply, Finset.sum_apply]
  rcases le_or_gt (n : WithTop ι) (τ ω) with h | h
  · rw [stoppedProcess_eq_of_le h, Set.indicator_of_mem, Finset.sum_eq_zero, add_zero]
    · intro m hm
      refine Set.indicator_of_notMem ?_ _
      rw [Finset.mem_filter] at hm
      simp only [Set.mem_setOf_eq]
      refine (lt_of_lt_of_le ?_ h).ne'
      exact mod_cast hm.2
    · exact h
  · rw [stoppedProcess_eq_of_ge (le_of_lt h)]
    have h_top : τ ω ≠ ⊤ := fun h_contra ↦ by simp [h_contra] at h
    specialize hbdd ω h
    lift τ ω to ι using h_top with i hi
    rw [Finset.sum_eq_single_of_mem i]
    · simp only [WithTop.untopD_coe]
      rw [Set.indicator_of_notMem, zero_add, Set.indicator_of_mem] <;> rw [Set.mem_setOf]
      · exact hi.symm
      · rw [← hi]
        exact not_le.2 h
    · rw [Finset.mem_filter]
      simp only [Set.mem_image, Finset.mem_coe, WithTop.coe_eq_coe, exists_eq_right] at hbdd
      exact ⟨hbdd, mod_cast h⟩
    · intro b _ hneq
      rw [Set.indicator_of_notMem]
      rw [Set.mem_setOf]
      rw [← hi]
      exact mod_cast hneq.symm

theorem stoppedProcess_eq'' [LinearOrder ι] [LocallyFiniteOrderBot ι] [AddCommMonoid E] (n : ι) :
    stoppedProcess u τ n = Set.indicator {a | n ≤ τ a} (u n) +
      ∑ i ∈ Finset.Iio n, Set.indicator {ω | τ ω = i} (u i) := by
  have h_mem : ∀ ω, τ ω < n → τ ω ∈ WithTop.some '' (Finset.Iio n) := by
    intro ω h
    simp only [Finset.coe_Iio, Set.mem_image, Set.mem_Iio]
    have h_top : τ ω ≠ ⊤ := fun h_contra ↦ by simp [h_contra] at h
    lift τ ω to ι using h_top with i hi
    exact ⟨i, mod_cast h, rfl⟩
  rw [stoppedProcess_eq_of_mem_finset n h_mem]
  congr with i
  simp

section StoppedValue

variable [PartialOrder ι] {ℱ : Filtration ι m} [NormedAddCommGroup E]

theorem memLp_stoppedValue_of_mem_finset (hτ : IsStoppingTime ℱ τ) (hu : ∀ n, MemLp (u n) p μ)
    {s : Finset ι} (hbdd : ∀ ω, τ ω ∈ WithTop.some '' s) :
    MemLp (stoppedValue u τ) p μ := by
  rw [stoppedValue_eq_of_mem_finset hbdd]
  refine memLp_finset_sum' _ fun i _ => MemLp.indicator ?_ (hu i)
  refine ℱ.le i {a : Ω | τ a = i} (hτ.measurableSet_eq_of_countable_range ?_ i)
  refine Set.Finite.countable ?_
  have : Set.range τ ⊆ WithTop.some '' s := by
    intro x hx
    obtain ⟨y, rfl⟩ := hx
    exact hbdd y
  exact ((Finset.finite_toSet s).image _).subset this

theorem memLp_stoppedValue [LocallyFiniteOrderBot ι] (hτ : IsStoppingTime ℱ τ)
    (hu : ∀ n, MemLp (u n) p μ) {N : ι} (hbdd : ∀ ω, τ ω ≤ N) : MemLp (stoppedValue u τ) p μ := by
  refine memLp_stoppedValue_of_mem_finset hτ hu (s := Finset.Iic N) fun ω => ?_
  simp only [Finset.coe_Iic, Set.mem_image, Set.mem_Iic]
  specialize hbdd ω
  have h_top : τ ω ≠ ⊤ := fun h_contra ↦ by simp [h_contra] at hbdd
  lift τ ω to ι using h_top with i hi
  exact ⟨i, mod_cast hbdd, rfl⟩

theorem integrable_stoppedValue_of_mem_finset (hτ : IsStoppingTime ℱ τ)
    (hu : ∀ n, Integrable (u n) μ) {s : Finset ι} (hbdd : ∀ ω, τ ω ∈ WithTop.some '' s) :
    Integrable (stoppedValue u τ) μ := by
  simp_rw [← memLp_one_iff_integrable] at hu ⊢
  exact memLp_stoppedValue_of_mem_finset hτ hu hbdd

variable (ι)

theorem integrable_stoppedValue [LocallyFiniteOrderBot ι] (hτ : IsStoppingTime ℱ τ)
    (hu : ∀ n, Integrable (u n) μ) {N : ι} (hbdd : ∀ ω, τ ω ≤ N) :
    Integrable (stoppedValue u τ) μ := by
  refine integrable_stoppedValue_of_mem_finset hτ hu (s := Finset.Iic N) fun ω => ?_
  simp only [Finset.coe_Iic, Set.mem_image, Set.mem_Iic]
  specialize hbdd ω
  have h_top : τ ω ≠ ⊤ := fun h_contra ↦ by simp [h_contra] at hbdd
  lift τ ω to ι using h_top with i hi
  exact ⟨i, mod_cast hbdd, rfl⟩

end StoppedValue

section StoppedProcess

variable [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι] [FirstCountableTopology ι]
  {ℱ : Filtration ι m} [NormedAddCommGroup E]

theorem memLp_stoppedProcess_of_mem_finset (hτ : IsStoppingTime ℱ τ) (hu : ∀ n, MemLp (u n) p μ)
    (n : ι) {s : Finset ι} (hbdd : ∀ ω, τ ω < n → τ ω ∈ WithTop.some '' s) :
    MemLp (stoppedProcess u τ n) p μ := by
  rw [stoppedProcess_eq_of_mem_finset n hbdd]
  refine MemLp.add ?_ ?_
  · exact MemLp.indicator (ℱ.le n {a : Ω | n ≤ τ a} (hτ.measurableSet_ge n)) (hu n)
  · suffices MemLp (fun ω => ∑ i ∈ s with i < n, {a : Ω | τ a = i}.indicator (u i) ω) p μ by
      convert this using 1; ext1 ω; simp only [Finset.sum_apply]
    refine memLp_finset_sum _ fun i _ => MemLp.indicator ?_ (hu i)
    exact ℱ.le i {a : Ω | τ a = i} (hτ.measurableSet_eq i)

theorem memLp_stoppedProcess [LocallyFiniteOrderBot ι] (hτ : IsStoppingTime ℱ τ)
    (hu : ∀ n, MemLp (u n) p μ) (n : ι) :
    MemLp (stoppedProcess u τ n) p μ := by
  refine memLp_stoppedProcess_of_mem_finset hτ hu n (s := Finset.Iic n) fun ω h => ?_
  simp only [Finset.coe_Iic, Set.mem_image, Set.mem_Iic]
  have h_top : τ ω ≠ ⊤ := fun h_contra ↦ by simp [h_contra] at h
  lift τ ω to ι using h_top with i hi
  exact ⟨i, mod_cast h.le, rfl⟩

theorem integrable_stoppedProcess_of_mem_finset (hτ : IsStoppingTime ℱ τ)
    (hu : ∀ n, Integrable (u n) μ) (n : ι) {s : Finset ι}
    (hbdd : ∀ ω, τ ω < n → τ ω ∈ WithTop.some '' s) :
    Integrable (stoppedProcess u τ n) μ := by
  simp_rw [← memLp_one_iff_integrable] at hu ⊢
  exact memLp_stoppedProcess_of_mem_finset hτ hu n hbdd

theorem integrable_stoppedProcess [LocallyFiniteOrderBot ι] (hτ : IsStoppingTime ℱ τ)
    (hu : ∀ n, Integrable (u n) μ) (n : ι) : Integrable (stoppedProcess u τ n) μ := by
  refine integrable_stoppedProcess_of_mem_finset hτ hu n (s := Finset.Iic n) fun ω h => ?_
  simp only [Finset.coe_Iic, Set.mem_image, Set.mem_Iic]
  have h_top : τ ω ≠ ⊤ := fun h_contra ↦ by simp [h_contra] at h
  lift τ ω to ι using h_top with i hi
  exact ⟨i, mod_cast h.le, rfl⟩

end StoppedProcess

end StoppedValueOfMemFinset

section AdaptedStoppedProcess

variable [TopologicalSpace β] [PseudoMetrizableSpace β] [Nonempty ι] [LinearOrder ι]
  [TopologicalSpace ι] [SecondCountableTopology ι] [OrderTopology ι]
  [MeasurableSpace ι] [BorelSpace ι]
  {f : Filtration ι m} {u : ι → Ω → β} {τ : Ω → WithTop ι}

/-- The stopped process of an adapted process with continuous paths is adapted. -/
theorem Adapted.stoppedProcess [MetrizableSpace ι] (hu : Adapted f u)
    (hu_cont : ∀ ω, Continuous fun i => u i ω) (hτ : IsStoppingTime f τ) :
    Adapted f (stoppedProcess u τ) :=
  ((hu.progMeasurable_of_continuous hu_cont).stoppedProcess hτ).adapted

/-- If the indexing order has the discrete topology, then the stopped process of an adapted process
is adapted. -/
theorem Adapted.stoppedProcess_of_discrete [DiscreteTopology ι] (hu : Adapted f u)
    (hτ : IsStoppingTime f τ) : Adapted f (MeasureTheory.stoppedProcess u τ) :=
  (hu.progMeasurable_of_discrete.stoppedProcess hτ).adapted

theorem Adapted.stronglyMeasurable_stoppedProcess [MetrizableSpace ι] (hu : Adapted f u)
    (hu_cont : ∀ ω, Continuous fun i => u i ω) (hτ : IsStoppingTime f τ) (n : ι) :
    StronglyMeasurable (MeasureTheory.stoppedProcess u τ n) :=
  (hu.progMeasurable_of_continuous hu_cont).stronglyMeasurable_stoppedProcess hτ n

theorem Adapted.stronglyMeasurable_stoppedProcess_of_discrete [DiscreteTopology ι]
    (hu : Adapted f u) (hτ : IsStoppingTime f τ) (n : ι) :
    StronglyMeasurable (MeasureTheory.stoppedProcess u τ n) :=
  hu.progMeasurable_of_discrete.stronglyMeasurable_stoppedProcess hτ n

end AdaptedStoppedProcess

section Nat

/-! ### Filtrations indexed by `ℕ` -/


open Filtration

variable {u : ℕ → Ω → β} {τ π : Ω → ℕ∞}

theorem stoppedValue_sub_eq_sum [AddCommGroup β] (hle : τ ≤ π) (hπ : ∀ ω, π ω ≠ ∞) :
    stoppedValue u π - stoppedValue u τ = fun ω =>
      (∑ i ∈ Finset.Ico (τ ω).untopA (π ω).untopA, (u (i + 1) - u i)) ω := by
  ext ω
  have h_le' : (τ ω).untopA ≤ (π ω).untopA := WithTop.untopA_mono (mod_cast hπ ω) (hle ω)
  rw [Finset.sum_Ico_eq_sub _ h_le', Finset.sum_range_sub, Finset.sum_range_sub]
  simp [stoppedValue]

theorem stoppedValue_sub_eq_sum' [AddCommGroup β] (hle : τ ≤ π) {N : ℕ} (hbdd : ∀ ω, π ω ≤ N) :
    stoppedValue u π - stoppedValue u τ = fun ω =>
      (∑ i ∈ Finset.range (N + 1), Set.indicator {ω | τ ω ≤ i ∧ i < π ω} (u (i + 1) - u i)) ω := by
  have hπ_top ω : π ω ≠ ⊤ := fun h ↦ by specialize hbdd ω; simp [h] at hbdd
  have hτ_top ω : τ ω ≠ ⊤ := ne_top_of_le_ne_top (hπ_top ω) (mod_cast hle ω)
  rw [stoppedValue_sub_eq_sum hle]
  swap; · intro ω; exact mod_cast hπ_top ω
  ext ω
  simp only [Finset.sum_apply, Finset.sum_indicator_eq_sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext i
  simp only [Finset.mem_filter, Set.mem_setOf_eq, Finset.mem_range, Finset.mem_Ico]
  specialize hbdd ω
  lift τ ω to ℕ using hτ_top ω with t ht
  lift π ω to ℕ using hπ_top ω with b hb
  simp only [Nat.cast_le] at hbdd
  simp
  grind

section AddCommMonoid

variable [AddCommMonoid β]

theorem stoppedValue_eq {N : ℕ} (hbdd : ∀ ω, τ ω ≤ N) : stoppedValue u τ = fun x =>
    (∑ i ∈ Finset.range (N + 1), Set.indicator {ω | τ ω = i} (u i)) x := by
  refine stoppedValue_eq_of_mem_finset fun ω ↦ ?_
  specialize hbdd ω
  have h_top : τ ω ≠ ⊤ := fun h_contra ↦ by simp [h_contra] at hbdd
  lift τ ω to ℕ using h_top with t ht
  simp only [Nat.cast_le] at hbdd
  simp only [ENat.some_eq_coe, Finset.coe_range, Set.mem_image, Set.mem_Iio, Nat.cast_inj,
    exists_eq_right, gt_iff_lt]
  grind

theorem stoppedProcess_eq (n : ℕ) : stoppedProcess u τ n = Set.indicator {a | n ≤ τ a} (u n) +
    ∑ i ∈ Finset.range n, Set.indicator {ω | τ ω = i} (u i) := by
  rw [stoppedProcess_eq'' n]
  congr with i
  rw [Finset.mem_Iio, Finset.mem_range]

theorem stoppedProcess_eq' (n : ℕ) : stoppedProcess u τ n = Set.indicator {a | n + 1 ≤ τ a} (u n) +
    ∑ i ∈ Finset.range (n + 1), Set.indicator {a | τ a = i} (u i) := by
  have : {a | n ≤ τ a}.indicator (u n) =
      {a | n + 1 ≤ τ a}.indicator (u n) + {a | τ a = n}.indicator (u n) := by
    ext x
    rw [add_comm, Pi.add_apply, ← Set.indicator_union_of_notMem_inter]
    · simp_rw [@eq_comm _ _ (n : WithTop ℕ), @le_iff_eq_or_lt _ _ (n : WithTop ℕ)]
      have : {a | ↑n + 1 ≤ τ a} = {a | ↑n < τ a} := by
        ext ω
        simp only [Set.mem_setOf_eq]
        cases τ ω with
        | top => simp
        | coe t =>
          simp only [Nat.cast_lt]
          norm_cast
      rw [this]
      simp_rw [Set.setOf_or]
    · rintro ⟨h₁, h₂⟩
      rw [Set.mem_setOf] at h₁ h₂
      rw [h₁] at h₂
      norm_cast at h₂
      grind
  rw [stoppedProcess_eq, this, Finset.sum_range_succ_comm, ← add_assoc]

end AddCommMonoid

end Nat

section PiecewiseConst

variable [Preorder ι] {𝒢 : Filtration ι m} {τ η : Ω → WithTop ι} {i j : ι} {s : Set Ω}
  [DecidablePred (· ∈ s)]

/-- Given stopping times `τ` and `η` which are bounded below, `Set.piecewise s τ η` is also
a stopping time with respect to the same filtration. -/
theorem IsStoppingTime.piecewise_of_le (hτ_st : IsStoppingTime 𝒢 τ) (hη_st : IsStoppingTime 𝒢 η)
    (hτ : ∀ ω, i ≤ τ ω) (hη : ∀ ω, i ≤ η ω) (hs : MeasurableSet[𝒢 i] s) :
    IsStoppingTime 𝒢 (s.piecewise τ η) := by
  intro n
  have : {ω | s.piecewise τ η ω ≤ n} = s ∩ {ω | τ ω ≤ n} ∪ sᶜ ∩ {ω | η ω ≤ n} := by
    ext1 ω
    simp only [Set.piecewise, Set.mem_setOf_eq]
    by_cases hx : ω ∈ s <;> simp [hx]
  rw [this]
  by_cases hin : i ≤ n
  · have hs_n : MeasurableSet[𝒢 n] s := 𝒢.mono hin _ hs
    exact (hs_n.inter (hτ_st n)).union (hs_n.compl.inter (hη_st n))
  · have hτn : ∀ ω, ¬τ ω ≤ n := fun ω hτn => hin (mod_cast (hτ ω).trans hτn)
    have hηn : ∀ ω, ¬η ω ≤ n := fun ω hηn => hin (mod_cast (hη ω).trans hηn)
    simp [hτn, hηn, @MeasurableSet.empty _ _]

theorem isStoppingTime_piecewise_const (hij : i ≤ j) (hs : MeasurableSet[𝒢 i] s) :
    IsStoppingTime 𝒢 (s.piecewise (fun _ => i) fun _ => j) :=
  (isStoppingTime_const 𝒢 i).piecewise_of_le (isStoppingTime_const 𝒢 j) (fun _ => le_rfl)
    (fun _ => mod_cast hij) hs

theorem stoppedValue_piecewise_const {ι' : Type*} [Nonempty ι'] {i j : ι'} {f : ι' → Ω → ℝ} :
    stoppedValue f (s.piecewise (fun _ => i) fun _ => j) = s.piecewise (f i) (f j) := by
  ext ω; rw [stoppedValue]; by_cases hx : ω ∈ s <;> simp [hx]

theorem stoppedValue_piecewise_const' {ι' : Type*} [Nonempty ι'] {i j : ι'} {f : ι' → Ω → ℝ} :
    stoppedValue f (s.piecewise (fun _ => i) fun _ => j) =
    s.indicator (f i) + sᶜ.indicator (f j) := by
  ext ω; rw [stoppedValue]; by_cases hx : ω ∈ s <;> simp [hx]

end PiecewiseConst

section Condexp

/-! ### Conditional expectation with respect to the σ-algebra generated by a stopping time -/


variable [LinearOrder ι] {μ : Measure Ω} {ℱ : Filtration ι m} {τ σ : Ω → WithTop ι} {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f : Ω → E}

theorem condExp_stopping_time_ae_eq_restrict_eq_of_countable_range [SigmaFiniteFiltration μ ℱ]
    (hτ : IsStoppingTime ℱ τ) (h_countable : (Set.range τ).Countable)
    [SigmaFinite (μ.trim (hτ.measurableSpace_le))] (i : ι) :
    μ[f|hτ.measurableSpace] =ᵐ[μ.restrict {x | τ x = i}] μ[f|ℱ i] := by
  refine condExp_ae_eq_restrict_of_measurableSpace_eq_on
    (hτ.measurableSpace_le) (ℱ.le i)
    (hτ.measurableSet_eq_of_countable_range' h_countable i) fun t => ?_
  rw [Set.inter_comm _ t, IsStoppingTime.measurableSet_inter_eq_iff]

theorem condExp_stopping_time_ae_eq_restrict_eq_of_countable [Countable ι]
    [SigmaFiniteFiltration μ ℱ] (hτ : IsStoppingTime ℱ τ)
    [SigmaFinite (μ.trim hτ.measurableSpace_le)] (i : ι) :
    μ[f|hτ.measurableSpace] =ᵐ[μ.restrict {x | τ x = i}] μ[f|ℱ i] :=
  condExp_stopping_time_ae_eq_restrict_eq_of_countable_range hτ (Set.to_countable _) i

theorem condExp_min_stopping_time_ae_eq_restrict_le_const (hτ : IsStoppingTime ℱ τ) (i : ι)
    [SigmaFinite (μ.trim (hτ.min_const i).measurableSpace_le)] :
    μ[f|(hτ.min_const i).measurableSpace] =ᵐ[μ.restrict {x | τ x ≤ i}] μ[f|hτ.measurableSpace] := by
  have : SigmaFinite (μ.trim hτ.measurableSpace_le) :=
    haveI h_le : (hτ.min_const i).measurableSpace ≤ hτ.measurableSpace := by
      rw [IsStoppingTime.measurableSpace_min_const]
      exact inf_le_left
    sigmaFiniteTrim_mono _ h_le
  refine (condExp_ae_eq_restrict_of_measurableSpace_eq_on hτ.measurableSpace_le
    (hτ.min_const i).measurableSpace_le (hτ.measurableSet_le' i) fun t => ?_).symm
  rw [Set.inter_comm _ t, hτ.measurableSet_inter_le_const_iff]

variable [TopologicalSpace ι] [OrderTopology ι]

theorem condExp_stopping_time_ae_eq_restrict_eq [FirstCountableTopology ι]
    [SigmaFiniteFiltration μ ℱ] (hτ : IsStoppingTime ℱ τ)
    [SigmaFinite (μ.trim hτ.measurableSpace_le)] (i : ι) :
    μ[f|hτ.measurableSpace] =ᵐ[μ.restrict {x | τ x = i}] μ[f|ℱ i] := by
  refine condExp_ae_eq_restrict_of_measurableSpace_eq_on hτ.measurableSpace_le (ℱ.le i)
    (hτ.measurableSet_eq' i) fun t => ?_
  rw [Set.inter_comm _ t, IsStoppingTime.measurableSet_inter_eq_iff]

theorem condExp_min_stopping_time_ae_eq_restrict_le [SecondCountableTopology ι]
    (hτ : IsStoppingTime ℱ τ) (hσ : IsStoppingTime ℱ σ)
    [SigmaFinite (μ.trim (hτ.min hσ).measurableSpace_le)] :
    μ[f|(hτ.min hσ).measurableSpace] =ᵐ[μ.restrict {x | τ x ≤ σ x}] μ[f|hτ.measurableSpace] := by
  have : SigmaFinite (μ.trim hτ.measurableSpace_le) :=
    haveI h_le : (hτ.min hσ).measurableSpace ≤ hτ.measurableSpace := by
      rw [IsStoppingTime.measurableSpace_min]
      · exact inf_le_left
      · simp_all only
    sigmaFiniteTrim_mono _ h_le
  refine (condExp_ae_eq_restrict_of_measurableSpace_eq_on hτ.measurableSpace_le
    (hτ.min hσ).measurableSpace_le (hτ.measurableSet_le_stopping_time hσ) fun t => ?_).symm
  rw [Set.inter_comm _ t, IsStoppingTime.measurableSet_inter_le_iff]; simp_all only

end Condexp

end MeasureTheory
