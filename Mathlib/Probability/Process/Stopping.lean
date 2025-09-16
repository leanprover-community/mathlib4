/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Rémy Degenne
-/
import Mathlib.Probability.Process.Adapted
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

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
def IsStoppingTime [Preorder ι] (f : Filtration ι m) (τ : Ω → ι) :=
  ∀ i : ι, MeasurableSet[f i] <| {ω | τ ω ≤ i}

theorem isStoppingTime_const [Preorder ι] (f : Filtration ι m) (i : ι) :
    IsStoppingTime f fun _ => i := fun j => by simp only [MeasurableSet.const]

section MeasurableSet

section Preorder

variable [Preorder ι] {f : Filtration ι m} {τ : Ω → ι}

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
    exact hi_min (τ ω)
  have : {ω : Ω | τ ω < i} = τ ⁻¹' Set.Iic (pred i) := by ext; simp [Iic_pred_of_not_isMin hi_min]
  rw [this]
  exact f.mono (pred_le i) _ (hτ.measurableSet_le <| pred i)

end Preorder

section CountableStoppingTime

namespace IsStoppingTime

variable [PartialOrder ι] {τ : Ω → ι} {f : Filtration ι m}

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
  · exact f.mono hji.le _ (hτ.measurableSet_le j)
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

protected theorem measurableSet_ge_of_countable_range {ι} [LinearOrder ι] {τ : Ω → ι}
    {f : Filtration ι m} (hτ : IsStoppingTime f τ) (h_countable : (Set.range τ).Countable) (i : ι) :
    MeasurableSet[f i] {ω | i ≤ τ ω} := by
  have : {ω | i ≤ τ ω} = {ω | τ ω < i}ᶜ := by
    ext1 ω; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_lt]
  rw [this]
  exact (hτ.measurableSet_lt_of_countable_range h_countable i).compl

protected theorem measurableSet_ge_of_countable {ι} [LinearOrder ι] {τ : Ω → ι} {f : Filtration ι m}
    [Countable ι] (hτ : IsStoppingTime f τ) (i : ι) : MeasurableSet[f i] {ω | i ≤ τ ω} :=
  hτ.measurableSet_ge_of_countable_range (Set.to_countable _) i

end IsStoppingTime

end CountableStoppingTime

section LinearOrder

variable [LinearOrder ι] {f : Filtration ι m} {τ : Ω → ι}

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
    exact isMin_iff_forall_not_lt.mp hi_min (τ ω)
  obtain ⟨seq, -, -, h_tendsto, h_bound⟩ :
      ∃ seq : ℕ → ι, Monotone seq ∧ (∀ j, seq j ≤ i) ∧ Tendsto seq atTop (𝓝 i) ∧ ∀ j, seq j < i :=
    h_lub.exists_seq_monotone_tendsto (not_isMin_iff.mp hi_min)
  have h_Ioi_eq_Union : Set.Iio i = ⋃ j, {k | k ≤ seq j} := by
    ext1 k
    simp only [Set.mem_Iio, Set.mem_iUnion, Set.mem_setOf_eq]
    refine ⟨fun hk_lt_i => ?_, fun h_exists_k_le_seq => ?_⟩
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
  simp only [Set.preimage_iUnion, Set.preimage_setOf_eq]
  exact MeasurableSet.iUnion fun n => f.mono (h_bound n).le _ (hτ.measurableSet_le (seq n))

theorem IsStoppingTime.measurableSet_lt (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[f i] {ω | τ ω < i} := by
  obtain ⟨i', hi'_lub⟩ : ∃ i', IsLUB (Set.Iio i) i' := exists_lub_Iio i
  rcases lub_Iio_eq_self_or_Iio_eq_Iic i hi'_lub with hi'_eq_i | h_Iio_eq_Iic
  · rw [← hi'_eq_i] at hi'_lub ⊢
    exact hτ.measurableSet_lt_of_isLUB i' hi'_lub
  · have h_lt_eq_preimage : {ω : Ω | τ ω < i} = τ ⁻¹' Set.Iio i := rfl
    rw [h_lt_eq_preimage, h_Iio_eq_Iic]
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
    {τ : Ω → ι} (hτ : ∀ i, MeasurableSet[f i] {ω | τ ω = i}) : IsStoppingTime f τ := by
  intro i
  rw [show {ω | τ ω ≤ i} = ⋃ k ≤ i, {ω | τ ω = k} by ext; simp]
  refine MeasurableSet.biUnion (Set.to_countable _) fun k hk => ?_
  exact f.mono hk _ (hτ k)

end Countable

end MeasurableSet

namespace IsStoppingTime

protected theorem max [LinearOrder ι] {f : Filtration ι m} {τ π : Ω → ι} (hτ : IsStoppingTime f τ)
    (hπ : IsStoppingTime f π) : IsStoppingTime f fun ω => max (τ ω) (π ω) := by
  intro i
  simp_rw [max_le_iff, Set.setOf_and]
  exact (hτ i).inter (hπ i)

protected theorem max_const [LinearOrder ι] {f : Filtration ι m} {τ : Ω → ι}
    (hτ : IsStoppingTime f τ) (i : ι) : IsStoppingTime f fun ω => max (τ ω) i :=
  hτ.max (isStoppingTime_const f i)

protected theorem min [LinearOrder ι] {f : Filtration ι m} {τ π : Ω → ι} (hτ : IsStoppingTime f τ)
    (hπ : IsStoppingTime f π) : IsStoppingTime f fun ω => min (τ ω) (π ω) := by
  intro i
  simp_rw [min_le_iff, Set.setOf_or]
  exact (hτ i).union (hπ i)

protected theorem min_const [LinearOrder ι] {f : Filtration ι m} {τ : Ω → ι}
    (hτ : IsStoppingTime f τ) (i : ι) : IsStoppingTime f fun ω => min (τ ω) i :=
  hτ.min (isStoppingTime_const f i)

theorem add_const [AddGroup ι] [Preorder ι] [AddRightMono ι]
    [AddLeftMono ι] {f : Filtration ι m} {τ : Ω → ι} (hτ : IsStoppingTime f τ)
    {i : ι} (hi : 0 ≤ i) : IsStoppingTime f fun ω => τ ω + i := by
  intro j
  simp_rw [← le_sub_iff_add_le]
  exact f.mono (sub_le_self j hi) _ (hτ (j - i))

theorem add_const_nat {f : Filtration ℕ m} {τ : Ω → ℕ} (hτ : IsStoppingTime f τ) {i : ℕ} :
    IsStoppingTime f fun ω => τ ω + i := by
  refine isStoppingTime_of_measurableSet_eq fun j => ?_
  by_cases hij : i ≤ j
  · simp_rw [eq_comm, ← Nat.sub_eq_iff_eq_add hij, eq_comm]
    exact f.mono (j.sub_le i) _ (hτ.measurableSet_eq (j - i))
  · rw [not_le] at hij
    convert @MeasurableSet.empty _ (f.1 j)
    ext ω
    simp only [Set.mem_empty_iff_false, iff_false, Set.mem_setOf]
    omega

-- generalize to certain countable type?
theorem add {f : Filtration ℕ m} {τ π : Ω → ℕ} (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) :
    IsStoppingTime f (τ + π) := by
  intro i
  rw [(_ : {ω | (τ + π) ω ≤ i} = ⋃ k ≤ i, {ω | π ω = k} ∩ {ω | τ ω + k ≤ i})]
  · exact MeasurableSet.iUnion fun k =>
      MeasurableSet.iUnion fun hk => (hπ.measurableSet_eq_le hk).inter (hτ.add_const_nat i)
  ext ω
  simp only [Pi.add_apply, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, exists_prop]
  refine ⟨fun h => ⟨π ω, by omega, rfl, h⟩, ?_⟩
  rintro ⟨j, hj, rfl, h⟩
  assumption

section Preorder

variable [Preorder ι] {f : Filtration ι m} {τ π : Ω → ι}

/-- The associated σ-algebra with a stopping time. -/
protected def measurableSpace (hτ : IsStoppingTime f τ) : MeasurableSpace Ω where
  MeasurableSet' s := ∀ i : ι, MeasurableSet[f i] (s ∩ {ω | τ ω ≤ i})
  measurableSet_empty i := (Set.empty_inter {ω | τ ω ≤ i}).symm ▸ @MeasurableSet.empty _ (f i)
  measurableSet_compl s hs i := by
    rw [(_ : sᶜ ∩ {ω | τ ω ≤ i} = (sᶜ ∪ {ω | τ ω ≤ i}ᶜ) ∩ {ω | τ ω ≤ i})]
    · refine MeasurableSet.inter ?_ ?_
      · rw [← Set.compl_inter]
        exact (hs i).compl
      · exact hτ i
    · rw [Set.union_inter_distrib_right]
      simp only [Set.compl_inter_self, Set.union_empty]
  measurableSet_iUnion s hs i := by
    rw [forall_swap] at hs
    rw [Set.iUnion_inter]
    exact MeasurableSet.iUnion (hs i)

protected theorem measurableSet (hτ : IsStoppingTime f τ) (s : Set Ω) :
    MeasurableSet[hτ.measurableSpace] s ↔ ∀ i : ι, MeasurableSet[f i] (s ∩ {ω | τ ω ≤ i}) :=
  Iff.rfl

theorem measurableSpace_mono (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) (hle : τ ≤ π) :
    hτ.measurableSpace ≤ hπ.measurableSpace := by
  intro s hs i
  rw [(_ : s ∩ {ω | π ω ≤ i} = s ∩ {ω | τ ω ≤ i} ∩ {ω | π ω ≤ i})]
  · exact (hs i).inter (hπ i)
  · ext
    simp only [Set.mem_inter_iff, iff_self_and, and_congr_left_iff, Set.mem_setOf_eq]
    intro hle' _
    exact le_trans (hle _) hle'

theorem measurableSpace_le_of_countable [Countable ι] (hτ : IsStoppingTime f τ) :
    hτ.measurableSpace ≤ m := by
  intro s hs
  change ∀ i, MeasurableSet[f i] (s ∩ {ω | τ ω ≤ i}) at hs
  rw [(_ : s = ⋃ i, s ∩ {ω | τ ω ≤ i})]
  · exact MeasurableSet.iUnion fun i => f.le i _ (hs i)
  · ext ω; constructor <;> rw [Set.mem_iUnion]
    · exact fun hx => ⟨τ ω, hx, le_rfl⟩
    · rintro ⟨_, hx, _⟩
      exact hx

theorem measurableSpace_le [IsCountablyGenerated (atTop : Filter ι)] [IsDirected ι (· ≤ ·)]
    (hτ : IsStoppingTime f τ) : hτ.measurableSpace ≤ m := by
  intro s hs
  cases isEmpty_or_nonempty ι
  · haveI : IsEmpty Ω := ⟨fun ω => IsEmpty.false (τ ω)⟩
    apply Subsingleton.measurableSet
  · change ∀ i, MeasurableSet[f i] (s ∩ {ω | τ ω ≤ i}) at hs
    obtain ⟨seq : ℕ → ι, h_seq_tendsto⟩ := (atTop : Filter ι).exists_seq_tendsto
    rw [(_ : s = ⋃ n, s ∩ {ω | τ ω ≤ seq n})]
    · exact MeasurableSet.iUnion fun i => f.le (seq i) _ (hs (seq i))
    · ext ω; constructor <;> rw [Set.mem_iUnion]
      · intro hx
        suffices ∃ i, τ ω ≤ seq i from ⟨this.choose, hx, this.choose_spec⟩
        rw [tendsto_atTop] at h_seq_tendsto
        exact (h_seq_tendsto (τ ω)).exists
      · rintro ⟨_, hx, _⟩
        exact hx

example {f : Filtration ℕ m} {τ : Ω → ℕ} (hτ : IsStoppingTime f τ) : hτ.measurableSpace ≤ m :=
  hτ.measurableSpace_le

example {f : Filtration ℝ m} {τ : Ω → ℝ} (hτ : IsStoppingTime f τ) : hτ.measurableSpace ≤ m :=
  hτ.measurableSpace_le

@[simp]
theorem measurableSpace_const (f : Filtration ι m) (i : ι) :
    (isStoppingTime_const f i).measurableSpace = f i := by
  ext1 s
  change MeasurableSet[(isStoppingTime_const f i).measurableSpace] s ↔ MeasurableSet[f i] s
  rw [IsStoppingTime.measurableSet]
  constructor <;> intro h
  · specialize h i
    simpa only [le_refl, Set.setOf_true, Set.inter_univ] using h
  · intro j
    by_cases hij : i ≤ j
    · simp only [hij, Set.setOf_true, Set.inter_univ]
      exact f.mono hij _ h
    · simp only [hij, Set.setOf_false, Set.inter_empty, @MeasurableSet.empty _ (f.1 j)]

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
  · specialize h i
    simpa only [Set.inter_assoc, this, le_refl, Set.setOf_true, Set.inter_univ] using h
  · intro j
    rw [Set.inter_assoc, this]
    by_cases hij : i ≤ j
    · simp only [hij, Set.setOf_true, Set.inter_univ]
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
    [(Filter.atTop : Filter ι).IsCountablyGenerated] {μ : Measure Ω} {f : Filtration ι m}
    {τ : Ω → ι} [SigmaFiniteFiltration μ f] (hτ : IsStoppingTime f τ) :
    SigmaFinite (μ.trim hτ.measurableSpace_le) := by
  refine @sigmaFiniteTrim_mono _ _ ?_ _ _ _ ?_ ?_
  · exact f ⊥
  · exact hτ.le_measurableSpace_of_const_le fun _ => bot_le
  · infer_instance

instance sigmaFinite_stopping_time_of_le {ι} [SemilatticeSup ι] [OrderBot ι] {μ : Measure Ω}
    {f : Filtration ι m} {τ : Ω → ι} [SigmaFiniteFiltration μ f] (hτ : IsStoppingTime f τ) {n : ι}
    (hτ_le : ∀ ω, τ ω ≤ n) : SigmaFinite (μ.trim (hτ.measurableSpace_le_of_le hτ_le)) := by
  refine @sigmaFiniteTrim_mono _ _ ?_ _ _ _ ?_ ?_
  · exact f ⊥
  · exact hτ.le_measurableSpace_of_const_le fun _ => bot_le
  · infer_instance

section LinearOrder

variable [LinearOrder ι] {f : Filtration ι m} {τ π : Ω → ι}

protected theorem measurableSet_le' (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[hτ.measurableSpace] {ω | τ ω ≤ i} := by
  intro j
  have : {ω : Ω | τ ω ≤ i} ∩ {ω : Ω | τ ω ≤ j} = {ω : Ω | τ ω ≤ min i j} := by
    ext1 ω; simp only [Set.mem_inter_iff, Set.mem_setOf_eq, le_min_iff]
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

protected theorem measurableSpace_le_of_countable_range (hτ : IsStoppingTime f τ)
    (h_countable : (Set.range τ).Countable) : hτ.measurableSpace ≤ m := by
  intro s hs
  change ∀ i, MeasurableSet[f i] (s ∩ {ω | τ ω ≤ i}) at hs
  rw [(_ : s = ⋃ i ∈ Set.range τ, s ∩ {ω | τ ω ≤ i})]
  · exact MeasurableSet.biUnion h_countable fun i _ => f.le i _ (hs i)
  · ext ω
    constructor <;> rw [Set.mem_iUnion]
    · exact fun hx => ⟨τ ω, by simpa using hx⟩
    · rintro ⟨i, hx⟩
      simp only [Set.mem_range, Set.iUnion_exists, Set.mem_iUnion, Set.mem_inter_iff,
        Set.mem_setOf_eq, exists_prop, exists_and_right] at hx
      exact hx.2.1

end Countable

protected theorem measurable [TopologicalSpace ι] [MeasurableSpace ι] [BorelSpace ι]
    [OrderTopology ι] [SecondCountableTopology ι] (hτ : IsStoppingTime f τ) :
    Measurable[hτ.measurableSpace] τ :=
  @measurable_of_Iic ι Ω _ _ _ hτ.measurableSpace _ _ _ _ fun i => hτ.measurableSet_le' i

protected theorem measurable_of_le [TopologicalSpace ι] [MeasurableSpace ι] [BorelSpace ι]
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
    exact fun h i => (h.left i).union (h.right i)

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
    [MeasurableSpace ι] [BorelSpace ι] (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π)
    (s : Set Ω) (hs : MeasurableSet[hτ.measurableSpace] s) :
    MeasurableSet[(hτ.min hπ).measurableSpace] (s ∩ {ω | τ ω ≤ π ω}) := by
  simp_rw [IsStoppingTime.measurableSet] at hs ⊢
  intro i
  have : s ∩ {ω | τ ω ≤ π ω} ∩ {ω | min (τ ω) (π ω) ≤ i} =
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
  rw [this]
  refine ((hs i).inter ((hτ.min hπ) i)).inter ?_
  apply @measurableSet_le _ _ _ _ _ (Filtration.seq f i) _ _ _ _ _ ?_ ?_
  · exact (hτ.min_const i).measurable_of_le fun _ => min_le_right _ _
  · exact ((hτ.min hπ).min_const i).measurable_of_le fun _ => min_le_right _ _

theorem measurableSet_inter_le_iff [TopologicalSpace ι] [SecondCountableTopology ι]
    [OrderTopology ι] [MeasurableSpace ι] [BorelSpace ι] (hτ : IsStoppingTime f τ)
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
  refine ⟨fun h => ⟨h, ?_⟩, fun h j => h.1 j⟩
  specialize h i
  rwa [Set.inter_assoc, Set.inter_self] at h

theorem measurableSet_le_stopping_time [TopologicalSpace ι] [SecondCountableTopology ι]
    [OrderTopology ι] [MeasurableSpace ι] [BorelSpace ι] (hτ : IsStoppingTime f τ)
    (hπ : IsStoppingTime f π) : MeasurableSet[hτ.measurableSpace] {ω | τ ω ≤ π ω} := by
  rw [hτ.measurableSet]
  intro j
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

theorem measurableSet_stopping_time_le [TopologicalSpace ι] [SecondCountableTopology ι]
    [OrderTopology ι] [MeasurableSpace ι] [BorelSpace ι] (hτ : IsStoppingTime f τ)
    (hπ : IsStoppingTime f π) : MeasurableSet[hπ.measurableSpace] {ω | τ ω ≤ π ω} := by
  suffices MeasurableSet[(hτ.min hπ).measurableSpace] {ω : Ω | τ ω ≤ π ω} by
    rw [measurableSet_min_iff hτ hπ] at this; exact this.2
  rw [← Set.univ_inter {ω : Ω | τ ω ≤ π ω}, ← hτ.measurableSet_inter_le_iff hπ, Set.univ_inter]
  exact measurableSet_le_stopping_time hτ hπ

theorem measurableSet_eq_stopping_time [AddGroup ι] [TopologicalSpace ι] [MeasurableSpace ι]
    [BorelSpace ι] [OrderTopology ι] [MeasurableSingletonClass ι] [SecondCountableTopology ι]
    [MeasurableSub₂ ι] (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) :
    MeasurableSet[hτ.measurableSpace] {ω | τ ω = π ω} := by
  rw [hτ.measurableSet]
  intro j
  have : {ω | τ ω = π ω} ∩ {ω | τ ω ≤ j} =
      {ω | min (τ ω) j = min (π ω) j} ∩ {ω | τ ω ≤ j} ∩ {ω | π ω ≤ j} := by
    ext1 ω
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    refine ⟨fun h => ⟨⟨?_, h.2⟩, ?_⟩, fun h => ⟨?_, h.1.2⟩⟩
    · rw [h.1]
    · rw [← h.1]; exact h.2
    · obtain ⟨h', hσ_le⟩ := h
      obtain ⟨h_eq, hτ_le⟩ := h'
      rwa [min_eq_left hτ_le, min_eq_left hσ_le] at h_eq
  rw [this]
  refine
    MeasurableSet.inter (MeasurableSet.inter ?_ (hτ.measurableSet_le j)) (hπ.measurableSet_le j)
  apply measurableSet_eq_fun
  · exact (hτ.min_const j).measurable_of_le fun _ => min_le_right _ _
  · exact (hπ.min_const j).measurable_of_le fun _ => min_le_right _ _

theorem measurableSet_eq_stopping_time_of_countable [Countable ι] [TopologicalSpace ι]
    [MeasurableSpace ι] [BorelSpace ι] [OrderTopology ι] [MeasurableSingletonClass ι]
    [SecondCountableTopology ι] (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) :
    MeasurableSet[hτ.measurableSpace] {ω | τ ω = π ω} := by
  rw [hτ.measurableSet]
  intro j
  have : {ω | τ ω = π ω} ∩ {ω | τ ω ≤ j} =
      {ω | min (τ ω) j = min (π ω) j} ∩ {ω | τ ω ≤ j} ∩ {ω | π ω ≤ j} := by
    ext1 ω
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    refine ⟨fun h => ⟨⟨?_, h.2⟩, ?_⟩, fun h => ⟨?_, h.1.2⟩⟩
    · rw [h.1]
    · rw [← h.1]; exact h.2
    · obtain ⟨h', hπ_le⟩ := h
      obtain ⟨h_eq, hτ_le⟩ := h'
      rwa [min_eq_left hτ_le, min_eq_left hπ_le] at h_eq
  rw [this]
  refine
    MeasurableSet.inter (MeasurableSet.inter ?_ (hτ.measurableSet_le j)) (hπ.measurableSet_le j)
  apply measurableSet_eq_fun_of_countable
  · exact (hτ.min_const j).measurable_of_le fun _ => min_le_right _ _
  · exact (hπ.min_const j).measurable_of_le fun _ => min_le_right _ _

end LinearOrder

end IsStoppingTime

section LinearOrder

/-! ## Stopped value and stopped process -/


/-- Given a map `u : ι → Ω → E`, its stopped value with respect to the stopping
time `τ` is the map `x ↦ u (τ ω) ω`. -/
def stoppedValue (u : ι → Ω → β) (τ : Ω → ι) : Ω → β := fun ω => u (τ ω) ω

theorem stoppedValue_const (u : ι → Ω → β) (i : ι) : (stoppedValue u fun _ => i) = u i :=
  rfl

variable [LinearOrder ι]

/-- Given a map `u : ι → Ω → E`, the stopped process with respect to `τ` is `u i ω` if
`i ≤ τ ω`, and `u (τ ω) ω` otherwise.

Intuitively, the stopped process stops evolving once the stopping time has occurred. -/
def stoppedProcess (u : ι → Ω → β) (τ : Ω → ι) : ι → Ω → β := fun i ω => u (min i (τ ω)) ω

theorem stoppedProcess_eq_stoppedValue {u : ι → Ω → β} {τ : Ω → ι} :
    stoppedProcess u τ = fun i => stoppedValue u fun ω => min i (τ ω) :=
  rfl

theorem stoppedValue_stoppedProcess {u : ι → Ω → β} {τ σ : Ω → ι} :
    stoppedValue (stoppedProcess u τ) σ = stoppedValue u fun ω => min (σ ω) (τ ω) :=
  rfl

theorem stoppedProcess_eq_of_le {u : ι → Ω → β} {τ : Ω → ι} {i : ι} {ω : Ω} (h : i ≤ τ ω) :
    stoppedProcess u τ i ω = u i ω := by simp [stoppedProcess, min_eq_left h]

theorem stoppedProcess_eq_of_ge {u : ι → Ω → β} {τ : Ω → ι} {i : ι} {ω : Ω} (h : τ ω ≤ i) :
    stoppedProcess u τ i ω = u (τ ω) ω := by simp [stoppedProcess, min_eq_right h]

section ProgMeasurable

variable [MeasurableSpace ι] [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι]
  [BorelSpace ι] [TopologicalSpace β] {u : ι → Ω → β} {τ : Ω → ι} {f : Filtration ι m}

theorem progMeasurable_min_stopping_time [PseudoMetrizableSpace ι] (hτ : IsStoppingTime f τ) :
    ProgMeasurable f fun i ω => min i (τ ω) := by
  intro i
  let m_prod : MeasurableSpace (Set.Iic i × Ω) := Subtype.instMeasurableSpace.prod (f i)
  let m_set : ∀ t : Set (Set.Iic i × Ω), MeasurableSpace t := fun _ =>
    @Subtype.instMeasurableSpace (Set.Iic i × Ω) _ m_prod
  let s := {p : Set.Iic i × Ω | τ p.2 ≤ i}
  have hs : MeasurableSet[m_prod] s := @measurable_snd (Set.Iic i) Ω _ (f i) _ (hτ i)
  have h_meas_fst : ∀ t : Set (Set.Iic i × Ω),
      Measurable[m_set t] fun x : t => ((x : Set.Iic i × Ω).fst : ι) :=
    fun t => (@measurable_subtype_coe (Set.Iic i × Ω) m_prod _).fst.subtype_val
  apply Measurable.stronglyMeasurable
  refine measurable_of_restrict_of_restrict_compl hs ?_ ?_
  · refine @Measurable.min _ _ _ _ _ (m_set s) _ _ _ _ _ (h_meas_fst s) ?_
    refine @measurable_of_Iic ι s _ _ _ (m_set s) _ _ _ _ fun j => ?_
    have h_set_eq : (fun x : s => τ (x : Set.Iic i × Ω).snd) ⁻¹' Set.Iic j =
        (fun x : s => (x : Set.Iic i × Ω).snd) ⁻¹' {ω | τ ω ≤ min i j} := by
      ext1 ω
      simp only [Set.mem_preimage, Set.mem_Iic, iff_and_self, le_min_iff, Set.mem_setOf_eq]
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
      exact h_meas_fst _
    ext1 ω
    rw [min_eq_left]
    have hx_fst_le : ↑(ω : Set.Iic i × Ω).fst ≤ i := (ω : Set.Iic i × Ω).fst.prop
    refine hx_fst_le.trans (le_of_lt ?_)
    convert ω.prop
    simp only [sc, s, not_le, Set.mem_compl_iff, Set.mem_setOf_eq]

theorem ProgMeasurable.stoppedProcess [PseudoMetrizableSpace ι] (h : ProgMeasurable f u)
    (hτ : IsStoppingTime f τ) : ProgMeasurable f (stoppedProcess u τ) :=
  h.comp (progMeasurable_min_stopping_time hτ) fun _ _ => min_le_left _ _

theorem ProgMeasurable.adapted_stoppedProcess [PseudoMetrizableSpace ι] (h : ProgMeasurable f u)
    (hτ : IsStoppingTime f τ) : Adapted f (MeasureTheory.stoppedProcess u τ) :=
  (h.stoppedProcess hτ).adapted

theorem ProgMeasurable.stronglyMeasurable_stoppedProcess [PseudoMetrizableSpace ι]
    (hu : ProgMeasurable f u) (hτ : IsStoppingTime f τ) (i : ι) :
    StronglyMeasurable (MeasureTheory.stoppedProcess u τ i) :=
  (hu.adapted_stoppedProcess hτ i).mono (f.le _)

theorem stronglyMeasurable_stoppedValue_of_le (h : ProgMeasurable f u) (hτ : IsStoppingTime f τ)
    {n : ι} (hτ_le : ∀ ω, τ ω ≤ n) : StronglyMeasurable[f n] (stoppedValue u τ) := by
  have : stoppedValue u τ =
      (fun p : Set.Iic n × Ω => u (↑p.fst) p.snd) ∘ fun ω => (⟨τ ω, hτ_le ω⟩, ω) := by
    ext1 ω; simp only [stoppedValue, Function.comp_apply]
  rw [this]
  refine StronglyMeasurable.comp_measurable (h n) ?_
  exact (hτ.measurable_of_le hτ_le).subtype_mk.prodMk measurable_id

theorem measurable_stoppedValue [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
    (hf_prog : ProgMeasurable f u) (hτ : IsStoppingTime f τ) :
    Measurable[hτ.measurableSpace] (stoppedValue u τ) := by
  have h_str_meas : ∀ i, StronglyMeasurable[f i] (stoppedValue u fun ω => min (τ ω) i) := fun i =>
    stronglyMeasurable_stoppedValue_of_le hf_prog (hτ.min_const i) fun _ => min_le_right _ _
  intro t ht i
  suffices stoppedValue u τ ⁻¹' t ∩ {ω : Ω | τ ω ≤ i} =
      (stoppedValue u fun ω => min (τ ω) i) ⁻¹' t ∩ {ω : Ω | τ ω ≤ i} by
    rw [this]; exact ((h_str_meas i).measurable ht).inter (hτ.measurableSet_le i)
  ext1 ω
  simp only [stoppedValue, Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq,
    and_congr_left_iff]
  intro h
  rw [min_eq_left h]

end ProgMeasurable

end LinearOrder

section StoppedValueOfMemFinset

variable {μ : Measure Ω} {τ : Ω → ι} {E : Type*} {p : ℝ≥0∞} {u : ι → Ω → E}

theorem stoppedValue_eq_of_mem_finset [AddCommMonoid E] {s : Finset ι} (hbdd : ∀ ω, τ ω ∈ s) :
    stoppedValue u τ = ∑ i ∈ s, Set.indicator {ω | τ ω = i} (u i) := by
  ext y
  classical
  rw [stoppedValue, Finset.sum_apply, Finset.sum_indicator_eq_sum_filter]
  suffices {i ∈ s | y ∈ {ω : Ω | τ ω = i}} = ({τ y} : Finset ι) by
    rw [this, Finset.sum_singleton]
  ext1 ω
  simp only [Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_singleton]
  constructor <;> intro h
  · exact h.2.symm
  · refine ⟨?_, h.symm⟩; rw [h]; exact hbdd y

theorem stoppedValue_eq' [Preorder ι] [LocallyFiniteOrderBot ι] [AddCommMonoid E] {N : ι}
    (hbdd : ∀ ω, τ ω ≤ N) :
    stoppedValue u τ = ∑ i ∈ Finset.Iic N, Set.indicator {ω | τ ω = i} (u i) :=
  stoppedValue_eq_of_mem_finset fun ω => Finset.mem_Iic.mpr (hbdd ω)

theorem stoppedProcess_eq_of_mem_finset [LinearOrder ι] [AddCommMonoid E] {s : Finset ι} (n : ι)
    (hbdd : ∀ ω, τ ω < n → τ ω ∈ s) : stoppedProcess u τ n = Set.indicator {a | n ≤ τ a} (u n) +
      ∑ i ∈ s with i < n, Set.indicator {ω | τ ω = i} (u i) := by
  ext ω
  rw [Pi.add_apply, Finset.sum_apply]
  rcases le_or_gt n (τ ω) with h | h
  · rw [stoppedProcess_eq_of_le h, Set.indicator_of_mem, Finset.sum_eq_zero, add_zero]
    · intro m hm
      refine Set.indicator_of_notMem ?_ _
      rw [Finset.mem_filter] at hm
      exact (hm.2.trans_le h).ne'
    · exact h
  · rw [stoppedProcess_eq_of_ge (le_of_lt h), Finset.sum_eq_single_of_mem (τ ω)]
    · rw [Set.indicator_of_notMem, zero_add, Set.indicator_of_mem] <;> rw [Set.mem_setOf]
      exact not_le.2 h
    · rw [Finset.mem_filter]
      exact ⟨hbdd ω h, h⟩
    · intro b _ hneq
      rw [Set.indicator_of_notMem]
      rw [Set.mem_setOf]
      exact hneq.symm

theorem stoppedProcess_eq'' [LinearOrder ι] [LocallyFiniteOrderBot ι] [AddCommMonoid E] (n : ι) :
    stoppedProcess u τ n = Set.indicator {a | n ≤ τ a} (u n) +
      ∑ i ∈ Finset.Iio n, Set.indicator {ω | τ ω = i} (u i) := by
  have h_mem : ∀ ω, τ ω < n → τ ω ∈ Finset.Iio n := fun ω h => Finset.mem_Iio.mpr h
  rw [stoppedProcess_eq_of_mem_finset n h_mem]
  congr with i
  simp

section StoppedValue

variable [PartialOrder ι] {ℱ : Filtration ι m} [NormedAddCommGroup E]

theorem memLp_stoppedValue_of_mem_finset (hτ : IsStoppingTime ℱ τ) (hu : ∀ n, MemLp (u n) p μ)
    {s : Finset ι} (hbdd : ∀ ω, τ ω ∈ s) : MemLp (stoppedValue u τ) p μ := by
  rw [stoppedValue_eq_of_mem_finset hbdd]
  refine memLp_finset_sum' _ fun i _ => MemLp.indicator ?_ (hu i)
  refine ℱ.le i {a : Ω | τ a = i} (hτ.measurableSet_eq_of_countable_range ?_ i)
  refine ((Finset.finite_toSet s).subset fun ω hω => ?_).countable
  obtain ⟨y, rfl⟩ := hω
  exact hbdd y

theorem memLp_stoppedValue [LocallyFiniteOrderBot ι] (hτ : IsStoppingTime ℱ τ)
    (hu : ∀ n, MemLp (u n) p μ) {N : ι} (hbdd : ∀ ω, τ ω ≤ N) : MemLp (stoppedValue u τ) p μ :=
  memLp_stoppedValue_of_mem_finset hτ hu fun ω => Finset.mem_Iic.mpr (hbdd ω)

theorem integrable_stoppedValue_of_mem_finset (hτ : IsStoppingTime ℱ τ)
    (hu : ∀ n, Integrable (u n) μ) {s : Finset ι} (hbdd : ∀ ω, τ ω ∈ s) :
    Integrable (stoppedValue u τ) μ := by
  simp_rw [← memLp_one_iff_integrable] at hu ⊢
  exact memLp_stoppedValue_of_mem_finset hτ hu hbdd

variable (ι)

theorem integrable_stoppedValue [LocallyFiniteOrderBot ι] (hτ : IsStoppingTime ℱ τ)
    (hu : ∀ n, Integrable (u n) μ) {N : ι} (hbdd : ∀ ω, τ ω ≤ N) :
    Integrable (stoppedValue u τ) μ :=
  integrable_stoppedValue_of_mem_finset hτ hu fun ω => Finset.mem_Iic.mpr (hbdd ω)

end StoppedValue

section StoppedProcess

variable [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι] [FirstCountableTopology ι]
  {ℱ : Filtration ι m} [NormedAddCommGroup E]

theorem memLp_stoppedProcess_of_mem_finset (hτ : IsStoppingTime ℱ τ) (hu : ∀ n, MemLp (u n) p μ)
    (n : ι) {s : Finset ι} (hbdd : ∀ ω, τ ω < n → τ ω ∈ s) : MemLp (stoppedProcess u τ n) p μ := by
  rw [stoppedProcess_eq_of_mem_finset n hbdd]
  refine MemLp.add ?_ ?_
  · exact MemLp.indicator (ℱ.le n {a : Ω | n ≤ τ a} (hτ.measurableSet_ge n)) (hu n)
  · suffices MemLp (fun ω => ∑ i ∈ s with i < n, {a : Ω | τ a = i}.indicator (u i) ω) p μ by
      convert this using 1; ext1 ω; simp only [Finset.sum_apply]
    refine memLp_finset_sum _ fun i _ => MemLp.indicator ?_ (hu i)
    exact ℱ.le i {a : Ω | τ a = i} (hτ.measurableSet_eq i)

theorem memLp_stoppedProcess [LocallyFiniteOrderBot ι] (hτ : IsStoppingTime ℱ τ)
    (hu : ∀ n, MemLp (u n) p μ) (n : ι) : MemLp (stoppedProcess u τ n) p μ :=
  memLp_stoppedProcess_of_mem_finset hτ hu n fun _ h => Finset.mem_Iio.mpr h

theorem integrable_stoppedProcess_of_mem_finset (hτ : IsStoppingTime ℱ τ)
    (hu : ∀ n, Integrable (u n) μ) (n : ι) {s : Finset ι} (hbdd : ∀ ω, τ ω < n → τ ω ∈ s) :
    Integrable (stoppedProcess u τ n) μ := by
  simp_rw [← memLp_one_iff_integrable] at hu ⊢
  exact memLp_stoppedProcess_of_mem_finset hτ hu n hbdd

theorem integrable_stoppedProcess [LocallyFiniteOrderBot ι] (hτ : IsStoppingTime ℱ τ)
    (hu : ∀ n, Integrable (u n) μ) (n : ι) : Integrable (stoppedProcess u τ n) μ :=
  integrable_stoppedProcess_of_mem_finset hτ hu n fun _ h => Finset.mem_Iio.mpr h

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

variable {u : ℕ → Ω → β} {τ π : Ω → ℕ}

theorem stoppedValue_sub_eq_sum [AddCommGroup β] (hle : τ ≤ π) :
    stoppedValue u π - stoppedValue u τ = fun ω =>
      (∑ i ∈ Finset.Ico (τ ω) (π ω), (u (i + 1) - u i)) ω := by
  ext ω
  rw [Finset.sum_Ico_eq_sub _ (hle ω), Finset.sum_range_sub, Finset.sum_range_sub]
  simp [stoppedValue]

theorem stoppedValue_sub_eq_sum' [AddCommGroup β] (hle : τ ≤ π) {N : ℕ} (hbdd : ∀ ω, π ω ≤ N) :
    stoppedValue u π - stoppedValue u τ = fun ω =>
      (∑ i ∈ Finset.range (N + 1), Set.indicator {ω | τ ω ≤ i ∧ i < π ω} (u (i + 1) - u i)) ω := by
  rw [stoppedValue_sub_eq_sum hle]
  ext ω
  simp only [Finset.sum_apply, Finset.sum_indicator_eq_sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext i
  simp only [Finset.mem_filter, Set.mem_setOf_eq, Finset.mem_range, Finset.mem_Ico]
  exact ⟨fun h => ⟨lt_trans h.2 (Nat.lt_succ_iff.2 <| hbdd _), h⟩, fun h => h.2⟩

section AddCommMonoid

variable [AddCommMonoid β]

theorem stoppedValue_eq {N : ℕ} (hbdd : ∀ ω, τ ω ≤ N) : stoppedValue u τ = fun x =>
    (∑ i ∈ Finset.range (N + 1), Set.indicator {ω | τ ω = i} (u i)) x :=
  stoppedValue_eq_of_mem_finset fun ω => Finset.mem_range_succ_iff.mpr (hbdd ω)

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
    · simp_rw [@eq_comm _ _ n, @le_iff_eq_or_lt _ _ n, Nat.succ_le_iff, Set.setOf_or]
    · rintro ⟨h₁, h₂⟩
      rw [Set.mem_setOf] at h₁ h₂
      exact (Nat.succ_le_iff.1 h₂).ne h₁.symm
  rw [stoppedProcess_eq, this, Finset.sum_range_succ_comm, ← add_assoc]

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
  have : {ω | s.piecewise τ η ω ≤ n} = s ∩ {ω | τ ω ≤ n} ∪ sᶜ ∩ {ω | η ω ≤ n} := by
    ext1 ω
    simp only [Set.piecewise, Set.mem_setOf_eq]
    by_cases hx : ω ∈ s <;> simp [hx]
  rw [this]
  by_cases hin : i ≤ n
  · have hs_n : MeasurableSet[𝒢 n] s := 𝒢.mono hin _ hs
    exact (hs_n.inter (hτ_st n)).union (hs_n.compl.inter (hη_st n))
  · have hτn : ∀ ω, ¬τ ω ≤ n := fun ω hτn => hin ((hτ ω).trans hτn)
    have hηn : ∀ ω, ¬η ω ≤ n := fun ω hηn => hin ((hη ω).trans hηn)
    simp [hτn, hηn, @MeasurableSet.empty _ _]

theorem isStoppingTime_piecewise_const (hij : i ≤ j) (hs : MeasurableSet[𝒢 i] s) :
    IsStoppingTime 𝒢 (s.piecewise (fun _ => i) fun _ => j) :=
  (isStoppingTime_const 𝒢 i).piecewise_of_le (isStoppingTime_const 𝒢 j) (fun _ => le_rfl)
    (fun _ => hij) hs

theorem stoppedValue_piecewise_const {ι' : Type*} {i j : ι'} {f : ι' → Ω → ℝ} :
    stoppedValue f (s.piecewise (fun _ => i) fun _ => j) = s.piecewise (f i) (f j) := by
  ext ω; rw [stoppedValue]; by_cases hx : ω ∈ s <;> simp [hx]

theorem stoppedValue_piecewise_const' {ι' : Type*} {i j : ι'} {f : ι' → Ω → ℝ} :
    stoppedValue f (s.piecewise (fun _ => i) fun _ => j) =
    s.indicator (f i) + sᶜ.indicator (f j) := by
  ext ω; rw [stoppedValue]; by_cases hx : ω ∈ s <;> simp [hx]

end PiecewiseConst

section Condexp

/-! ### Conditional expectation with respect to the σ-algebra generated by a stopping time -/


variable [LinearOrder ι] {μ : Measure Ω} {ℱ : Filtration ι m} {τ σ : Ω → ι} {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f : Ω → E}

theorem condExp_stopping_time_ae_eq_restrict_eq_of_countable_range [SigmaFiniteFiltration μ ℱ]
    (hτ : IsStoppingTime ℱ τ) (h_countable : (Set.range τ).Countable)
    [SigmaFinite (μ.trim (hτ.measurableSpace_le_of_countable_range h_countable))] (i : ι) :
    μ[f|hτ.measurableSpace] =ᵐ[μ.restrict {x | τ x = i}] μ[f|ℱ i] := by
  refine condExp_ae_eq_restrict_of_measurableSpace_eq_on
    (hτ.measurableSpace_le_of_countable_range h_countable) (ℱ.le i)
    (hτ.measurableSet_eq_of_countable_range' h_countable i) fun t => ?_
  rw [Set.inter_comm _ t, IsStoppingTime.measurableSet_inter_eq_iff]

theorem condExp_stopping_time_ae_eq_restrict_eq_of_countable [Countable ι]
    [SigmaFiniteFiltration μ ℱ] (hτ : IsStoppingTime ℱ τ)
    [SigmaFinite (μ.trim hτ.measurableSpace_le_of_countable)] (i : ι) :
    μ[f|hτ.measurableSpace] =ᵐ[μ.restrict {x | τ x = i}] μ[f|ℱ i] :=
  condExp_stopping_time_ae_eq_restrict_eq_of_countable_range hτ (Set.to_countable _) i

variable [(Filter.atTop : Filter ι).IsCountablyGenerated]

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

theorem condExp_min_stopping_time_ae_eq_restrict_le [MeasurableSpace ι] [SecondCountableTopology ι]
    [BorelSpace ι] (hτ : IsStoppingTime ℱ τ) (hσ : IsStoppingTime ℱ σ)
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
