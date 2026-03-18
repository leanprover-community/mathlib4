/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Classes for s-finite measures

We introduce the following typeclasses for measures:

* `SFinite μ`: the measure `μ` can be written as a countable sum of finite measures;
* `SigmaFinite μ`: there exists a countable collection of sets that cover `univ`
  where `μ` is finite.
-/

@[expose] public section

namespace MeasureTheory

open Set Filter Function Measure MeasurableSpace NNReal ENNReal
open scoped Topology

variable {α β ι : Type*} {m0 : MeasurableSpace α} [MeasurableSpace β] {μ ν : Measure α}
  {s t : Set α} {a : α}

section SFinite

/-- A measure is called s-finite if it is a countable sum of finite measures. -/
class SFinite (μ : Measure α) : Prop where
  out' : ∃ m : ℕ → Measure α, (∀ n, IsFiniteMeasure (m n)) ∧ μ = Measure.sum m

/-- A sequence of finite measures such that `μ = sum (sfiniteSeq μ)` (see `sum_sfiniteSeq`). -/
noncomputable def sfiniteSeq (μ : Measure α) [h : SFinite μ] : ℕ → Measure α := h.1.choose

instance isFiniteMeasure_sfiniteSeq [h : SFinite μ] (n : ℕ) : IsFiniteMeasure (sfiniteSeq μ n) :=
  h.1.choose_spec.1 n

lemma sum_sfiniteSeq (μ : Measure α) [h : SFinite μ] : sum (sfiniteSeq μ) = μ :=
  h.1.choose_spec.2.symm

lemma sfiniteSeq_le (μ : Measure α) [SFinite μ] (n : ℕ) : sfiniteSeq μ n ≤ μ :=
  (le_sum _ n).trans (sum_sfiniteSeq μ).le

instance : SFinite (0 : Measure α) := ⟨fun _ ↦ 0, inferInstance, by rw [Measure.sum_zero]⟩

@[simp]
lemma sfiniteSeq_zero (n : ℕ) : sfiniteSeq (0 : Measure α) n = 0 :=
  bot_unique <| sfiniteSeq_le _ _

/-- A countable sum of finite measures is s-finite.
This lemma is superseded by the instance below. -/
lemma sfinite_sum_of_countable [Countable ι]
    (m : ι → Measure α) [∀ n, IsFiniteMeasure (m n)] : SFinite (Measure.sum m) := by
  classical
  obtain ⟨f, hf⟩ : ∃ f : ι → ℕ, Function.Injective f := Countable.exists_injective_nat ι
  refine ⟨_, fun n ↦ ?_, (sum_extend_zero hf m).symm⟩
  rcases em (n ∈ range f) with ⟨i, rfl⟩ | hn
  · rw [hf.extend_apply]
    infer_instance
  · rw [Function.extend_apply' _ _ _ hn, Pi.zero_apply]
    infer_instance

instance [Countable ι] (m : ι → Measure α) [∀ n, SFinite (m n)] : SFinite (Measure.sum m) := by
  change SFinite (Measure.sum (fun i ↦ m i))
  simp_rw [← sum_sfiniteSeq (m _), Measure.sum_sum]
  apply sfinite_sum_of_countable

instance [SFinite μ] [SFinite ν] : SFinite (μ + ν) := by
  have : ∀ b : Bool, SFinite (cond b μ ν) := by simp [*]
  simpa using inferInstanceAs (SFinite (.sum (cond · μ ν)))

instance [SFinite μ] (s : Set α) : SFinite (μ.restrict s) :=
  ⟨fun n ↦ (sfiniteSeq μ n).restrict s, fun n ↦ inferInstance,
    by rw [← restrict_sum_of_countable, sum_sfiniteSeq]⟩

variable (μ) in
/-- For an s-finite measure `μ`, there exists a finite measure `ν`
such that each of `μ` and `ν` is absolutely continuous with respect to the other.
-/
theorem exists_isFiniteMeasure_absolutelyContinuous [SFinite μ] :
    ∃ ν : Measure α, IsFiniteMeasure ν ∧ μ ≪ ν ∧ ν ≪ μ := by
  rcases ENNReal.exists_pos_tsum_mul_lt_of_countable top_ne_zero (sfiniteSeq μ · univ)
    fun _ ↦ measure_ne_top _ _ with ⟨c, hc₀, hc⟩
  have {s : Set α} : sum (fun n ↦ c n • sfiniteSeq μ n) s = 0 ↔ μ s = 0 := by
    conv_rhs => rw [← sum_sfiniteSeq μ, sum_apply_of_countable]
    simp [(hc₀ _).ne']
  refine ⟨.sum fun n ↦ c n • sfiniteSeq μ n, ⟨?_⟩, fun _ ↦ this.1, fun _ ↦ this.2⟩
  simpa [mul_comm] using hc

end SFinite

/-- A measure `μ` is called σ-finite if there is a countable collection of sets
`{ A i | i ∈ ℕ }` such that `μ (A i) < ∞` and `⋃ i, A i = s`. -/
class SigmaFinite {m0 : MeasurableSpace α} (μ : Measure α) : Prop where
  out' : Nonempty (μ.FiniteSpanningSetsIn univ)

theorem sigmaFinite_iff : SigmaFinite μ ↔ Nonempty (μ.FiniteSpanningSetsIn univ) :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

theorem SigmaFinite.out (h : SigmaFinite μ) : Nonempty (μ.FiniteSpanningSetsIn univ) :=
  h.1

/-- If `μ` is σ-finite it has finite spanning sets in the collection of all measurable sets. -/
def Measure.toFiniteSpanningSetsIn (μ : Measure α) [h : SigmaFinite μ] :
    μ.FiniteSpanningSetsIn { s | MeasurableSet s } where
  set n := toMeasurable μ (h.out.some.set n)
  set_mem _ := measurableSet_toMeasurable _ _
  finite n := by
    rw [measure_toMeasurable]
    exact h.out.some.finite n
  spanning := eq_univ_of_subset (iUnion_mono fun _ => subset_toMeasurable _ _) h.out.some.spanning

/-- A noncomputable way to get a monotone collection of sets that span `univ` and have finite
  measure using `Classical.choose`. This definition satisfies monotonicity in addition to all other
  properties in `SigmaFinite`. -/
def spanningSets (μ : Measure α) [SigmaFinite μ] (i : ℕ) : Set α :=
  accumulate μ.toFiniteSpanningSetsIn.set i

theorem monotone_spanningSets (μ : Measure α) [SigmaFinite μ] : Monotone (spanningSets μ) :=
  monotone_accumulate

@[gcongr]
lemma spanningSets_mono [SigmaFinite μ] {m n : ℕ} (hmn : m ≤ n) :
    spanningSets μ m ⊆ spanningSets μ n := monotone_spanningSets _ hmn

theorem measurableSet_spanningSets (μ : Measure α) [SigmaFinite μ] (i : ℕ) :
    MeasurableSet (spanningSets μ i) :=
  MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ => μ.toFiniteSpanningSetsIn.set_mem j

theorem measure_spanningSets_lt_top (μ : Measure α) [SigmaFinite μ] (i : ℕ) :
    μ (spanningSets μ i) < ∞ :=
  measure_biUnion_lt_top (finite_le_nat i) fun j _ => μ.toFiniteSpanningSetsIn.finite j

@[simp]
theorem iUnion_spanningSets (μ : Measure α) [SigmaFinite μ] : ⋃ i : ℕ, spanningSets μ i = univ := by
  simp_rw [spanningSets, iUnion_accumulate, μ.toFiniteSpanningSetsIn.spanning]

theorem isCountablySpanning_spanningSets (μ : Measure α) [SigmaFinite μ] :
    IsCountablySpanning (range (spanningSets μ)) :=
  ⟨spanningSets μ, mem_range_self, iUnion_spanningSets μ⟩

open scoped Classical in
/-- `spanningSetsIndex μ x` is the least `n : ℕ` such that `x ∈ spanningSets μ n`. -/
noncomputable def spanningSetsIndex (μ : Measure α) [SigmaFinite μ] (x : α) : ℕ :=
  Nat.find <| iUnion_eq_univ_iff.1 (iUnion_spanningSets μ) x

open scoped Classical in
theorem measurableSet_spanningSetsIndex (μ : Measure α) [SigmaFinite μ] :
    Measurable (spanningSetsIndex μ) :=
  measurable_find _ <| measurableSet_spanningSets μ

open scoped Classical in
theorem preimage_spanningSetsIndex_singleton (μ : Measure α) [SigmaFinite μ] (n : ℕ) :
    spanningSetsIndex μ ⁻¹' {n} = disjointed (spanningSets μ) n :=
  preimage_find_eq_disjointed _ _ _

theorem spanningSetsIndex_eq_iff (μ : Measure α) [SigmaFinite μ] {x : α} {n : ℕ} :
    spanningSetsIndex μ x = n ↔ x ∈ disjointed (spanningSets μ) n := by
  convert Set.ext_iff.1 (preimage_spanningSetsIndex_singleton μ n) x

theorem mem_disjointed_spanningSetsIndex (μ : Measure α) [SigmaFinite μ] (x : α) :
    x ∈ disjointed (spanningSets μ) (spanningSetsIndex μ x) :=
  (spanningSetsIndex_eq_iff μ).1 rfl

theorem mem_spanningSetsIndex (μ : Measure α) [SigmaFinite μ] (x : α) :
    x ∈ spanningSets μ (spanningSetsIndex μ x) :=
  disjointed_subset _ _ (mem_disjointed_spanningSetsIndex μ x)

theorem mem_spanningSets_of_index_le (μ : Measure α) [SigmaFinite μ] (x : α) {n : ℕ}
    (hn : spanningSetsIndex μ x ≤ n) : x ∈ spanningSets μ n :=
  monotone_spanningSets μ hn (mem_spanningSetsIndex μ x)

theorem eventually_mem_spanningSets (μ : Measure α) [SigmaFinite μ] (x : α) :
    ∀ᶠ n in atTop, x ∈ spanningSets μ n :=
  eventually_atTop.2 ⟨spanningSetsIndex μ x, fun _ => mem_spanningSets_of_index_le μ x⟩

lemma measure_singleton_lt_top [SigmaFinite μ] : μ {a} < ∞ :=
  measure_lt_top_mono (singleton_subset_iff.2 <| mem_spanningSetsIndex ..)
    (measure_spanningSets_lt_top _ _)

theorem sum_restrict_disjointed_spanningSets (μ ν : Measure α) [SigmaFinite ν] :
    sum (fun n ↦ μ.restrict (disjointed (spanningSets ν) n)) = μ := by
  rw [← restrict_iUnion (disjoint_disjointed _)
      (MeasurableSet.disjointed (measurableSet_spanningSets _)),
    iUnion_disjointed, iUnion_spanningSets, restrict_univ]

instance (priority := 100) [SigmaFinite μ] : SFinite μ := by
  have : ∀ n, Fact (μ (disjointed (spanningSets μ) n) < ∞) :=
    fun n ↦ ⟨(measure_mono (disjointed_subset _ _)).trans_lt (measure_spanningSets_lt_top μ n)⟩
  exact ⟨⟨fun n ↦ μ.restrict (disjointed (spanningSets μ) n), fun n ↦ by infer_instance,
    (sum_restrict_disjointed_spanningSets μ μ).symm⟩⟩

namespace Measure

/-- A set in a σ-finite space has zero measure if and only if its intersection with
all members of the countable family of finite measure spanning sets has zero measure. -/
theorem forall_measure_inter_spanningSets_eq_zero [MeasurableSpace α] {μ : Measure α}
    [SigmaFinite μ] (s : Set α) : (∀ n, μ (s ∩ spanningSets μ n) = 0) ↔ μ s = 0 := by
  nth_rw 2 [show s = ⋃ n, s ∩ spanningSets μ n by
      rw [← inter_iUnion, iUnion_spanningSets, inter_univ]]
  rw [measure_iUnion_null_iff]

/-- A set in a σ-finite space has positive measure if and only if its intersection with
some member of the countable family of finite measure spanning sets has positive measure. -/
theorem exists_measure_inter_spanningSets_pos [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
    (s : Set α) : (∃ n, 0 < μ (s ∩ spanningSets μ n)) ↔ 0 < μ s := by
  contrapose!
  simp only [nonpos_iff_eq_zero]
  exact forall_measure_inter_spanningSets_eq_zero s

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
      iUnion_Ici_eq_Ioi_of_lt_of_tendsto (fun n => (as_mem n).1) as_lim]
  rw [countable_union]
  refine countable_iUnion fun n => Finite.countable ?_
  exact finite_const_le_meas_of_disjoint_iUnion₀ μ (as_mem n).1 As_mble As_disj Union_As_finite

/-- If the union of disjoint measurable sets has finite measure, then there are only
countably many members of the union whose measure is positive. -/
theorem countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top {ι : Type*} {_ : MeasurableSpace α}
    (μ : Measure α) {As : ι → Set α} (As_mble : ∀ i : ι, MeasurableSet (As i))
    (As_disj : Pairwise (Disjoint on As)) (Union_As_finite : μ (⋃ i, As i) ≠ ∞) :
    Set.Countable { i : ι | 0 < μ (As i) } :=
  countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top₀ μ (fun i ↦ (As_mble i).nullMeasurableSet)
    ((fun _ _ h ↦ Disjoint.aedisjoint (As_disj h))) Union_As_finite

/-- In an s-finite space, among disjoint null-measurable sets, only countably many can have positive
measure. -/
theorem countable_meas_pos_of_disjoint_iUnion₀ {ι : Type*} {_ : MeasurableSpace α} {μ : Measure α}
    [SFinite μ] {As : ι → Set α} (As_mble : ∀ i : ι, NullMeasurableSet (As i) μ)
    (As_disj : Pairwise (AEDisjoint μ on As)) :
    Set.Countable { i : ι | 0 < μ (As i) } := by
  rw [← sum_sfiniteSeq μ] at As_disj As_mble ⊢
  have obs : { i : ι | 0 < sum (sfiniteSeq μ) (As i) }
      ⊆ ⋃ n, { i : ι | 0 < sfiniteSeq μ n (As i) } := by
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

private lemma exists_ae_subset_biUnion_countable_of_isFiniteMeasure [IsFiniteMeasure μ]
    {C : Set (Set α)} (hC : ∀ s ∈ C, MeasurableSet s) :
    ∃ D ⊆ C, D.Countable ∧ ∀ s ∈ C, s ≤ᵐ[μ] (⋃₀ D) := by
  let m := ⨆ D ∈ {D : Set (Set α) | D ⊆ C ∧ D.Countable}, μ (⋃₀ D)
  obtain ⟨D, D_mem, hD⟩ : ∃ D ∈ {D : Set (Set α) | D ⊆ C ∧ D.Countable}, μ (⋃₀ D) = m := by
    rcases eq_bot_or_bot_lt m with hm | hm
    · exact ⟨∅, by simp, by simp [hm]⟩
    obtain ⟨u, -, u_mem, u_lim⟩ :
        ∃ u : ℕ → ℝ≥0∞, StrictMono u ∧ (∀ n, u n ∈ Ioo 0 m) ∧ Tendsto u atTop (𝓝 m) :=
      exists_seq_strictMono_tendsto' hm
    have A n : ∃ D ∈ {D : Set (Set α) | D ⊆ C ∧ D.Countable}, u n < μ (⋃₀ D) :=
      lt_biSup_iff.1 (u_mem n).2
    choose! D D_mem huD using A
    have hD : ⋃ n, D n ∈ {D | D ⊆ C ∧ D.Countable} := by simp; grind
    refine ⟨⋃ n, D n, hD, ?_⟩
    apply le_antisymm (le_biSup (f := fun D ↦ μ (⋃₀ D)) hD)
    apply le_of_tendsto' u_lim (fun n ↦ (huD n).le.trans ?_)
    exact measure_mono (fun x hx ↦ by simp at hx ⊢; grind)
  refine ⟨D, by grind, by grind, fun s hs ↦ union_ae_eq_right_iff_ae_subset.mp ?_⟩
  symm
  apply ae_eq_of_ae_subset_of_measure_ge subset_union_right.eventuallyLE
  · rw [hD, show s ∪ ⋃₀ D = ⋃₀ (D ∪ {s}) by simp]
    apply le_biSup (f := fun D ↦ μ (⋃₀ D))
    simp [D_mem.2, insert_subset_iff, hs, D_mem.1]
  · exact (MeasurableSet.sUnion D_mem.2 (by grind)).nullMeasurableSet
  · simp

variable (μ) in
/-- Given a family of measurable sets, its measurable union is its union modulo sets of measure
zero. It is well defined up to measure 0. For instance, the measurable union of all the singleton
sets in `ℝ` is empty (while the usual union would be the whole space).
This lemma shows the existence of a measurable union, writing it as the union of a countable
subfamily. -/
lemma exists_ae_subset_biUnion_countable [SFinite μ]
    {C : Set (Set α)} (hC : ∀ s ∈ C, MeasurableSet s) :
    ∃ D ⊆ C, D.Countable ∧ ∀ s ∈ C, s ≤ᵐ[μ] (⋃₀ D) := by
  have A n : ∃ D ⊆ C, D.Countable ∧ ∀ s ∈ C, s ≤ᵐ[sfiniteSeq μ n] (⋃₀ D) :=
    exists_ae_subset_biUnion_countable_of_isFiniteMeasure hC
  choose D DC D_count hD using A
  refine ⟨⋃ n, D n, by simp [DC], by simp [D_count], fun s hs ↦ ?_⟩
  rw [← sum_sfiniteSeq μ]
  apply ae_sum_iff.2 (fun n ↦ (hD n s hs).trans ?_)
  exact HasSubset.Subset.eventuallyLE (fun x hx ↦ by simp at hx ⊢; grind)

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
    refine le_antisymm ?_ (by gcongr)
    rw [hμ, sum_apply _ (M.inter hu)]
    apply le_trans _ (le_sum_apply _ _)
    apply ENNReal.tsum_le_tsum (fun i ↦ ?_)
    calc
    m i ((⋂ n, w n) ∩ u) ≤ m i (w i ∩ u) := by gcongr; apply iInter_subset
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
          refine mem_iUnion.2 ⟨n, ?_⟩
          have : x ∈ t ∩ v n := ⟨hx, hn⟩
          exact ⟨hx, subset_toMeasurable μ _ this⟩
        _ ⊆ ⋃ n, toMeasurable μ (t ∩ disjointed w n) :=
          iUnion_mono fun n => subset_toMeasurable _ _
    refine ⟨t', tt', MeasurableSet.iUnion fun n => measurableSet_toMeasurable μ _, fun u hu => ?_⟩
    apply le_antisymm _ (by gcongr)
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
          μ (t ∩ disjointed w n) ≤ μ (t ∩ w n) := by
            gcongr
            exact disjointed_le w n
          _ ≤ μ (w n) := measure_mono inter_subset_right
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
      _ ≤ μ.restrict (t ∩ u) univ := measure_mono (subset_univ _)
      _ = μ (t ∩ u) := by rw [restrict_apply MeasurableSet.univ, univ_inter]
  -- thanks to the definition of `toMeasurable`, the previous property will also be shared
  -- by `toMeasurable μ t`, which is enough to conclude the proof.
  rw [toMeasurable]
  split_ifs with ht
  · apply measure_congr
    exact ae_eq_set_inter ht.choose_spec.2.2 (ae_eq_refl _)
  · exact A.choose_spec.2.2 s hs

theorem restrict_toMeasurable_of_cover {s : Set α} {v : ℕ → Set α} (hv : s ⊆ ⋃ n, v n)
    (h'v : ∀ n, μ (s ∩ v n) ≠ ∞) : μ.restrict (toMeasurable μ s) = μ.restrict s :=
  ext fun t ht => by
    simp only [restrict_apply ht, inter_comm t, measure_toMeasurable_inter_of_cover ht hv h'v]

/-- The measurable superset `toMeasurable μ t` of `t` (which has the same measure as `t`)
satisfies, for any measurable set `s`, the equality `μ (toMeasurable μ t ∩ s) = μ (t ∩ s)`.
This only holds when `μ` is s-finite -- for example for σ-finite measures. For a version without
this assumption (but requiring that `t` has finite measure), see `measure_toMeasurable_inter`. -/
theorem measure_toMeasurable_inter_of_sFinite [SFinite μ] {s : Set α} (hs : MeasurableSet s)
    (t : Set α) : μ (toMeasurable μ t ∩ s) = μ (t ∩ s) :=
  measure_toMeasurable_inter_of_sum hs (fun _ ↦ measure_ne_top _ t) (sum_sfiniteSeq μ).symm

@[simp]
theorem restrict_toMeasurable_of_sFinite [SFinite μ] (s : Set α) :
    μ.restrict (toMeasurable μ s) = μ.restrict s :=
  ext fun t ht => by
    rw [restrict_apply ht, inter_comm t, measure_toMeasurable_inter_of_sFinite ht,
      restrict_apply ht, inter_comm t]

/-- Auxiliary lemma for `iSup_restrict_spanningSets`. -/
theorem iSup_restrict_spanningSets_of_measurableSet [SigmaFinite μ] (hs : MeasurableSet s) :
    ⨆ i, μ.restrict (spanningSets μ i) s = μ s :=
  calc
    ⨆ i, μ.restrict (spanningSets μ i) s = μ.restrict (⋃ i, spanningSets μ i) s :=
      (restrict_iUnion_apply_eq_iSup (monotone_spanningSets μ).directed_le hs).symm
    _ = μ s := by rw [iUnion_spanningSets, restrict_univ]

theorem iSup_restrict_spanningSets [SigmaFinite μ] (s : Set α) :
    ⨆ i, μ.restrict (spanningSets μ i) s = μ s := by
  rw [← measure_toMeasurable s,
    ← iSup_restrict_spanningSets_of_measurableSet (measurableSet_toMeasurable _ _)]
  simp_rw [restrict_apply' (measurableSet_spanningSets μ _), Set.inter_comm s,
    ← restrict_apply (measurableSet_spanningSets μ _), ← restrict_toMeasurable_of_sFinite s,
    restrict_apply (measurableSet_spanningSets μ _), Set.inter_comm _ (toMeasurable μ s)]

/-- In a σ-finite space, any measurable set of measure `> r` contains a measurable subset of
finite measure `> r`. -/
theorem exists_subset_measure_lt_top [SigmaFinite μ] {r : ℝ≥0∞} (hs : MeasurableSet s)
    (h's : r < μ s) : ∃ t, MeasurableSet t ∧ t ⊆ s ∧ r < μ t ∧ μ t < ∞ := by
  rw [← iSup_restrict_spanningSets,
    @lt_iSup_iff _ _ _ r fun i : ℕ => μ.restrict (spanningSets μ i) s] at h's
  rcases h's with ⟨n, hn⟩
  simp only [restrict_apply hs] at hn
  refine
    ⟨s ∩ spanningSets μ n, hs.inter (measurableSet_spanningSets _ _), inter_subset_left, hn, ?_⟩
  exact (measure_mono inter_subset_right).trans_lt (measure_spanningSets_lt_top _ _)

namespace FiniteSpanningSetsIn

variable {C D : Set (Set α)}

/-- If `μ` has finite spanning sets in `C` and `C ∩ {s | μ s < ∞} ⊆ D` then `μ` has finite spanning
sets in `D`. -/
protected def mono' (h : μ.FiniteSpanningSetsIn C) (hC : C ∩ { s | μ s < ∞ } ⊆ D) :
    μ.FiniteSpanningSetsIn D :=
  ⟨h.set, fun i => hC ⟨h.set_mem i, h.finite i⟩, h.finite, h.spanning⟩

/-- If `μ` has finite spanning sets in `C` and `C ⊆ D` then `μ` has finite spanning sets in `D`. -/
protected def mono (h : μ.FiniteSpanningSetsIn C) (hC : C ⊆ D) : μ.FiniteSpanningSetsIn D :=
  h.mono' fun _s hs => hC hs.1

/-- If `μ` has finite spanning sets in the collection of measurable sets `C`, then `μ` is σ-finite.
-/
protected theorem sigmaFinite (h : μ.FiniteSpanningSetsIn C) : SigmaFinite μ :=
  ⟨⟨h.mono <| subset_univ C⟩⟩

/-- An extensionality for measures. It is `ext_of_generateFrom_of_iUnion` formulated in terms of
`FiniteSpanningSetsIn`. -/
protected theorem ext {ν : Measure α} {C : Set (Set α)} (hA : ‹_› = generateFrom C)
    (hC : IsPiSystem C) (h : μ.FiniteSpanningSetsIn C) (h_eq : ∀ s ∈ C, μ s = ν s) : μ = ν :=
  ext_of_generateFrom_of_iUnion C _ hA hC h.spanning h.set_mem (fun i => (h.finite i).ne) h_eq

protected theorem isCountablySpanning (h : μ.FiniteSpanningSetsIn C) : IsCountablySpanning C :=
  ⟨h.set, h.set_mem, h.spanning⟩

end FiniteSpanningSetsIn

theorem sigmaFinite_of_countable {S : Set (Set α)} (hc : S.Countable) (hμ : ∀ s ∈ S, μ s < ∞)
    (hU : ⋃₀ S = univ) : SigmaFinite μ := by
  obtain ⟨s, hμ, hs⟩ : ∃ s : ℕ → Set α, (∀ n, μ (s n) < ∞) ∧ ⋃ n, s n = univ :=
    (@exists_seq_cover_iff_countable _ (fun x => μ x < ∞) ⟨∅, by simp⟩).2 ⟨S, hc, hμ, hU⟩
  exact ⟨⟨⟨fun n => s n, fun _ => trivial, hμ, hs⟩⟩⟩

/-- Given measures `μ`, `ν` where `ν ≤ μ`, `FiniteSpanningSetsIn.ofLe` provides the induced
`FiniteSpanningSet` with respect to `ν` from a `FiniteSpanningSet` with respect to `μ`. -/
def FiniteSpanningSetsIn.ofLE (h : ν ≤ μ) {C : Set (Set α)} (S : μ.FiniteSpanningSetsIn C) :
    ν.FiniteSpanningSetsIn C where
  set := S.set
  set_mem := S.set_mem
  finite n := lt_of_le_of_lt (le_iff'.1 h _) (S.finite n)
  spanning := S.spanning

theorem sigmaFinite_of_le (μ : Measure α) [hs : SigmaFinite μ] (h : ν ≤ μ) : SigmaFinite ν :=
  ⟨hs.out.map <| FiniteSpanningSetsIn.ofLE h⟩

@[simp] lemma add_right_inj (μ ν₁ ν₂ : Measure α) [SigmaFinite μ] :
    μ + ν₁ = μ + ν₂ ↔ ν₁ = ν₂ := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]⟩
  rw [ext_iff_of_iUnion_eq_univ (iUnion_spanningSets μ)]
  intro i
  ext s hs
  rw [← ENNReal.add_right_inj (measure_mono s.inter_subset_right |>.trans_lt <|
    measure_spanningSets_lt_top μ i).ne]
  simp only [ext_iff', coe_add, Pi.add_apply] at h
  simp [hs, h]

@[simp] lemma add_left_inj (μ ν₁ ν₂ : Measure α) [SigmaFinite μ] :
    ν₁ + μ = ν₂ + μ ↔ ν₁ = ν₂ := by rw [add_comm _ μ, add_comm _ μ, μ.add_right_inj]

end Measure

/-- Every finite measure is σ-finite. -/
instance (priority := 100) IsFiniteMeasure.toSigmaFinite {_m0 : MeasurableSpace α} (μ : Measure α)
    [IsFiniteMeasure μ] : SigmaFinite μ :=
  ⟨⟨⟨fun _ => univ, fun _ => trivial, fun _ => measure_lt_top μ _, iUnion_const _⟩⟩⟩

/-- A measure on a countable space is sigma-finite iff it gives finite mass to every singleton.

See `measure_singleton_lt_top` for the forward direction without the countability assumption. -/
lemma Measure.sigmaFinite_iff_measure_singleton_lt_top [Countable α] :
    SigmaFinite μ ↔ ∀ a, μ {a} < ∞ where
  mp _ a := measure_singleton_lt_top
  mpr hμ := by
    cases isEmpty_or_nonempty α
    · rw [Subsingleton.elim μ 0]
      infer_instance
    · obtain ⟨f, hf⟩ := exists_surjective_nat α
      exact ⟨⟨⟨fun n ↦ {f n}, by simp, by simpa [hf.forall] using hμ, by simp [hf.range_eq]⟩⟩⟩

theorem sigmaFinite_bot_iff (μ : @Measure α ⊥) : SigmaFinite μ ↔ IsFiniteMeasure μ := by
  refine ⟨fun h => ⟨?_⟩, fun h => by infer_instance⟩
  haveI : SigmaFinite μ := h
  let s := spanningSets μ
  have hs_univ : ⋃ i, s i = Set.univ := iUnion_spanningSets μ
  have hs_meas : ∀ i, MeasurableSet[⊥] (s i) := measurableSet_spanningSets μ
  simp_rw [MeasurableSpace.measurableSet_bot_iff] at hs_meas
  by_cases h_univ_empty : (Set.univ : Set α) = ∅
  · rw [h_univ_empty, measure_empty]
    exact ENNReal.zero_ne_top.lt_top
  obtain ⟨i, hsi⟩ : ∃ i, s i = Set.univ := by
    by_contra! h_not_univ
    have h_empty : ∀ i, s i = ∅ := by simpa [h_not_univ] using hs_meas
    simp only [h_empty, iUnion_empty] at hs_univ
    exact h_univ_empty hs_univ.symm
  rw [← hsi]
  exact measure_spanningSets_lt_top μ i

instance Restrict.sigmaFinite (μ : Measure α) [SigmaFinite μ] (s : Set α) :
    SigmaFinite (μ.restrict s) := by
  refine ⟨⟨⟨spanningSets μ, fun _ => trivial, fun i => ?_, iUnion_spanningSets μ⟩⟩⟩
  rw [Measure.restrict_apply (measurableSet_spanningSets μ i)]
  exact (measure_mono inter_subset_left).trans_lt (measure_spanningSets_lt_top μ i)

instance sum.sigmaFinite {ι} [Finite ι] (μ : ι → Measure α) [∀ i, SigmaFinite (μ i)] :
    SigmaFinite (sum μ) := by
  cases nonempty_fintype ι
  have : ∀ n, MeasurableSet (⋂ i : ι, spanningSets (μ i) n) := fun n =>
    MeasurableSet.iInter fun i => measurableSet_spanningSets (μ i) n
  refine ⟨⟨⟨fun n => ⋂ i, spanningSets (μ i) n, fun _ => trivial, fun n => ?_, ?_⟩⟩⟩
  · rw [sum_apply _ (this n), tsum_fintype, ENNReal.sum_lt_top]
    rintro i -
    exact (measure_mono <| iInter_subset _ i).trans_lt (measure_spanningSets_lt_top (μ i) n)
  · rw [iUnion_iInter_of_monotone]
    · simp_rw [iUnion_spanningSets, iInter_univ]
    exact fun i => monotone_spanningSets (μ i)

instance Add.sigmaFinite (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    SigmaFinite (μ + ν) := by
  rw [← sum_cond]
  refine @sum.sigmaFinite _ _ _ _ _ (Bool.rec ?_ ?_) <;> simpa

instance SMul.sigmaFinite {μ : Measure α} [SigmaFinite μ] (c : ℝ≥0) :
    MeasureTheory.SigmaFinite (c • μ) where
  out' :=
  ⟨{  set := spanningSets μ
      set_mem := fun _ ↦ trivial
      finite := by
        intro i
        simp only [Measure.coe_smul, Pi.smul_apply, nnreal_smul_coe_apply]
        exact ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_spanningSets_lt_top μ i)
      spanning := iUnion_spanningSets μ }⟩

instance [SigmaFinite (μ.restrict s)] [SigmaFinite (μ.restrict t)] :
    SigmaFinite (μ.restrict (s ∪ t)) := sigmaFinite_of_le _ (restrict_union_le _ _)

instance [SigmaFinite (μ.restrict s)] : SigmaFinite (μ.restrict (s ∩ t)) :=
  sigmaFinite_of_le (μ.restrict s) (restrict_mono_ae (ae_of_all _ Set.inter_subset_left))

instance [SigmaFinite (μ.restrict t)] : SigmaFinite (μ.restrict (s ∩ t)) :=
  sigmaFinite_of_le (μ.restrict t) (restrict_mono_ae (ae_of_all _ Set.inter_subset_right))

theorem SigmaFinite.of_map (μ : Measure α) {f : α → β} (hf : AEMeasurable f μ)
    (h : SigmaFinite (μ.map f)) : SigmaFinite μ :=
  ⟨⟨⟨fun n => f ⁻¹' spanningSets (μ.map f) n, fun _ => trivial, fun n => by
        simp only [← map_apply_of_aemeasurable hf, measurableSet_spanningSets,
          measure_spanningSets_lt_top],
        by rw [← preimage_iUnion, iUnion_spanningSets, preimage_univ]⟩⟩⟩

lemma _root_.MeasurableEmbedding.sigmaFinite_map {f : α → β} (hf : MeasurableEmbedding f)
    [SigmaFinite μ] :
    SigmaFinite (μ.map f) := by
  refine ⟨fun n ↦ f '' (spanningSets μ n) ∪ (Set.range f)ᶜ, by simp, fun n ↦ ?_, ?_⟩
  · rw [hf.map_apply, Set.preimage_union]
    simp only [Set.preimage_compl, Set.preimage_range, Set.compl_univ, Set.union_empty,
      Set.preimage_image_eq _ hf.injective]
    exact measure_spanningSets_lt_top μ n
  · rw [← Set.iUnion_union, ← Set.image_iUnion, iUnion_spanningSets,
      Set.image_univ, Set.union_compl_self]

theorem _root_.MeasurableEquiv.sigmaFinite_map (f : α ≃ᵐ β) [SigmaFinite μ] :
    SigmaFinite (μ.map f) := f.measurableEmbedding.sigmaFinite_map

/-- Similar to `ae_of_forall_measure_lt_top_ae_restrict`, but where you additionally get the
  hypothesis that another σ-finite measure has finite values on `s`. -/
theorem ae_of_forall_measure_lt_top_ae_restrict' {μ : Measure α} (ν : Measure α) [SigmaFinite μ]
    [SigmaFinite ν] (P : α → Prop)
    (h : ∀ s, MeasurableSet s → μ s < ∞ → ν s < ∞ → ∀ᵐ x ∂μ.restrict s, P x) : ∀ᵐ x ∂μ, P x := by
  have : ∀ n, ∀ᵐ x ∂μ, x ∈ spanningSets (μ + ν) n → P x := by
    intro n
    have := h
      (spanningSets (μ + ν) n) (measurableSet_spanningSets _ _)
      ((self_le_add_right _ _).trans_lt (measure_spanningSets_lt_top (μ + ν) _))
      ((self_le_add_left _ _).trans_lt (measure_spanningSets_lt_top (μ + ν) _))
    exact (ae_restrict_iff' (measurableSet_spanningSets _ _)).mp this
  filter_upwards [ae_all_iff.2 this] with _ hx using hx _ (mem_spanningSetsIndex _ _)

/-- To prove something for almost all `x` w.r.t. a σ-finite measure, it is sufficient to show that
  this holds almost everywhere in sets where the measure has finite value. -/
theorem ae_of_forall_measure_lt_top_ae_restrict {μ : Measure α} [SigmaFinite μ] (P : α → Prop)
    (h : ∀ s, MeasurableSet s → μ s < ∞ → ∀ᵐ x ∂μ.restrict s, P x) : ∀ᵐ x ∂μ, P x :=
  ae_of_forall_measure_lt_top_ae_restrict' μ P fun s hs h2s _ => h s hs h2s

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
  refine Measure.sigmaFinite_of_countable (htc.image s) (forall_mem_image.2 fun x _ => hsμ x) ?_
  rwa [sUnion_image]

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

theorem FiniteSpanningSetsIn.disjointed_set_eq {μ : Measure α}
    (S : μ.FiniteSpanningSetsIn { s | MeasurableSet s }) : S.disjointed.set = disjointed S.set :=
  rfl

theorem exists_eq_disjoint_finiteSpanningSetsIn (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    ∃ (S : μ.FiniteSpanningSetsIn { s | MeasurableSet s })
      (T : ν.FiniteSpanningSetsIn { s | MeasurableSet s }),
      S.set = T.set ∧ Pairwise (Disjoint on S.set) :=
  let S := (μ + ν).toFiniteSpanningSetsIn.disjointed
  ⟨S.ofLE (Measure.le_add_right le_rfl), S.ofLE (Measure.le_add_left le_rfl), rfl,
    disjoint_disjointed _⟩

end disjointed

end Measure

end MeasureTheory
