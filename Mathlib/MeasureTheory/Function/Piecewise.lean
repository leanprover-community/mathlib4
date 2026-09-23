/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Data.Setoid.Partition
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

/-!
# Measurability of piecewise functions

In this file, we prove some results about measurability of functions defined by using
`IndexedPartition.piecewise`.

-/

@[expose] public section

open MeasureTheory Set Filter

namespace IndexedPartition

variable {ι α β : Type*} [MeasurableSpace α] {s : ι → Set α} {f : ι → α → β}

@[fun_prop]
theorem measurable_piecewise [MeasurableSpace β] [Countable ι]
    (hs : IndexedPartition s) (hm : ∀ i, MeasurableSet (s i)) (hf : ∀ i, Measurable (f i)) :
    Measurable (hs.piecewise f) :=
  fun t ht => by simpa [piecewise_preimage] using .iUnion (fun i => (hm i).inter ((hf i) ht))

@[fun_prop]
theorem aemeasurable_piecewise {μ : Measure α} [MeasurableSpace β] [Countable ι]
    (hs : IndexedPartition s) (hm : ∀ i, MeasurableSet (s i)) (hf : ∀ i, AEMeasurable (f i) μ) :
    AEMeasurable (hs.piecewise f) μ := by
  choose p hp hq using hf
  refine ⟨hs.piecewise p, hs.measurable_piecewise hm hp, ?_⟩
  filter_upwards [ae_all_iff.2 hq] with x hx using hx (hs.index x)

/-- This is the analogue of `SimpleFunc.piecewise` for `IndexedPartition`. -/
def simpleFunc_piecewise [Finite ι] (hs : IndexedPartition s)
    (hm : ∀ i, MeasurableSet (s i)) (f : ι → SimpleFunc α β) : SimpleFunc α β where
  toFun := hs.piecewise (fun i => f i)
  measurableSet_fiber' := fun _ =>
    letI : MeasurableSpace β := ⊤
    hs.measurable_piecewise hm (fun i => (f i).measurable) trivial
  finite_range' := (finite_iUnion (fun i => (f i).finite_range)).subset
    (hs.range_piecewise_subset _)

@[fun_prop]
theorem stronglyMeasurable_piecewise [Countable ι] (hs : IndexedPartition s)
    (hm : ∀ i, MeasurableSet (s i)) [TopologicalSpace β] (hf : ∀ i, StronglyMeasurable (f i)) :
    StronglyMeasurable (hs.piecewise f) := by
  by_cases Fi : Finite ι
  · refine ⟨fun n => simpleFunc_piecewise hs hm (fun i => (hf i).approx n), fun x => ?_⟩
    simp [simpleFunc_piecewise, piecewise_apply, StronglyMeasurable.tendsto_approx]
  simp only [not_finite_iff_infinite] at Fi
  obtain ⟨e, -⟩ := exists_true_iff_nonempty.mpr (nonempty_equiv_of_countable (α := ℕ) (β := ι))
  classical
  let g (n : ℕ) (i : ι) : Fin (n + 1) :=
    if hi : ∃ m < n, i = e m then ⟨hi.choose, by grind⟩ else Fin.last n
  have sg (n : ℕ) : (g n).Surjective := by
    intro b
    unfold g
    refine ⟨e b, ?_⟩
    by_cases hb : b < n
    · have : ∃ m < n, e b = e m := ⟨b, ⟨hb, rfl⟩⟩
      simpa only [this, Fin.ext_iff] using e.injective this.choose_spec.2.symm
    · simp [hb]
      grind
  have G (n : ℕ) := hs.coarserPartition (g n) (sg n)
  refine ⟨fun n => (G n).simpleFunc_piecewise (fun i => ?_) (fun i => (hf (e i)).approx n),
    fun x => ?_⟩
  · exact .biUnion (to_countable _) fun _ _ ↦ hm _
  simp only [simpleFunc_piecewise, SimpleFunc.coe_mk, piecewise_apply]
  have : ∀ᶠ n in atTop, e ((G n).index x) = hs.index x := by
    obtain ⟨y, hy⟩ := e.bijective.2 (hs.index x)
    refine eventually_atTop.mpr ⟨y + 1, fun b hb => ?_⟩
    have : y = (⟨y, by lia⟩ : Fin (b + 1)).1 := rfl
    rw [← hy, EmbeddingLike.apply_eq_iff_eq, this, ← Fin.ext_iff, ← (G b).mem_iff_index_eq]
    have : ∃ m < b, hs.index x = e m := ⟨y, ⟨by lia, hy.symm⟩⟩
    simpa [g, hs.mem_iff_index_eq, this] using e.injective (hy.trans this.choose_spec.2).symm
  have : ∀ᶠ n in atTop, (hf (hs.index x)).approx n x = (hf (e ((G n).index x))).approx n x := by
    filter_upwards [this] with n hn using by rw [hn]
  exact (Filter.tendsto_congr' this).mp (by simp [StronglyMeasurable.tendsto_approx])

@[fun_prop]
theorem aestronglyMeasurable_piecewise {μ : Measure α} [Countable ι] (hs : IndexedPartition s)
    (hm : ∀ i, MeasurableSet (s i)) [TopologicalSpace β] (hf : ∀ i, AEStronglyMeasurable (f i) μ) :
    AEStronglyMeasurable (hs.piecewise f) μ := by
  choose p hp hq using hf
  refine ⟨hs.piecewise p, hs.stronglyMeasurable_piecewise hm hp, ?_⟩
  filter_upwards [ae_all_iff.2 hq] with x hx using hx (hs.index x)

end IndexedPartition
