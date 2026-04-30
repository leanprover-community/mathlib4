/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

/-!
# Results about strongly measurable functions

In measure theory it is often assumed that some space is a `PolishSpace`, i.e. a separable and
completely metrizable topological space, because it ensures a nice interaction between the topology
and the measurable space structure. Moreover a strongly measurable function whose codomain is a
metric space is measurable and has a separable range
(see `stronglyMeasurable_iff_measurable_separable`). Therefore if the codomain is also complete,
by corestricting the function to the closure of its range, some results about measurable functions
can be extended to strongly measurable functions without assuming separability on the codomain.
The purpose of this file is to collect those results.
-/

public section

open Filter MeasureTheory Set TopologicalSpace

open scoped Topology

variable {ι X E : Type*} [MeasurableSpace X] [TopologicalSpace E] [Countable ι] {l : Filter ι}
  [l.IsCountablyGenerated] {f : ι → X → E}

namespace MeasureTheory.StronglyMeasurable

theorem measurableSet_exists_tendsto [IsCompletelyPseudoMetrizableSpace E]
    (hf : ∀ i, StronglyMeasurable (f i)) :
    MeasurableSet {x | ∃ c, Tendsto (f · x) l (𝓝 c)} := by
  obtain rfl | hl := eq_or_neBot l
  · simp_all
  borelize E
  letI := upgradeIsCompletelyPseudoMetrizable E
  let s := closure (⋃ i, range (f i))
  have : SecondCountableTopology s := @UniformSpace.secondCountable_of_separable s _ _
    (IsSeparable.iUnion (fun i ↦ (hf i).isSeparable_range)).closure.separableSpace
  have : IsCompletelyPseudoMetrizableSpace s := isClosed_closure.isCompletelyPseudoMetrizableSpace
  let g i x : s := ⟨f i x, subset_closure <| mem_iUnion.2 ⟨i, ⟨x, rfl⟩⟩⟩
  have mg i : Measurable (g i) := (hf i).measurable.subtype_mk
  convert MeasureTheory.measurableSet_exists_tendsto (l := l) mg with x
  refine ⟨fun ⟨c, hc⟩ ↦ ⟨⟨c, ?_⟩, tendsto_subtype_rng.2 hc⟩,
    fun ⟨c, hc⟩ ↦ ⟨c, tendsto_subtype_rng.1 hc⟩⟩
  exact mem_closure_of_tendsto hc (Eventually.of_forall fun i ↦ mem_iUnion.2 ⟨i, ⟨x, rfl⟩⟩)

protected theorem limUnder [hE : Nonempty E] [IsCompletelyMetrizableSpace E]
    (hf : ∀ i, StronglyMeasurable (f i)) :
    StronglyMeasurable (fun x ↦ limUnder l (f · x)) := by
  obtain rfl | hl := eq_or_neBot l
  · simpa [limUnder, Filter.map_bot] using stronglyMeasurable_const
  borelize E
  let e := Classical.choice hE
  rw [stronglyMeasurable_iff_measurable_separable]; constructor
  · let conv := {x | ∃ c, Tendsto (f · x) l (𝓝 c)}
    have mconv : MeasurableSet conv := StronglyMeasurable.measurableSet_exists_tendsto hf
    have : (fun x ↦ limUnder l (f · x)) = ((↑) : conv → X).extend
        (fun x ↦ limUnder l (f · x)) (fun _ ↦ e) := by
      ext x
      by_cases hx : x ∈ conv
      · rw [Function.extend_val_apply hx]
      · rw [Function.extend_val_apply' hx, limUnder_of_not_tendsto hx]
    rw [this]
    refine (MeasurableEmbedding.subtype_coe mconv).measurable_extend
      (measurable_of_tendsto_metrizable' l
        (fun i ↦ (hf i).measurable.comp measurable_subtype_coe)
        (tendsto_pi_nhds.2 fun ⟨x, ⟨c, hc⟩⟩ ↦ ?_)) measurable_const
    rwa [hc.limUnder_eq]
  · let s := closure (⋃ i, range (f i)) ∪ {e}
    have hs : IsSeparable s := (IsSeparable.iUnion (fun i ↦ (hf i).isSeparable_range)).closure.union
      (finite_singleton e).isSeparable
    refine hs.mono ?_
    rintro - ⟨x, rfl⟩
    by_cases hx : ∃ c, Tendsto (f · x) l (𝓝 c)
    · obtain ⟨c, hc⟩ := hx
      simp_rw [hc.limUnder_eq]
      exact subset_union_left <| mem_closure_of_tendsto hc
        (Eventually.of_forall fun i ↦ mem_iUnion.2 ⟨i, ⟨x, rfl⟩⟩)
    · simp_rw [limUnder_of_not_tendsto hx]
      exact subset_union_right (mem_singleton e)

end MeasureTheory.StronglyMeasurable

namespace MeasureTheory

variable {α β ι : Type*} [MeasurableSpace α] [CommMonoid β] [TopologicalSpace β]

section

variable [IsCompletelyPseudoMetrizableSpace β] [ContinuousMul β]
  [Countable ι] {L : SummationFilter ι} [L.NeBot] [L.filter.IsCountablyGenerated]

/-- The product of strongly measurable functions is measurable. -/
@[to_additive (attr := fun_prop)
/-- The sum of strongly measurable functions is measurable. -/]
theorem StronglyMeasurable.tprod {f : ι → α → β} (h : ∀ i : ι, StronglyMeasurable (f i)) :
    StronglyMeasurable (fun x => ∏'[L] i : ι, f i x) := by
  let E := { x | Multipliable (f · x) L }
  have hE : MeasurableSet E := StronglyMeasurable.measurableSet_exists_tendsto (by fun_prop)
  have h0 : (Eᶜ.restrict fun x => ∏'[L] i, f i x) = fun _ => 1 :=
    funext fun ⟨x, hx⟩ => tprod_eq_one_of_not_multipliable hx
  refine stronglyMeasurable_of_restrict_of_restrict_compl hE ?_ (h0 ▸ stronglyMeasurable_const)
  refine stronglyMeasurable_of_tendsto L.filter ?_ (tendsto_pi_nhds.mpr fun e => e.2.hasProd)
  fun_prop

/-- The product of almost everywhere strongly measurable functions is measurable. -/
@[to_additive (attr := fun_prop)
/-- The sum of almost everywhere strongly measurable functions is measurable. -/]
theorem AEStronglyMeasurable.tprod {μ : MeasureTheory.Measure α} {f : ι → α → β}
    (h : ∀ i : ι, AEStronglyMeasurable (f i) μ) :
    AEStronglyMeasurable (fun x => ∏'[L] i : ι, f i x) μ := by
  choose g hg_meas hg_eq_f using h
  use (fun x => ∏'[L] i, g i x), StronglyMeasurable.tprod hg_meas
  filter_upwards [MeasureTheory.ae_all_iff.mpr hg_eq_f] with x h_eq using tprod_congr h_eq

end

section

variable [PseudoMetrizableSpace β] [ContinuousMul β]
  {L : SummationFilter ι} [L.NeBot] [L.filter.IsCountablyGenerated]

/-- The product of strongly measurable functions is measurable. -/
@[to_additive (attr := fun_prop)
/-- The sum of strongly measurable functions is measurable. -/]
theorem StronglyMeasurable.tprod' {f : ι → α → β} (h : ∀ i : ι, StronglyMeasurable (f i)) :
    StronglyMeasurable (∏'[L] i : ι, f i) := by
  rw [tprod_def, finprod_def']
  split_ifs with hm
  · refine Finset.stronglyMeasurable_prod _ fun _ _ => ?_
    rw [Set.mulIndicator]
    split_ifs
    · fun_prop
    · exact stronglyMeasurable_one
  · exact stronglyMeasurable_one
  · exact stronglyMeasurable_one
  · exact stronglyMeasurable_of_tendsto L.filter (by fun_prop) hm.choose_spec
  · exact stronglyMeasurable_one

/-- The product of almost everywhere strongly measurable functions is measurable. -/
@[to_additive (attr := fun_prop)
/-- The sum of almost everywhere strongly measurable functions is measurable. -/]
theorem AEStronglyMeasurable.tprod' {μ : MeasureTheory.Measure α} {f : ι → α → β}
    (h : ∀ i : ι, AEStronglyMeasurable (f i) μ) : AEStronglyMeasurable (∏'[L] i : ι, f i) μ := by
  rw [tprod_def, finprod_def']
  split_ifs with hm
  · refine Finset.aestronglyMeasurable_prod _ fun _ _ => ?_
    rw [Set.mulIndicator]
    split_ifs <;> fun_prop
  · exact aestronglyMeasurable_one
  · exact aestronglyMeasurable_one
  · apply aestronglyMeasurable_of_tendsto_ae L.filter (f := fun s => ∏ i ∈ s, f i) (by fun_prop)
    filter_upwards with x using Tendsto.apply_nhds hm.choose_spec x
  · exact aestronglyMeasurable_one

end

end MeasureTheory
