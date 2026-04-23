/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Order.Filter.Map
import Mathlib.Order.Filter.Tendsto
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Neighborhoods

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

variable {ι X E : Type*} [MeasurableSpace X] [TopologicalSpace E] [IsCompletelyMetrizableSpace E]
  [Countable ι] {l : Filter ι} [l.IsCountablyGenerated] {f : ι → X → E}

namespace MeasureTheory.StronglyMeasurable

theorem measurableSet_exists_tendsto (hf : ∀ i, StronglyMeasurable (f i)) :
    MeasurableSet {x | ∃ c, Tendsto (f · x) l (𝓝 c)} := by
  obtain rfl | hl := eq_or_neBot l
  · simp_all
  borelize E
  letI := upgradeIsCompletelyMetrizable E
  let s := closure (⋃ i, range (f i))
  have : PolishSpace s :=
    { toSecondCountableTopology := @UniformSpace.secondCountable_of_separable s _ _
        (IsSeparable.iUnion (fun i ↦ (hf i).isSeparable_range)).closure.separableSpace
      toIsCompletelyMetrizableSpace := isClosed_closure.isCompletelyMetrizableSpace }
  let g i x : s := ⟨f i x, subset_closure <| mem_iUnion.2 ⟨i, ⟨x, rfl⟩⟩⟩
  have mg i : Measurable (g i) := (hf i).measurable.subtype_mk
  convert MeasureTheory.measurableSet_exists_tendsto (l := l) mg with x
  refine ⟨fun ⟨c, hc⟩ ↦ ⟨⟨c, ?_⟩, tendsto_subtype_rng.2 hc⟩,
    fun ⟨c, hc⟩ ↦ ⟨c, tendsto_subtype_rng.1 hc⟩⟩
  exact mem_closure_of_tendsto hc (Eventually.of_forall fun i ↦ mem_iUnion.2 ⟨i, ⟨x, rfl⟩⟩)

protected theorem limUnder [hE : Nonempty E] (hf : ∀ i, StronglyMeasurable (f i)) :
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
