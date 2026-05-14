/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
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
import Mathlib.Logic.Equiv.List
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Order.Filter.Map
import Mathlib.Order.Filter.Tendsto
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.Translate.ToAdditive
import Mathlib.Topology.Algebra.InfiniteSum.Basic
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
  let e := Classical.choice hE
  let conv := {x | ∃ c, Tendsto (f · x) l (𝓝 c)}
  have mconv : MeasurableSet conv := StronglyMeasurable.measurableSet_exists_tendsto hf
  have hconv : StronglyMeasurable (fun x : conv ↦ limUnder l (f · x)) := by
    refine stronglyMeasurable_of_tendsto l
      (fun i ↦ (hf i).comp_measurable measurable_subtype_coe) ?_
    refine tendsto_pi_nhds.2 fun x ↦ ?_
    obtain ⟨c, hc⟩ := x.2
    rwa [hc.limUnder_eq]
  have : (fun x ↦ limUnder l (f · x)) = ((↑) : conv → X).extend
      (fun x ↦ limUnder l (f · x)) (fun _ ↦ e) := by
    ext x
    by_cases hx : x ∈ conv
    · rw [Function.extend_val_apply hx]
    · rw [Function.extend_val_apply' hx, limUnder_of_not_tendsto hx]
  rw [this]
  exact (MeasurableEmbedding.subtype_coe mconv).stronglyMeasurable_extend hconv
    stronglyMeasurable_const

end MeasureTheory.StronglyMeasurable

namespace MeasureTheory

variable {X E ι : Type*} [MeasurableSpace X] [CommMonoid E] [TopologicalSpace E]

section

variable [IsCompletelyPseudoMetrizableSpace E] [ContinuousMul E]
  [Countable ι] {L : SummationFilter ι} [L.NeBot] [L.filter.IsCountablyGenerated]

/-- The product of strongly measurable functions is measurable. -/
@[to_additive (attr := fun_prop)
/-- The sum of strongly measurable functions is measurable. -/]
theorem StronglyMeasurable.tprod {f : ι → X → E} (h : ∀ i : ι, StronglyMeasurable (f i)) :
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
theorem AEStronglyMeasurable.tprod {μ : MeasureTheory.Measure X} {f : ι → X → E}
    (h : ∀ i : ι, AEStronglyMeasurable (f i) μ) :
    AEStronglyMeasurable (fun x => ∏'[L] i : ι, f i x) μ := by
  choose g hg_meas hg_eq_f using h
  use (fun x => ∏'[L] i, g i x), StronglyMeasurable.tprod hg_meas
  filter_upwards [ae_all_iff.mpr hg_eq_f] with x h_eq using tprod_congr h_eq

end

section

variable [PseudoMetrizableSpace E] [ContinuousMul E]
  {L : SummationFilter ι} [L.NeBot] [L.filter.IsCountablyGenerated]

/-- The product of strongly measurable functions is measurable. -/
@[to_additive (attr := fun_prop)
/-- The sum of strongly measurable functions is measurable. -/]
theorem StronglyMeasurable.tprod' {f : ι → X → E} (h : ∀ i : ι, StronglyMeasurable (f i)) :
    StronglyMeasurable (∏'[L] i : ι, f i) := by
  rw [tprod_def, finprod_def']
  split_ifs with hm
  any_goals exact stronglyMeasurable_one
  · refine Finset.stronglyMeasurable_prod _ (fun _ _ ↦ ?_)
    rw [Set.mulIndicator]
    split_ifs
    · fun_prop
    · exact stronglyMeasurable_one
  · exact stronglyMeasurable_of_tendsto L.filter (by fun_prop) hm.choose_spec

/-- The product of almost everywhere strongly measurable functions is measurable. -/
@[to_additive (attr := fun_prop)
/-- The sum of almost everywhere strongly measurable functions is measurable. -/]
theorem AEStronglyMeasurable.tprod' {μ : MeasureTheory.Measure X} {f : ι → X → E}
    (h : ∀ i : ι, AEStronglyMeasurable (f i) μ) : AEStronglyMeasurable (∏'[L] i : ι, f i) μ := by
  rw [tprod_def, finprod_def']
  split_ifs with hm
  any_goals exact aestronglyMeasurable_one
  · refine Finset.aestronglyMeasurable_prod _ (fun _ _ ↦ ?_)
    rw [Set.mulIndicator]
    split_ifs <;> fun_prop
  · apply aestronglyMeasurable_of_tendsto_ae L.filter (f := fun s => ∏ i ∈ s, f i) (by fun_prop)
    exact .of_forall fun x ↦ hm.choose_spec.apply_nhds x

end

end MeasureTheory
