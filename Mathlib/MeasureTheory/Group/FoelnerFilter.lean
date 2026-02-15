/-
Copyright (c) 2025 Stefano Rocca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Stefano Rocca
-/
module

public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Group.Action
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Følner sequences and filters - definitions and properties

This file defines Følner sequences and filters for measurable spaces acted on by a group.

## Definitions

* `IsFoelner G μ l F` : Consider a group `G` acting on a measure space `X`.
  A sequence of sets `F : ι → Set X` is **Følner** with respect to the `G`-action, the measure `μ`,
  and a filter `l` on the indexing type `ι`, if:
  1. Eventually, as `i` tends to `l`, the set `F i` is measurable with finite non-zero measure,
  2. For all `g : G`, `μ ((g • F i) ∆ F i) / μ (F i)` tends to `0`.

* `IsFoelner.mean μ u F s` : The limit along an ultrafilter `u` of the density of a set `s`
  with respect to a Følner sequence `F` in the measure space `X`.

* `maxFoelner G μ` : The maximal Følner filter with respect to some group `G` acting on a
  measure space `X` is the pullback of `𝓝 0` along the map `s ↦ μ (g • s) / μ s` over measurable
  sets of finite non-zero measure.

* `IsAddFoelner G μ l F`: the analog of `IsFoelner G μ l F` for an additive group action

## Main results

* `IsFoelner.amenable` : If there exists a non-trivial Følner filter with respect to some
  group `G` acting on a measure space `X`, then there exists a `G`-invariant finitely additive
  probability measure on `X`.

* `isFoelner_iff_tendsto` : A sequence of sets is Følner if and only if it tends to the
  maximal Følner filter.
  The attribute "maximal" of the latter comes from the direct implication of this theorem :
  if `IsFoelner G μ l F` then the push-forward filter `map F l ≤ maxFoelner G μ`.

* `amenable_of_maxFoelner_neBot` : If the maximal Følner filter is non-trivial,
  then there exists a `G`-invariant finitely additive probability measure on `X`.

## Temporary design adaptations

* In the current version, we refer to the amenability of the action of a group on a measure space
  (e.g. in `IsFoelner.amenable` and `amenable_of_maxFoelner_neBot`), even though a definition of
  amenability has not yet been given in Mathlib.
  This is because there are different notions of amenability for groups and for group actions,
  and a Mathlib definition should be provided at the greatest level of generality, on which there
  has not yet been a general consensus.
  At the present moment, `amenable` corresponds to the existence of a `G`-invariant finitely
  additive probability measure.

## Tags

Foelner, Følner filter, amenability, amenable group
-/

@[expose] public section

open MeasureTheory Filter Set Tendsto
open scoped ENNReal Pointwise symmDiff Topology Filter

variable {G X : Type*} [MeasurableSpace X] {μ : Measure X} [Group G] [MulAction G X]
variable {ι : Type*} {l : Filter ι} {u : Ultrafilter ι} {F : ι → Set X}

variable (G : Type*) {X : Type*} [MeasurableSpace X] (μ : Measure X) [AddGroup G] [AddAction G X]
         {ι : Type*} (l : Filter ι) (F : ι → Set X) in
/-- Consider an additive group `G` acting on a measure space `X`.
  A sequence of sets `F : ι → Set X` is **Følner** with respect to the `G`-action,
  the measure `μ`, and a filter `l` on the indexing type `ι`, if:
  1. Each `s` in `l` is eventually measurable with finite non-zero measure,
  2. For all `g : G`, `μ ((g +ᵥ F i) ∆ F i) / μ (F i)` tends to `0`. -/
@[mk_iff]
structure IsAddFoelner : Prop where
  eventually_measurableSet : ∀ᶠ i in l, MeasurableSet (F i)
  eventually_meas_ne_zero : ∀ᶠ i in l, μ (F i) ≠ 0
  eventually_meas_ne_top : ∀ᶠ i in l, μ (F i) ≠ ∞
  tendsto_meas_vadd_symmDiff (g : G) : Tendsto (fun i ↦ μ ((g +ᵥ F i) ∆ F i) / μ (F i)) l (𝓝 0)

variable (G μ l F) in
/-- Consider a group `G` acting on a measure space `X`.
  A sequence of sets `F : ι → Set X` is **Følner** with respect to the `G`-action,
  the measure `μ`, and a filter `l` on the indexing type `ι`, if:
  1. Each `s` in `l` is eventually measurable with finite non-zero measure,
  2. For all `g : G`, `μ ((g • F i) ∆ F i) / μ (F i)` tends to `0`. -/
@[mk_iff]
structure IsFoelner : Prop where
  eventually_measurableSet : ∀ᶠ i in l, MeasurableSet (F i)
  eventually_meas_ne_zero : ∀ᶠ i in l, μ (F i) ≠ 0
  eventually_meas_ne_top : ∀ᶠ i in l, μ (F i) ≠ ∞
  tendsto_meas_smul_symmDiff (g : G) : Tendsto (fun i ↦ μ ((g • F i) ∆ F i) / μ (F i)) l (𝓝 0)

attribute [to_additive IsAddFoelner] IsFoelner
attribute [to_additive existing isAddFoelner_iff] isFoelner_iff

namespace IsFoelner

/-- The constant sequence `X` is Følner if `X` has finite measure. -/
@[to_additive /--The constant sequence `X` is Følner if `X` has finite measure. -/]
theorem univ_of_isFiniteMeasure [NeZero μ] [IsFiniteMeasure μ] :
    IsFoelner G μ l (fun _ ↦ .univ) where
  eventually_measurableSet := by simp
  eventually_meas_ne_zero := by simp [NeZero.ne]
  eventually_meas_ne_top := by simp
  tendsto_meas_smul_symmDiff := by simp [tendsto_const_nhds]

@[to_additive]
theorem mono {l' : Filter ι} (hfoel : IsFoelner G μ l F) (hle : l' ≤ l) :
    IsFoelner G μ l' F where
  eventually_measurableSet := hfoel.eventually_measurableSet.filter_mono hle
  eventually_meas_ne_zero := hfoel.eventually_meas_ne_zero.filter_mono hle
  eventually_meas_ne_top := hfoel.eventually_meas_ne_top.filter_mono hle
  tendsto_meas_smul_symmDiff (g : G) := Tendsto.mono_left (hfoel.tendsto_meas_smul_symmDiff g) hle

@[to_additive]
theorem comp_tendsto {ι' : Type*} {l' : Filter ι'} {φ : ι' → ι} (hfoel : IsFoelner G μ l F)
    (htendsto : Tendsto φ l' l) :
    IsFoelner G μ l' (F ∘ φ) where
  eventually_measurableSet := htendsto.eventually hfoel.eventually_measurableSet
  eventually_meas_ne_zero := htendsto.eventually hfoel.eventually_meas_ne_zero
  eventually_meas_ne_top := htendsto.eventually hfoel.eventually_meas_ne_top
  tendsto_meas_smul_symmDiff (g : G) := (hfoel.tendsto_meas_smul_symmDiff g).comp htendsto

variable (μ u F) in
/-- The limit along an ultrafilter of the density of a set with respect to a sequence in `X`. -/
@[to_additive
/-- The limit along an ultrafilter of the density of a set with respect to a sequence in `X`. -/]
noncomputable def mean (s : Set X) :=
  limUnder u (fun i ↦ μ (s ∩ F i) / μ (F i))

@[to_additive]
theorem tendsto_nhds_mean (hfoel : IsFoelner G μ u F) (s : Set X) :
    Tendsto (fun i ↦ μ (s ∩ F i) / μ (F i)) u (𝓝 (mean μ u F s)) := by
  have mem_Icc : ∀ᶠ i in u, μ (s ∩ F i) / μ (F i) ∈ Icc 0 1 := by
    filter_upwards [hfoel.eventually_meas_ne_zero, hfoel.eventually_meas_ne_top] with i hi hi'
    simpa [ENNReal.div_le_iff hi hi'] using μ.mono inter_subset_right
  obtain ⟨x, hx⟩ := isCompact_Icc.ultrafilter_le_nhds'
    (u.map (fun i ↦ μ (s ∩ F i) / μ (F i))) (mem_map.1 mem_Icc)
  exact tendsto_nhds_limUnder (by use x; exact hx.2)

@[to_additive]
theorem mean_univ_eq_one (hfoel : IsFoelner G μ u F) :
    mean μ u F .univ = 1 := by
  refine tendsto_nhds_unique_of_eventuallyEq (hfoel.tendsto_nhds_mean _) tendsto_const_nhds ?_
  filter_upwards [hfoel.eventually_meas_ne_zero, hfoel.eventually_meas_ne_top] with i hi hi'
  simp [ENNReal.div_self hi hi']

@[to_additive]
theorem mean_union_eq_add_of_disjoint (hfoel : IsFoelner G μ u F)
    (s t : Set X) (ht : MeasurableSet t) (hdisj : Disjoint s t) :
    mean μ u F (s ∪ t) = mean μ u F s + mean μ u F t := by
  refine tendsto_nhds_unique_of_eventuallyEq
    (hfoel.tendsto_nhds_mean _) (hfoel.tendsto_nhds_mean _ |>.add <| hfoel.tendsto_nhds_mean _) ?_
  filter_upwards [hfoel.eventually_measurableSet] with i hi
  rw [union_inter_distrib_right,
    measure_union (hdisj.inter_left _ |>.inter_right _) (ht.inter hi), ENNReal.add_div]

@[to_additive]
theorem tendsto_meas_smul_symmDiff_smul [SMulInvariantMeasure G X μ]
    (hfoel : IsFoelner G μ u F) (g h : G) :
    Tendsto (fun i ↦ μ ((g • F i) ∆ (h • F i)) / μ (F i)) u (𝓝 0) := by
  simpa [← smul_smul] using hfoel.tendsto_meas_smul_symmDiff (h⁻¹ * g)

@[to_additive]
theorem mean_smul_eq_mean_smul [SMulInvariantMeasure G X μ]
    (hfoel : IsFoelner G μ u F) (g h : G) (s : Set X) :
    mean μ u F (g • s) = mean μ u F (h • s) := by
  suffices hle : ∀ g h, mean μ u F (g • s) ≤ mean μ u F (h • s) by
    exact le_antisymm (hle g h) (hle h g)
  intro g h
  rw [← add_zero <| mean μ u F (h • s)]
  refine le_of_tendsto_of_tendsto
    (hfoel.tendsto_nhds_mean (g • s))
    (hfoel.tendsto_nhds_mean (h • s) |>.add <| hfoel.tendsto_meas_smul_symmDiff_smul g⁻¹ h⁻¹) ?_
  filter_upwards [hfoel.eventually_meas_ne_zero] with i hi
  rw [← tsub_le_iff_left, ← ENNReal.sub_div <| fun _ _ ↦ hi]
  refine ENNReal.div_le_div_right (le_trans ?_ (measure_mono <| @inter_subset_right _ s _)) _
  simpa [inter_symmDiff_distrib_left, ← measure_inter_inv_smul] using le_measure_symmDiff

@[to_additive]
theorem mean_smul_eq_mean [SMulInvariantMeasure G X μ]
    (hfoel : IsFoelner G μ u F) (g : G) (s : Set X) :
    mean μ u F (g • s) = mean μ u F s := by
  simpa using hfoel.mean_smul_eq_mean_smul g 1 s

/-- If there exists a non-trivial Følner filter with respect to some group `G` acting on a measure
    space `X`, then there exists a `G`-invariant finitely additive probability measure on `X`. -/
@[to_additive
/-- If there exists a non-trivial Følner filter with respect to some additive group
    `G` acting on a measure space `X`, then there exists a `G`-invariant finitely additive
    probability measure on `X`. -/]
theorem amenable [SMulInvariantMeasure G X μ] [NeBot l] (hfoel : IsFoelner G μ l F) :
    ∃ m : Set X → ℝ≥0∞, m .univ = 1 ∧
      (∀ s t, MeasurableSet t → Disjoint s t → m (s ∪ t) = m s + m t) ∧
        ∀ (g : G) (s : Set X), m (g • s) = m s := by
  use mean μ (Ultrafilter.of l) F
  refine ⟨?_, ?_, ?_⟩
  · exact (hfoel.mono <| Ultrafilter.of_le l).mean_univ_eq_one
  · exact (hfoel.mono <| Ultrafilter.of_le l).mean_union_eq_add_of_disjoint
  · exact (hfoel.mono <| Ultrafilter.of_le l).mean_smul_eq_mean

end IsFoelner

variable (G μ) in
/-- The maximal Følner filter with respect to some group `G` acting on a
    measure space `X` is the pullback of `𝓝 0` along the map `s ↦ μ (g • s) / μ s`
    on measurable sets of finite non-zero measure. -/
@[to_additive maxAddFoelner
/-- The maximal Følner filter with respect to some additive group `G` acting
    on a measure space `X` is the pullback of `𝓝 0` along the map `s ↦ μ (g +ᵥ s) / μ s`
    on measurable sets of finite non-zero measure. -/]
def maxFoelner : Filter (Set X) :=
  𝓟 {s : Set X | MeasurableSet s ∧ μ s ≠ 0 ∧ μ s ≠ ∞} ⊓
  ⨅ (g : G), comap (fun s ↦ μ ((g • s) ∆ s) / μ s) (𝓝 0)

variable (l F) in
@[to_additive isAddFoelner_iff_tendsto]
theorem isFoelner_iff_tendsto : IsFoelner G μ l F ↔ Tendsto F l (maxFoelner G μ) := by
  simp [maxFoelner, tendsto_inf, tendsto_iInf, isFoelner_iff, Function.comp_def, and_assoc]

variable (G μ) in
@[to_additive isAddFoelner_maxAddFoelner]
theorem isFoelner_maxFoelner : IsFoelner G μ (maxFoelner G μ) id :=
  isFoelner_iff_tendsto _ _ |>.2 <| @tendsto_id _ (maxFoelner G μ)

@[to_additive amenable_of_maxAddFoelner_neBot]
theorem amenable_of_maxFoelner_neBot [SMulInvariantMeasure G X μ] [NeBot (maxFoelner G μ)] :
    ∃ m : Set X → ℝ≥0∞, m .univ = 1 ∧
      (∀ s t, MeasurableSet t → Disjoint s t → m (s ∪ t) = m s + m t) ∧
        ∀ (g : G) (s : Set X), m (g • s) = m s :=
  IsFoelner.amenable <| isFoelner_maxFoelner G μ
