/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.Order.Interval.Set.Monotone

/-!
# Measures of intervals

This file provide lemmas regarding the properties of measures and intervals,
such as continuity statements specialized to intervals or the fact that if `µ {a} = 0`
then `Icc a b =ᵐ[μ] Ioc a b`.

## Tags

measure, interval
-/

public section

open Set Filter
open scoped Topology

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}

section Preorder

variable [Preorder α]

theorem biSup_measure_Iic {s : Set α} (hsc : s.Countable)
    (hst : ∀ x : α, ∃ y ∈ s, x ≤ y) (hdir : DirectedOn (· ≤ ·) s) :
    ⨆ x ∈ s, μ (Iic x) = μ univ := by
  rw [← measure_biUnion_eq_iSup hsc]
  · congr
    simp only [← bex_def] at hst
    exact iUnion₂_eq_univ_iff.2 hst
  · exact directedOn_iff_directed.2 (hdir.directed_val.mono_comp _ fun x y => Iic_subset_Iic.2)

theorem tendsto_measure_Ico_atTop [NoMaxOrder α] [(atTop : Filter α).IsCountablyGenerated]
    (μ : Measure α) (a : α) :
    Tendsto (fun x => μ (Ico a x)) atTop (𝓝 (μ (Ici a))) := by
  rw [← iUnion_Ico_right]
  exact tendsto_measure_iUnion_atTop (antitone_const.Ico monotone_id)

theorem tendsto_measure_Ioc_atBot [NoMinOrder α] [(atBot : Filter α).IsCountablyGenerated]
    (μ : Measure α) (a : α) :
    Tendsto (fun x => μ (Ioc x a)) atBot (𝓝 (μ (Iic a))) := by
  rw [← iUnion_Ioc_left]
  exact tendsto_measure_iUnion_atBot (monotone_id.Ioc antitone_const)

theorem tendsto_measure_Iic_atTop [(atTop : Filter α).IsCountablyGenerated]
    (μ : Measure α) : Tendsto (fun x => μ (Iic x)) atTop (𝓝 (μ univ)) := by
  rw [← iUnion_Iic]
  exact tendsto_measure_iUnion_atTop monotone_Iic

theorem tendsto_measure_Ici_atBot [(atBot : Filter α).IsCountablyGenerated]
    (μ : Measure α) : Tendsto (fun x => μ (Ici x)) atBot (𝓝 (μ univ)) :=
  tendsto_measure_Iic_atTop (α := αᵒᵈ) μ

end Preorder

section PartialOrder

variable [PartialOrder α] {a b : α}

theorem Iio_ae_eq_Iic' (ha : μ {a} = 0) : Iio a =ᵐ[μ] Iic a := by
  rw [← Iic_sdiff_right, sdiff_ae_eq_self, measure_mono_null Set.inter_subset_right ha]

theorem Ioi_ae_eq_Ici' (ha : μ {a} = 0) : Ioi a =ᵐ[μ] Ici a :=
  Iio_ae_eq_Iic' (α := αᵒᵈ) ha

theorem Ioo_ae_eq_Ioc' (hb : μ {b} = 0) : Ioo a b =ᵐ[μ] Ioc a b :=
  .inter .rfl (Iio_ae_eq_Iic' hb)

theorem Ioc_ae_eq_Icc' (ha : μ {a} = 0) : Ioc a b =ᵐ[μ] Icc a b :=
  (Ioi_ae_eq_Ici' ha).inter .rfl

theorem Ioo_ae_eq_Ico' (ha : μ {a} = 0) : Ioo a b =ᵐ[μ] Ico a b :=
  (Ioi_ae_eq_Ici' ha).inter .rfl

theorem Ioo_ae_eq_Icc' (ha : μ {a} = 0) (hb : μ {b} = 0) : Ioo a b =ᵐ[μ] Icc a b :=
  (Ioi_ae_eq_Ici' ha).inter (Iio_ae_eq_Iic' hb)

theorem Ico_ae_eq_Icc' (hb : μ {b} = 0) : Ico a b =ᵐ[μ] Icc a b :=
  .inter .rfl (Iio_ae_eq_Iic' hb)

theorem Ico_ae_eq_Ioc' (ha : μ {a} = 0) (hb : μ {b} = 0) : Ico a b =ᵐ[μ] Ioc a b :=
  (Ioo_ae_eq_Ico' ha).symm.trans (Ioo_ae_eq_Ioc' hb)

end PartialOrder

end MeasureTheory
