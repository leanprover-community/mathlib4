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

theorem measure_eq_iSup_inter_Iic (μ : Measure α) (S : Set α) [IsDirectedOrder S]
    [(atTop : Filter S).IsCountablyGenerated] :
    μ S = ⨆ x ∈ S, μ (S ∩ Iic x) := by
  refine le_antisymm ?_ <| iSup₂_le fun _ _ ↦ measure_mono inter_subset_left
  rcases isEmpty_or_nonempty S with h | h
  · simp [isEmpty_coe_sort.mp h]
  have : Tendsto (fun x : S ↦ μ (S ∩ Iic x)) atTop (𝓝 (μ (⋃ x : S, S ∩ Iic x))) :=
    tendsto_measure_iUnion_atTop fun _ _ h ↦ inter_subset_inter_right _ <| Iic_subset_Iic.mpr h
  rw [le_antisymm (iUnion_subset fun _ ↦ inter_subset_left)
    fun x hx ↦ mem_iUnion.mpr ⟨⟨x, hx⟩, hx, le_rfl⟩] at this
  exact le_of_tendsto' this (le_biSup (μ <| S ∩ Iic ·) ·.property)

-- TODO: generate this using `@[to_dual]` once Monotone <-> Antitone is tagged with `@[to_dual]`
@[to_dual existing measure_eq_iSup_inter_Iic]
theorem measure_eq_iSup_inter_Ici (μ : Measure α) (S : Set α) [IsCodirectedOrder S]
    [(atBot : Filter S).IsCountablyGenerated] :
    μ S = ⨆ x ∈ S, μ (S ∩ Ici x) := by
  refine le_antisymm ?_ <| iSup₂_le fun _ _ ↦ measure_mono inter_subset_left
  rcases isEmpty_or_nonempty S with h | h
  · simp [isEmpty_coe_sort.mp h]
  have : Tendsto (fun x : S ↦ μ (S ∩ Ici x)) atBot (𝓝 (μ (⋃ x : S, S ∩ Ici x))) :=
    tendsto_measure_iUnion_atBot fun _ _ h ↦ inter_subset_inter_right _ <| Ici_subset_Ici.mpr h
  rw [le_antisymm (iUnion_subset fun _ ↦ inter_subset_left)
    fun x hx ↦ mem_iUnion.mpr ⟨⟨x, hx⟩, hx, le_rfl⟩] at this
  exact le_of_tendsto' this (le_biSup (μ <| S ∩ Ici ·) ·.property)

end Preorder

section PartialOrder

variable [PartialOrder α] {a b : α}

theorem Iio_ae_eq_Iic' (ha : μ {a} = 0) : Iio a =ᵐ[μ] Iic a := by
  rw [← Iic_sdiff_right, sdiff_ae_eq_self, measure_mono_null Set.inter_subset_right ha]

theorem Ioi_ae_eq_Ici' (ha : μ {a} = 0) : Ioi a =ᵐ[μ] Ici a :=
  Iio_ae_eq_Iic' (α := αᵒᵈ) ha

theorem Ioo_ae_eq_Ioc' (hb : μ {b} = 0) : Ioo a b =ᵐ[μ] Ioc a b :=
  .inter (.rfl (s := Ioi a)) (Iio_ae_eq_Iic' hb)

theorem Ioc_ae_eq_Icc' (ha : μ {a} = 0) : Ioc a b =ᵐ[μ] Icc a b :=
  (Ioi_ae_eq_Ici' ha).inter (.rfl (s := Iic b))

theorem Ioo_ae_eq_Ico' (ha : μ {a} = 0) : Ioo a b =ᵐ[μ] Ico a b :=
  (Ioi_ae_eq_Ici' ha).inter (.rfl (s := Iio b))

theorem Ioo_ae_eq_Icc' (ha : μ {a} = 0) (hb : μ {b} = 0) : Ioo a b =ᵐ[μ] Icc a b :=
  (Ioi_ae_eq_Ici' ha).inter (Iio_ae_eq_Iic' hb)

theorem Ico_ae_eq_Icc' (hb : μ {b} = 0) : Ico a b =ᵐ[μ] Icc a b :=
  .inter (.rfl (s := Ici a)) (Iio_ae_eq_Iic' hb)

theorem Ico_ae_eq_Ioc' (ha : μ {a} = 0) (hb : μ {b} = 0) : Ico a b =ᵐ[μ] Ioc a b :=
  (Ioo_ae_eq_Ico' ha).symm.trans (Ioo_ae_eq_Ioc' hb)

open scoped Pointwise in
/-- `μ A + μ B ≤ μ (A * B) + μ singleton` for ordered magma. -/
@[to_additive /-- `μ A + μ B ≤ μ (A + B) + μ singleton` for ordered add magma.
This is used to prove `Real.volume_add_volume_le` -/]
theorem _root_.PartialOrder.measure_add_measure_le_measure_mul_add_iSup [Mul α] [MulLeftMono α]
    [MulRightMono α] (hIic : ∀ x : α, MeasurableSet (Iic x))
    (hl : ∀ a s, μ s ≤ μ ((a * ·) '' s)) (hr : ∀ b s, μ s ≤ μ ((· * b) '' s))
    {A B : Set α} [IsDirectedOrder A] [(atTop : Filter A).IsCountablyGenerated]
    [IsCodirectedOrder B] [(atBot : Filter B).IsCountablyGenerated] (hA : A.Nonempty)
    (hB : B.Nonempty) :
    μ A + μ B ≤ μ (A * B) + ⨆ x ∈ A * B, μ {x} := by
  rw [measure_eq_iSup_inter_Iic μ A, measure_eq_iSup_inter_Ici μ B]
  refine ENNReal.biSup_add_biSup_le hA hB fun a ha b hb ↦ ?_
  calc
    _ ≤ μ ((· * b) '' (A ∩ Iic a)) + μ ((a * ·) '' (B ∩ Ici b)) := by
      gcongr 1
      · apply hr b
      · apply hl a
    _ ≤ μ (A * B ∩ Iic (a * b)) + μ ((A * B) \ Iio (a * b)) := by
      gcongr
      · rintro _ ⟨x, ⟨hx, hxa⟩, rfl⟩
        exact ⟨mul_mem_mul hx hb, mul_le_mul_left hxa b⟩
      · rintro _ ⟨y, ⟨hy, hyb⟩, rfl⟩
        refine ⟨mul_mem_mul ha hy, (mul_le_mul_right hyb a).not_gt⟩
    _ ≤ μ (A * B ∩ Iic (a * b)) + μ ((A * B) \ Iic (a * b)) + μ {a * b} := by
      grw [add_assoc, ← measure_union_le _ {a * b}, ← Set.sdiff_sdiff_eq_sdiff_union ?_,
        Set.Iic_sdiff_right]
      simpa using Set.mul_mem_mul ha hb
    _ ≤ _ := by
      grw [measure_inter_add_sdiff _ (hIic _), le_biSup (μ {·}) (Set.mul_mem_mul ha hb)]

end PartialOrder

end MeasureTheory
