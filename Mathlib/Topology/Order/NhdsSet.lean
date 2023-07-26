/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Topology.Order.Basic

/-!
# Set neighborhoods of intervals

In this file we prove basic theorems about `𝓝ˢ s`,
where `s` is one of the intervals
`Set.Ici`, `Set.Iic`, `Set.Ioi`, `Set.Iio`, `Set.Ico`, `Set.Ioc`, `Set.Ioo`, and `Set.Icc`.

First, we prove lemmas in terms of filter equalities,
then we prove lemmas about `s ∈ 𝓝ˢ t`, where both `s` and `t` are intervals.
-/


open Set Filter OrderDual
open scoped Topology

variable {α : Type _} [LinearOrder α] [TopologicalSpace α] [OrderClosedTopology α] {a b c d : α}

/-!
# Formulae for `𝓝ˢ` of intervals
-/

@[simp] theorem nhdsSet_Ioi : 𝓝ˢ (Ioi a) = 𝓟 (Ioi a) := isOpen_Ioi.nhdsSet_eq
@[simp] theorem nhdsSet_Iio : 𝓝ˢ (Iio a) = 𝓟 (Iio a) := isOpen_Iio.nhdsSet_eq
@[simp] theorem nhdsSet_Ioo : 𝓝ˢ (Ioo a b) = 𝓟 (Ioo a b) := isOpen_Ioo.nhdsSet_eq

theorem nhdsSet_Ici : 𝓝ˢ (Ici a) = 𝓝 a ⊔ 𝓟 (Ioi a) := by
  rw [← Ioi_insert, nhdsSet_insert, nhdsSet_Ioi]

theorem nhdsSet_Iic : 𝓝ˢ (Iic a) = 𝓝 a ⊔ 𝓟 (Iio a) := nhdsSet_Ici (α := αᵒᵈ)

theorem nhdsSet_Ico (h : a < b) : 𝓝ˢ (Ico a b) = 𝓝 a ⊔ 𝓟 (Ioo a b) := by
  rw [← Ioo_insert_left h, nhdsSet_insert, nhdsSet_Ioo]

theorem nhdsSet_Ioc (h : a < b) : 𝓝ˢ (Ioc a b) = 𝓝 b ⊔ 𝓟 (Ioo a b) := by
  rw [← Ioo_insert_right h, nhdsSet_insert, nhdsSet_Ioo]

theorem nhdsSet_Icc (h : a ≤ b) : 𝓝ˢ (Icc a b) = 𝓝 a ⊔ 𝓝 b ⊔ 𝓟 (Ioo a b) := by
  rcases h.eq_or_lt with rfl | hlt
  · simp
  · rw [← Ioc_insert_left h, nhdsSet_insert, nhdsSet_Ioc hlt, sup_assoc]

/-!
### Lemmas about `Ixi _ ∈ 𝓝ˢ (Set.Ici _)`
-/

@[simp]
theorem Ioi_mem_nhdsSet_Ici : Ioi a ∈ 𝓝ˢ (Ici b) ↔ a < b := by
  refine ⟨(Ici_subset_Ioi.1 <| principal_le_nhdsSet ·), fun h ↦ ?_⟩
  rw [nhdsSet_Ici]
  exact ⟨Ioi_mem_nhds h, Ioi_subset_Ioi h.le⟩

theorem Ici_mem_nhdsSet_Ici (h : a < b) : Ici a ∈ 𝓝ˢ (Ici b) :=
  mem_of_superset (Ioi_mem_nhdsSet_Ici.2 h) Ioi_subset_Ici_self

/-!
### Lemmas about `Iix _ ∈ 𝓝ˢ (Set.Iic _)`
-/

theorem Iio_mem_nhdsSet_Iic : Iio b ∈ 𝓝ˢ (Iic a) ↔ a < b :=
  Ioi_mem_nhdsSet_Ici (α := αᵒᵈ)

theorem Iic_mem_nhdsSet_Iic (h : a < b) : Iic b ∈ 𝓝ˢ (Iic a) :=
  Ici_mem_nhdsSet_Ici (α := αᵒᵈ) h

/-!
### Lemmas about `Ixx _ _? ∈ 𝓝ˢ (Set.Icc _ _)`
-/

theorem Ioi_mem_nhdsSet_Icc (h : a < b) : Ioi a ∈ 𝓝ˢ (Icc b c) := by
  cases le_or_lt b c with
  | inl hbc =>
    rw [nhdsSet_Icc hbc]
    exact ⟨⟨Ioi_mem_nhds h, Ioi_mem_nhds (h.trans_le hbc)⟩,
      Ioo_subset_Ioi_self.trans <| Ioi_subset_Ioi h.le⟩
  | inr hcb => simp [Icc_eq_empty_of_lt hcb]

theorem Ici_mem_nhdsSet_Icc (h : a < b) : Ici a ∈ 𝓝ˢ (Icc b c) :=
  mem_of_superset (Ioi_mem_nhdsSet_Icc h) Ioi_subset_Ici_self

theorem Iio_mem_nhdsSet_Icc (h : b < c) : Iio c ∈ 𝓝ˢ (Icc a b) :=
  have : Iio c ∈ 𝓝ˢ (toDual ⁻¹' (Icc (toDual b) (toDual a))) :=
    Ioi_mem_nhdsSet_Icc (α := αᵒᵈ) h
  by rwa [dual_Icc] at this

theorem Iic_mem_nhdsSet_Icc (h : b < c) : Iic c ∈ 𝓝ˢ (Icc a b) :=
  mem_of_superset (Iio_mem_nhdsSet_Icc h) Iio_subset_Iic_self

theorem Ioo_mem_nhdsSet_Icc (h : a < b) (h' : c < d) : Ioo a d ∈ 𝓝ˢ (Icc b c) :=
  inter_mem (Ioi_mem_nhdsSet_Icc h) (Iio_mem_nhdsSet_Icc h')

theorem Ico_mem_nhdsSet_Icc (h : a < b) (h' : c < d) : Ico a d ∈ 𝓝ˢ (Icc b c) :=
  inter_mem (Ici_mem_nhdsSet_Icc h) (Iio_mem_nhdsSet_Icc h')

theorem Ioc_mem_nhdsSet_Icc (h : a < b) (h' : c < d) : Ioc a d ∈ 𝓝ˢ (Icc b c) :=
  inter_mem (Ioi_mem_nhdsSet_Icc h) (Iic_mem_nhdsSet_Icc h')

theorem Icc_mem_nhdsSet_Icc (h : a < b) (h' : c < d) : Icc a d ∈ 𝓝ˢ (Icc b c) :=
  inter_mem (Ici_mem_nhdsSet_Icc h) (Iic_mem_nhdsSet_Icc h')

/-!
### Lemmas about `Ixx _ _? ∈ 𝓝ˢ (Set.Ico _ _)`
-/

theorem Ici_mem_nhdsSet_Ico (h : a < b) : Ici a ∈ 𝓝ˢ (Ico b c) :=
  nhdsSet_mono Ico_subset_Icc_self <| Ici_mem_nhdsSet_Icc h

theorem Ioi_mem_nhdsSet_Ico (h : a < b) : Ioi a ∈ 𝓝ˢ (Ico b c) :=
  nhdsSet_mono Ico_subset_Icc_self <| Ioi_mem_nhdsSet_Icc h

theorem Iio_mem_nhdsSet_Ico (h : b ≤ c) : Iio c ∈ 𝓝ˢ (Ico a b) :=
  nhdsSet_mono Ico_subset_Iio_self <| by simpa

theorem Iic_mem_nhdsSet_Ico (h : b ≤ c) : Iic c ∈ 𝓝ˢ (Ico a b) :=
  mem_of_superset (Iio_mem_nhdsSet_Ico h) Iio_subset_Iic_self

theorem Ioo_mem_nhdsSet_Ico (h : a < b) (h' : c ≤ d) : Ioo a d ∈ 𝓝ˢ (Ico b c) :=
  inter_mem (Ioi_mem_nhdsSet_Ico h) (Iio_mem_nhdsSet_Ico h')

theorem Icc_mem_nhdsSet_Ico (h : a < b) (h' : c ≤ d) : Icc a d ∈ 𝓝ˢ (Ico b c) :=
  inter_mem (Ici_mem_nhdsSet_Ico h) (Iic_mem_nhdsSet_Ico h')

theorem Ioc_mem_nhdsSet_Ico (h : a < b) (h' : c ≤ d) : Ioc a d ∈ 𝓝ˢ (Ico b c) :=
  inter_mem (Ioi_mem_nhdsSet_Ico h) (Iic_mem_nhdsSet_Ico h')

theorem Ico_mem_nhdsSet_Ico (h : a < b) (h' : c ≤ d) : Ico a d ∈ 𝓝ˢ (Ico b c) :=
  inter_mem (Ici_mem_nhdsSet_Ico h) (Iio_mem_nhdsSet_Ico h')

/-!
### Lemmas about `Ixx _ _? ∈ 𝓝ˢ (Set.Ioc _ _)`
-/

theorem Ioi_mem_nhdsSet_Ioc (h : a ≤ b) : Ioi a ∈ 𝓝ˢ (Ioc b c) :=
  nhdsSet_mono Ioc_subset_Ioi_self <| by simpa

theorem Iio_mem_nhdsSet_Ioc (h : b < c) : Iio c ∈ 𝓝ˢ (Ioc a b) :=
  nhdsSet_mono Ioc_subset_Icc_self <| Iio_mem_nhdsSet_Icc h

theorem Ici_mem_nhdsSet_Ioc (h : a ≤ b) : Ici a ∈ 𝓝ˢ (Ioc b c) :=
  mem_of_superset (Ioi_mem_nhdsSet_Ioc h) Ioi_subset_Ici_self

theorem Iic_mem_nhdsSet_Ioc (h : b < c) : Iic c ∈ 𝓝ˢ (Ioc a b) :=
  nhdsSet_mono Ioc_subset_Icc_self <| Iic_mem_nhdsSet_Icc h

theorem Ioo_mem_nhdsSet_Ioc (h : a ≤ b) (h' : c < d) : Ioo a d ∈ 𝓝ˢ (Ioc b c) :=
  inter_mem (Ioi_mem_nhdsSet_Ioc h) (Iio_mem_nhdsSet_Ioc h')

theorem Icc_mem_nhdsSet_Ioc (h : a ≤ b) (h' : c < d) : Icc a d ∈ 𝓝ˢ (Ioc b c) :=
  inter_mem (Ici_mem_nhdsSet_Ioc h) (Iic_mem_nhdsSet_Ioc h')

theorem Ioc_mem_nhdsSet_Ioc (h : a ≤ b) (h' : c < d) : Ioc a d ∈ 𝓝ˢ (Ioc b c) :=
  inter_mem (Ioi_mem_nhdsSet_Ioc h) (Iic_mem_nhdsSet_Ioc h')

theorem Ico_mem_nhdsSet_Ioc (h : a ≤ b) (h' : c < d) : Ico a d ∈ 𝓝ˢ (Ioc b c) :=
  inter_mem (Ici_mem_nhdsSet_Ioc h) (Iio_mem_nhdsSet_Ioc h')
