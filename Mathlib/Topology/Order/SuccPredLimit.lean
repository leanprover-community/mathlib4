/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Topology.Order.IsLUB
import Mathlib.Order.SuccPred.Limit

open Set Filter
open scoped Topology

variable {X : Type*} [LinearOrder X] [TopologicalSpace X] [OrderTopology X]
  {s : Set X} {a b : X}

namespace Order.IsSuccPrelimit

theorem comap_coe_nhdsWithin_Iio_of_Ioo_subset (hb : IsSuccPrelimit b) (hsb : s ⊆ Iio b)
    (hs : s.Nonempty → ∃ a < b, Ioo a b ⊆ s) : comap ((↑) : s → X) (𝓝[<] b) = atTop := by
  nontriviality
  haveI : Nonempty s := nontrivial_iff_nonempty.1 ‹_›
  rcases hs (nonempty_subtype.1 ‹_›) with ⟨a, h, hs⟩
  ext u; constructor
  · rintro ⟨t, ht, hts⟩
    obtain ⟨x, ⟨hxa : a ≤ x, hxb : x < b⟩, hxt : Ioo x b ⊆ t⟩ :=
      (mem_nhdsWithin_Iio_iff_exists_mem_Ico_Ioo_subset h).mp ht
    obtain ⟨y, hyb, hxy⟩ := hb.lt_iff_exists_lt.mp hxb
    refine mem_of_superset (mem_atTop ⟨y, hs ⟨hxa.trans_lt hxy, hyb⟩⟩) ?_
    rintro ⟨z, hzs⟩ (hyz : y ≤ z)
    exact hts (hxt ⟨hxy.trans_le hyz, hsb hzs⟩)
  · intro hu
    obtain ⟨x : s, hx : ∀ z, x ≤ z → z ∈ u⟩ := mem_atTop_sets.1 hu
    exact ⟨Ioo x b, Ioo_mem_nhdsWithin_Iio' (hsb x.2), fun z hz => hx _ hz.1.le⟩

theorem map_coe_atTop_of_Ioo_subset (hb : IsSuccPrelimit b) (hsb : s ⊆ Iio b)
    (hs : (Iio b).Nonempty → ∃ a < b, Ioo a b ⊆ s) : map ((↑) : s → X) atTop = 𝓝[<] b := by
  rcases eq_empty_or_nonempty (Iio b) with hbe | hbe
  · have : IsEmpty s := ⟨fun x => hbe.subset (hsb x.2)⟩
    rw [filter_eq_bot_of_isEmpty atTop, Filter.map_bot, hbe, nhdsWithin_empty]
  · rw [← hb.comap_coe_nhdsWithin_Iio_of_Ioo_subset hsb fun _ => hs hbe, map_comap_of_mem]
    rw [Subtype.range_val]
    let ⟨a, ha⟩ := hbe
    exact (mem_nhdsWithin_Iio_iff_exists_Ioo_subset' ha).2 (hs hbe)

/-- The `atTop` filter for an open interval `Ioo a b` comes from the left-neighbourhoods filter at
the right endpoint in the ambient order. -/
theorem comap_coe_Ioo_nhdsWithin_Iio (hb : IsSuccPrelimit b) (a : X) :
    comap ((↑) : Ioo a b → X) (𝓝[<] b) = atTop :=
  hb.comap_coe_nhdsWithin_Iio_of_Ioo_subset Ioo_subset_Iio_self fun ⟨_c, hac, hcb⟩ ↦
    ⟨a, hac.trans hcb, Subset.rfl⟩

theorem comap_coe_Iio_nhdsWithin_Iio (ha : IsSuccPrelimit a) :
    comap ((↑) : Iio a → X) (𝓝[<] a) = atTop :=
  ha.comap_coe_nhdsWithin_Iio_of_Ioo_subset Subset.rfl fun ⟨b, hb⟩ ↦ ⟨b, hb, Ioo_subset_Iio_self⟩

/-- The `atBot` filter for an open interval `Ioo a b` comes from the right-neighbourhoods filter at
the left endpoint in the ambient order. -/
theorem comap_coe_Ioo_nhdsWithin_Ioi (a b : α) : comap ((↑) : Ioo a b → α) (𝓝[>] a) = atBot :=
  comap_coe_nhdsWithin_Ioi_of_Ioo_subset Ioo_subset_Ioi_self fun h =>
    ⟨b, nonempty_Ioo.1 h, Subset.refl _⟩

theorem comap_coe_Ioi_nhdsWithin_Ioi (a : α) : comap ((↑) : Ioi a → α) (𝓝[>] a) = atBot :=
  comap_coe_nhdsWithin_Ioi_of_Ioo_subset (Subset.refl _) fun ⟨x, hx⟩ => ⟨x, hx, Ioo_subset_Ioi_self⟩

@[simp]
theorem map_coe_Ioo_atTop {a b : α} (h : a < b) : map ((↑) : Ioo a b → α) atTop = 𝓝[<] b :=
  map_coe_atTop_of_Ioo_subset Ioo_subset_Iio_self fun _ _ => ⟨_, h, Subset.refl _⟩

@[simp]
theorem map_coe_Ioo_atBot {a b : α} (h : a < b) : map ((↑) : Ioo a b → α) atBot = 𝓝[>] a :=
  map_coe_atBot_of_Ioo_subset Ioo_subset_Ioi_self fun _ _ => ⟨_, h, Subset.refl _⟩

@[simp]
theorem map_coe_Ioi_atBot (a : α) : map ((↑) : Ioi a → α) atBot = 𝓝[>] a :=
  map_coe_atBot_of_Ioo_subset (Subset.refl _) fun b hb => ⟨b, hb, Ioo_subset_Ioi_self⟩

@[simp]
theorem map_coe_Iio_atTop (a : α) : map ((↑) : Iio a → α) atTop = 𝓝[<] a :=
  map_coe_Ioi_atBot (α := αᵒᵈ) _


end Order.IsSuccPrelimit

namespace Order.IsPredPrelimit

theorem comap_coe_nhdsWithin_Ioi_of_Ioo_subset (hb : IsPredPrelimit b) (hsb : s ⊆ Ioi b)
    (hs : s.Nonempty → ∃ a > b, Ioo b a ⊆ s) : comap ((↑) : s → X) (𝓝[>] b) = atBot := by
  refine hb.dual.comap_coe_nhdsWithin_Iio_of_Ioo_subset hsb fun hne ↦ ?_
  rcases hs hne with ⟨a, hab, ha⟩
  use OrderDual.toDual a, hab
  rwa [Set.dual_Ioo]

theorem map_coe_atBot_of_Ioo_subset (hb : IsPredPrelimit b) (hsb : s ⊆ Ioi b)
    (hs : (Ioi b).Nonempty → ∃ a > b, Ioo b a ⊆ s) : map ((↑) : s → X) atBot = 𝓝[>] b := by
  refine hb.dual.map_coe_atTop_of_Ioo_subset hsb fun h ↦ ?_
  rcases hs h with ⟨a, hab, ha⟩
  use OrderDual.toDual a, hab
  rwa [Set.dual_Ioo]

end Order.IsPredPrelimit
