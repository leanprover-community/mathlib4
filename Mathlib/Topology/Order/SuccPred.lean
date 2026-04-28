/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux, Violeta Hernández Palacios
-/
module

public import Mathlib.Topology.Order.Basic
public import Mathlib.Order.SuccPred.Limit

/-!
# Order topologies of successor or predecessor orders

This file proves miscellaneous results under the assumption of `OrderTopology` plus either of
`SuccOrder` or `PredOrder`.
-/

public section

variable {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
  {a : α} {s : Set α}

open Order Topology

namespace SuccOrder
variable [SuccOrder α]

@[to_dual]
theorem isOpen_singleton_of_not_isSuccPrelimit (ha : ¬ IsSuccPrelimit a) : IsOpen {a} := by
  obtain ⟨b, hb⟩ := not_isSuccPrelimit_iff_exists_covBy a |>.mp ha
  by_cases ha' : IsMax a
  · convert isOpen_Ioi (a := b) using 1
    rw [hb.Ioi_eq]
    grind [IsMax]
  · convert isOpen_Ioo (a := b) (b := Order.succ a) using 1
    simp [(covBy_succ_of_not_isMax ha').Ioo_eq_Ioc, hb.Ioc_eq]

variable [NoMaxOrder α]

theorem isOpen_singleton_iff : IsOpen {a} ↔ ¬ IsSuccLimit a := by
  nontriviality α
  refine ⟨fun h ha ↦ ?_, fun ha ↦ ?_⟩
  · obtain ⟨l, u, h₁, h₂⟩ := mem_nhds_iff_exists_Ioo_subset' (by simpa using ha.not_isMin)
      (by simpa only [not_isMax_iff] using not_isMax a) |>.mp (h.mem_nhds (Set.mem_singleton a))
    refine ha.isSuccPrelimit l ?_
    rw [← succ_eq_iff_covBy]
    simp only [Set.mem_Ioo, Set.subset_singleton_iff] at h₁ h₂
    exact h₂ _ ⟨lt_succ l, h₁.1.succ_le.trans_lt h₁.2⟩
  · obtain (ha | ha) := not_isSuccLimit_iff.mp ha
    · convert isOpen_Iio (a := Order.succ a) using 1
      simp [ha.Iic_eq]
    · exact isOpen_singleton_of_not_isSuccPrelimit ha

-- TODO: generate this automatically
@[to_dual existing]
theorem _root_.PredOrder.isOpen_singleton_iff {α}
    [LinearOrder α] [TopologicalSpace α] [OrderTopology α] {a : α} [PredOrder α] [NoMinOrder α] :
    IsOpen {a} ↔ ¬ IsPredLimit a :=
  (SuccOrder.isOpen_singleton_iff (α := αᵒᵈ)).trans isSuccLimit_toDual_iff.not

@[to_dual]
theorem nhds_eq_pure {a : α} : 𝓝 a = pure a ↔ ¬ IsSuccLimit a :=
  (isOpen_singleton_iff_nhds_eq_pure _).symm.trans isOpen_singleton_iff

@[to_dual]
theorem isOpen_iff {s : Set α} : IsOpen s ↔
    ∀ o ∈ s, IsSuccLimit o → ∃ a < o, Set.Ioo a o ⊆ s := by
  refine isOpen_iff_mem_nhds.trans <| forall₂_congr fun o ho ↦ ?_
  by_cases ho' : IsSuccLimit o
  · rw [(SuccOrder.hasBasis_nhds_Ioc_of_exists_lt (not_isMin_iff.1 ho'.not_isMin)).mem_iff]
    grind
  · simp [nhds_eq_pure.2 ho', ho, ho']

@[to_dual]
theorem isSuccLimit_of_mem_frontier {a : α} {s : Set α} (ha : a ∈ frontier s) : IsSuccLimit a := by
  rw [← isOpen_singleton_iff.not_left]
  rw [frontier_eq_closure_inter_closure] at ha
  grind [mem_closure_iff, Set.Nonempty]

end SuccOrder
