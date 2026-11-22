/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux, Violeta Hernández Palacios
-/
module

public import Mathlib.Order.SuccPred.Limit
public import Mathlib.Topology.Order.Basic

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Order topologies of successor or predecessor orders

This file proves miscellaneous results under the assumption of `OrderTopology` plus either of
`SuccOrder` or `PredOrder`.
-/

public section

variable {α : Type*} [LinearOrder α] [TopologicalSpace α] {a b : α} {s : Set α}

open Filter Order Set

open scoped Topology

namespace SuccOrder
variable [SuccOrder α]

@[to_dual]
theorem isOpen_Iic [ClosedIciTopology α] : IsOpen (Iic a) := by
  by_cases ha : IsMax a
  · rw [ha.isTop.Iic_eq]
    exact isOpen_univ
  · rw [← (covBy_succ_of_not_isMax ha).Iio_eq]
    exact isOpen_Iio

variable [OrderTopology α]

@[to_dual]
theorem isOpen_Ioc : IsOpen (Ioc a b) := by
  rw [← Ioi_inter_Iic]
  exact isOpen_Ioi.inter isOpen_Iic

/-- In a successor order, limit points correspond to limit successors. -/
@[to_dual
/-- In a predecessor order, limit points correspond to limit predecessors. -/]
theorem isOpen_singleton_iff : IsOpen {a} ↔ ¬ IsSuccLimit a := by
  refine ⟨fun h ha ↦ ?_, fun ha ↦ ?_⟩
  · obtain ⟨l, h₁, h₂⟩ := exists_Ioc_subset_of_mem_nhds (h.mem_nhds (mem_singleton a))
      (not_isMin_iff.1 ha.not_isMin)
    exact ha.isSuccPrelimit l ⟨h₁, fun b hlb hba ↦ hba.ne <| h₂ ⟨hlb, hba.le⟩⟩
  · rw [not_isSuccLimit_iff, not_isSuccPrelimit_iff] at ha
    obtain (ha | ⟨b, hb⟩) := ha
    · rw [← ha.Iic_eq]
      exact isOpen_Iic
    · rw [← hb.Ioc_eq]
      exact isOpen_Ioc

@[to_dual] alias ⟨_, isOpen_singleton_of_not_isSuccLimit⟩ := isOpen_singleton_iff

@[to_dual (attr := deprecated isOpen_singleton_of_not_isSuccLimit +typeChanged
(since := "2026-11-03"))]
theorem isOpen_singleton_of_not_isSuccPrelimit (ha : ¬ IsSuccPrelimit a) : IsOpen {a} :=
  isOpen_singleton_of_not_isSuccLimit (mt IsSuccLimit.isSuccPrelimit ha)

@[to_dual]
theorem isOpen_singleton_of_isMin (ha : IsMin a) : IsOpen {a} :=
  isOpen_singleton_of_not_isSuccLimit ha.not_isSuccLimit

@[to_dual (attr := simp)]
theorem isOpen_singleton_bot [OrderBot α] : IsOpen {(⊥ : α)} :=
  isOpen_singleton_of_isMin isMin_bot

@[to_dual]
theorem nhds_eq_pure {a : α} : 𝓝 a = pure a ↔ ¬ IsSuccLimit a :=
  (isOpen_singleton_iff_nhds_eq_pure _).symm.trans isOpen_singleton_iff

@[to_dual]
theorem nhds_of_isMin {a : α} (h : IsMin a) : 𝓝 a = pure a :=
  (isOpen_singleton_iff_nhds_eq_pure _).1 (isOpen_singleton_of_isMin h)

@[to_dual (attr := simp)]
theorem nhds_bot [OrderBot α] : 𝓝 (⊥ : α) = pure ⊥ :=
  nhds_of_isMin isMin_bot

@[to_dual]
theorem isOpen_iff {s : Set α} : IsOpen s ↔
    ∀ o ∈ s, IsSuccLimit o → ∃ a < o, Ioo a o ⊆ s := by
  refine isOpen_iff_mem_nhds.trans <| forall₂_congr fun o ho ↦ ?_
  by_cases ho' : IsSuccLimit o
  · rw [(hasBasis_nhds_Ioc_of_exists_lt (not_isMin_iff.1 ho'.not_isMin)).mem_iff]
    grind
  · simp [nhds_eq_pure.2 ho', ho, ho']

@[to_dual]
theorem accPt_principal {a : α} {s : Set α} :
    AccPt a (𝓟 s) ↔ ¬ IsMin a ∧ ∀ b < a, (s ∩ Ioo b a).Nonempty := by
  rw [accPt_iff_frequently]
  by_cases ha : IsMin a
  · simp [nhds_of_isMin, ha]
  · rw [not_isMin_iff] at ha ⊢
    simp_rw [(hasBasis_nhds_Ioc_of_exists_lt ha).frequently_iff, Set.Nonempty, mem_inter_iff]
    grind

@[to_dual]
theorem _root_.AccPt.not_isMin {a : α} {s : Set α} (h : AccPt a (𝓟 s)) : ¬ IsMin a :=
  (accPt_principal.1 h).1

@[to_dual]
theorem _root_.AccPt.isSuccLimit {a : α} {s : Set α} (h : AccPt a (𝓟 s)) : IsSuccLimit a := by
  rw [isSuccLimit_iff, IsSuccPrelimit]
  simp_rw [accPt_principal, Set.Nonempty] at h
  grind [covBy_iff_Ioo_eq]

@[to_dual]
theorem isSuccLimit_of_mem_frontier {a : α} {s : Set α} (ha : a ∈ frontier s) : IsSuccLimit a := by
  rw [← isOpen_singleton_iff.not_left]
  rw [frontier_eq_closure_inter_closure] at ha
  grind [mem_closure_iff, Set.Nonempty]

end SuccOrder
