/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos Fernández
-/

import Mathlib.Topology.Algebra.LinearTopology

/-! # Topologicall nilpotent elements -/

def IsTopologicallyNilpotent
  {α : Type*} [Semiring α] [TopologicalSpace α] (a : α) : Prop :=
    Filter.Tendsto (fun n : ℕ => a ^ n) Filter.atTop (nhds 0)

namespace IsTopologicallyNilpotent

theorem map {α β : Type*} [CommRing α] [CommRing β] [TopologicalSpace α] [TopologicalSpace β]
  {φ : α →+* β} (hφ : Continuous φ) {a : α} (ha : IsTopologicallyNilpotent a) :
  IsTopologicallyNilpotent (φ a) := by
  unfold IsTopologicallyNilpotent at ha ⊢
  simp_rw [← map_pow]
  apply Filter.Tendsto.comp _ ha
  convert hφ.tendsto 0; rw [map_zero]

theorem mul_right {α : Type*} [CommRing α] [TopologicalSpace α] [LinearTopology α] {a : α}
    (ha : IsTopologicallyNilpotent a) (b : α) : IsTopologicallyNilpotent (a * b) := by
  intro v hv
  rw [LinearTopology.mem_nhds_zero_iff] at hv
  rcases hv with ⟨I, _, I_mem_nhds, I_subset⟩
  specialize ha I_mem_nhds
  simp only [Filter.mem_map, Filter.mem_atTop_sets, ge_iff_le, Set.mem_preimage, SetLike.mem_coe] at ha ⊢
  rcases ha with ⟨n, ha⟩
  use n
  intro m hm
  rw [mul_pow]
  apply I_subset
  apply I.mul_mem_right _ (ha m hm)

 theorem mul_left {α : Type*} [CommRing α] [TopologicalSpace α] [LinearTopology α] (a : α) {b : α}
    (hb : IsTopologicallyNilpotent b) : IsTopologicallyNilpotent (a * b) := by
  rw [mul_comm]; exact mul_right hb a

theorem add {α : Type*} [CommRing α] [TopologicalSpace α] [LinearTopology α] {a b : α}
    (ha : IsTopologicallyNilpotent a) (hb : IsTopologicallyNilpotent b) :
    IsTopologicallyNilpotent (a + b) := by
  intro v hv
  rw [LinearTopology.mem_nhds_zero_iff] at hv
  rcases hv with ⟨I, _, I_mem_nhds, I_subset⟩
  specialize ha I_mem_nhds
  specialize hb I_mem_nhds
  simp only [Filter.mem_map, Filter.mem_atTop_sets, ge_iff_le,
    Set.mem_preimage, SetLike.mem_coe] at ha hb
  rcases ha with ⟨na, ha⟩
  rcases hb with ⟨nb, hb⟩
  simp only [Filter.mem_map, Filter.mem_atTop_sets, ge_iff_le, Set.mem_preimage]
  use na + nb
  intro m hm
  apply I_subset
  apply I.add_pow_mem_of_pow_mem_of_le (ha na le_rfl) (hb nb le_rfl)
  apply le_trans hm (Nat.le_add_right _ _)

theorem zero {α : Type*} [CommRing α] [TopologicalSpace α] :
  IsTopologicallyNilpotent (0 : α) := tendsto_atTop_of_eventually_const (i₀ := 1)
    (fun _ hi => by rw [zero_pow (Nat.ne_zero_iff_zero_lt.mpr hi)])

end IsTopologicallyNilpotent
