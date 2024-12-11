/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/

import Mathlib.Topology.Algebra.Nonarchimedean.Bases

/-! # Linear topologies on rings

Following Bourbaki, *Algebra II*, chapter 4, §2, n° 3, a topology on a ring `R` is *linear* if
it is invariant by translation and there admits a basis of neighborhoods of 0 consisting of
two-sided ideals.

- `LinearTopology.tendsto_zero_mul`: for `f, g : ι → R` such that `f i` converges to `0`,
`f i * g i` converges to `0`.

TODO. For the moment, it is only done on commutative rings.

-/

section Definition

variable (α : Type*) [CommRing α]

/-- A topology on a ring is linear if its topology is defined by a family of ideals. -/
class LinearTopology [TopologicalSpace α] [TopologicalRing α] where
  isLinearTopology : (nhds (0 : α)).HasBasis
    (fun I : Ideal α ↦ IsOpen (I : Set α)) (fun I : Ideal α ↦ (I : Set α))

end Definition

namespace LinearTopology

variable {α : Type*} [CommRing α] [TopologicalSpace α] [TopologicalRing α] [LinearTopology α]

theorem mem_nhds_zero_iff (s : Set α) :
    (s ∈ nhds 0) ↔
    (∃ I : Ideal α, ((I : Set α) ∈ nhds 0) ∧ (I : Set α) ⊆ s) := by
  rw [isLinearTopology.mem_iff]
  apply exists_congr
  intro I
  apply and_congr_left
  intro hI
  rw [isOpen_iff_nhds]
  constructor
  · exact fun hI' ↦ hI' 0 I.zero_mem fun ⦃_⦄ a ↦ a
  · intro hI' x hx s hs
    rw [Filter.mem_principal] at hs
    rw [← vadd_mem_nhds_vadd_iff (-x)]
    simp only [vadd_eq_add, neg_add_cancel]
    apply Filter.mem_of_superset hI'
    intro y hy
    rw [Set.mem_neg_vadd_set_iff]
    exact hs (add_mem hx hy)

theorem tendsto_zero_mul {ι : Type*} {f : Filter ι}
    (a b : ι → α) (hb : Filter.Tendsto b f (nhds 0)) :
    Filter.Tendsto (a * b) f (nhds 0) := by
  intro v hv
  obtain ⟨I, I_mem, I_le⟩ := (LinearTopology.mem_nhds_zero_iff _).mp hv
  apply Filter.sets_of_superset _ _ I_le
  simp only [Filter.mem_sets, Filter.mem_map]
  rw [Filter.tendsto_def] at hb
  exact Filter.sets_of_superset _ (hb _ I_mem) (fun x hx ↦ Ideal.mul_mem_left _ _ hx)

end LinearTopology
