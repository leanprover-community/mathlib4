/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, Anatole Dedecker
-/
module

public import Mathlib.Topology.Semicontinuous

/-! # Two lemmas about sublevel sets and semicontinuity related to compactness

* `LowerSemicontinuousOn.isCompact_inter_preimage_Iic`, the sublevels
  of a lower semicontinuous function on a compact set are compact.

* `LowerSemicontinuousOn.inter_biInter_preimage_Iic_eq_empty_iff_exists_finset`, an intersection
  of sublevel sets of a lower semicontinuous function on a compact set
  is empty if and only if a finite sub-intersection is already empty.

-/

@[expose] public section

open Function Set

namespace LowerSemicontinuousOn

open scoped Set.Notation
variable {ι α β : Type*} [TopologicalSpace α] {A : Set α}
    [LinearOrder β] {f : ι → α → β}

theorem isCompact_inter_preimage_Iic {f : α → β}
    (hfA : LowerSemicontinuousOn f A) (kA : IsCompact A) (b : β) :
    IsCompact (A ∩ f ⁻¹' Iic b) := by
  rw [lowerSemicontinuousOn_iff_preimage_Iic] at hfA
  obtain ⟨v, hv, hv'⟩ := hfA b
  exact hv' ▸ kA.inter_right hv

theorem inter_biInter_preimage_Iic_eq_empty_iff_exists_finset
    (kA : IsCompact A) {I : Set ι} {b : β} (hfi : ∀ i ∈ I, LowerSemicontinuousOn (f i) A) :
    A ∩ ⋂ i ∈ I, (f i) ⁻¹' Iic b = ∅ ↔ ∃ u : Finset I, ∀ x ∈ A, ∃ i ∈ u, b < f i x := by
  refine ⟨fun H ↦ ?_, fun ⟨u, hu⟩ ↦ ?_⟩
  · suffices ∀ i ∈ I, IsClosed (A ↓∩ (fun i ↦ f i ⁻¹' Iic b) i) by
      simpa [Set.eq_empty_iff_forall_notMem] using
        kA.elim_finite_subfamily_isClosed_subtype _ this H
    exact fun i hi ↦ lowerSemicontinuous_restrict_iff.mpr (hfi i hi) |>.isClosed_preimage b
  · rw [Set.eq_empty_iff_forall_notMem]
    simp only [mem_inter_iff, mem_iInter, mem_preimage, mem_Iic, not_and, not_forall,
      exists_prop, not_le]
    simp only [Subtype.exists, exists_and_right] at hu
    grind

end LowerSemicontinuousOn
