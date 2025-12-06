/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, Anatole Dedecker
-/
module

public import Mathlib.Topology.Semicontinuous

/-! # Two lemmas about sublevels and semicontinuity related to compactness

* `Set.isCompact_leSublevelOn`, the sublevels of a lower semicontinuous function
  on a compact set are compact.

* `Set.inter_leSublevelOn_empty_iff_exists_finset_inter`,
  an intersection of sublevels of a lower semicontinuous function
  on a compact set is empty if and only if
  a finite sub-intersection is already empty.

-/

@[expose] public section

open Function Set

namespace LowerSemicontinuousOn

open scoped Set.Notation
variable {ι α β : Type*} [TopologicalSpace α] {A : Set α}
    [LinearOrder β] {f : ι → α → β}

theorem isCompact_leSublevelOn {f : α → β}
    (hfA : LowerSemicontinuousOn f A) (kA : IsCompact A) (b : β) :
    IsCompact ({x ∈ A | f x ≤ b}) := by
  rw [lowerSemicontinuousOn_iff_preimage_Iic] at hfA
  obtain ⟨v, hv, hv'⟩ := hfA b
  suffices {x | x ∈ A ∧ f x ≤ b} = A ∩ v by
    rw [this]
    exact kA.inter_right hv
  aesop

theorem inter_leSublevelOn_empty_iff_exists_finset_inter
    (kA : IsCompact A)
    {I : Set ι} (ne_I : I.Nonempty) {b : β}
    (hfi : ∀ i ∈ I, LowerSemicontinuousOn (f i) A) :
    ⋂ i ∈ I, { x ∈ A | f i x ≤ b } = ∅ ↔
      ∃ u : Finset I, ∀ x ∈ A, ∃ i ∈ u, b < f i x := by
  refine ⟨fun H ↦ ?_, fun ⟨u, hu⟩ ↦ ?_⟩
  · suffices ∃ u : Finset I, A ∩ ⋂ i ∈ u, {x | f (↑i) x ≤ b} = ∅ by
      obtain ⟨u, hu⟩ := this
      use u
      intro x hx
      rw [Set.eq_empty_iff_forall_notMem] at hu
      specialize hu x
      simp only [iInter_coe_set, mem_inter_iff, hx, mem_iInter, true_and, not_forall] at hu
      obtain ⟨i, hi, hi', hi''⟩ := hu
      use ⟨i, hi⟩, hi'
      simpa using hi''
    apply kA.elim_finite_subfamily_closedOn (fun i ↦ { x| f i x ≤ b })
    · intro i hi
      specialize hfi i hi
      rw [← lowerSemicontinuous_restrict_iff, lowerSemicontinuous_iff_isClosed_preimage] at hfi
      exact hfi b
    · rwa [← Set.inter_biInter ne_I]
  · rw [Set.eq_empty_iff_forall_notMem]
    intro x
    by_cases hx : x ∈ A
    · obtain ⟨i, hi, hi'⟩ := hu x hx
      simp only [hx, mem_iInter, not_forall, mem_setOf_eq, true_and, not_le]
      use i.val, i.prop
    · simpa [hx] using ne_I

end LowerSemicontinuousOn
