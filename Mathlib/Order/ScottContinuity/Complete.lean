/-
Copyright (c) 2025 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Order.ScottContinuity.Prod

/-!

# Scott continuity on complete lattices

## Main results

- `scottContinuous_iff_map_sSup`: A function is Scott continuous if and only if it commutes with
  `sSup` on directed sets.

-/

variable {α β : Type*}

section CompleteLattice

variable [CompleteLattice α] [CompleteLattice β]

/- `f` is Scott continuous if and only if it commutes with `sSup` on directed sets -/
lemma scottContinuous_iff_map_sSup {f : α → β} : ScottContinuous f ↔
    ∀ ⦃d : Set α⦄, d.Nonempty → DirectedOn (· ≤ ·) d → f (sSup d) = sSup (f '' d) :=
  ⟨fun h _ d₁ d₂ => by rw [IsLUB.sSup_eq (h d₁ d₂ (isLUB_iff_sSup_eq.mpr rfl))],
    fun h _ d₁ d₂ _ hda => by rw [isLUB_iff_sSup_eq, ← (h d₁ d₂), IsLUB.sSup_eq hda]⟩

alias ⟨ScottContinuous.map_sSup, ScottContinuous.of_map_sSup⟩ :=
  scottContinuous_iff_map_sSup

end CompleteLattice

/- In a complete linear order, the Scott Topology coincides with the Upper topology, see
`Topology.IsScott.scott_eq_upper_of_completeLinearOrder` -/
section CompleteLinearOrder

variable [CompleteLinearOrder β]

lemma inf_sSup_eq_sSup_map   (a : β) (d : Set β) :
    a ⊓ sSup d = sSup ((fun b ↦ a ⊓ b) '' d) := eq_of_forall_ge_iff fun _ => by
  simp only [inf_le_iff, sSup_le_iff, ← forall_or_left, Set.mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]

lemma sSup_inf_eq_sSup_map (b : β) (d : Set β) :
    sSup d ⊓ b = sSup ((fun a ↦ a ⊓ b) '' d) := eq_of_forall_ge_iff fun _ => by
  simp [inf_le_iff, sSup_le_iff, ← forall_or_right, Set.mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]

lemma scottContinuous_inf_right (a : β) : ScottContinuous fun b ↦ a ⊓ b := by
  refine ScottContinuous.of_map_sSup (fun d _ _ ↦ by rw [inf_sSup_eq_sSup_map])

lemma scottContinuous_inf_left (b : β) : ScottContinuous fun a ↦ a ⊓ b := by
  refine ScottContinuous.of_map_sSup (fun d _ _ ↦ by rw [sSup_inf_eq_sSup_map])

/- The meet operation is Scott continuous -/
lemma ScottContinuous.inf₂ : ScottContinuous fun (a, b) => (a ⊓ b : β) :=
  ScottContinuous_prod_of_ScottContinuous scottContinuous_inf_right right_cont_inf

end CompleteLinearOrder
