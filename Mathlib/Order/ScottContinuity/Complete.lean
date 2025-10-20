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
lemma scottContinuous_iff_map_sSup {f : α → β} :
    ScottContinuous f ↔
      ∀ ⦃d : Set α⦄, d.Nonempty → DirectedOn (· ≤ ·) d → f (sSup d) = sSup (f '' d) where
  mp h _ d₁ d₂ := by rw [IsLUB.sSup_eq (h d₁ d₂ (isLUB_iff_sSup_eq.mpr rfl))]
  mpr h _ d₁ d₂ _ hda := by rw [isLUB_iff_sSup_eq, ← (h d₁ d₂), IsLUB.sSup_eq hda]

alias ⟨ScottContinuous.map_sSup, ScottContinuous.of_map_sSup⟩ :=
  scottContinuous_iff_map_sSup

end CompleteLattice

/-!
In a complete linear order, the Scott Topology coincides with the Upper topology, see
`Topology.IsScott.scott_eq_upper_of_completeLinearOrder`
-/

section CompleteLinearOrder

variable [CompleteLinearOrder β]

lemma scottContinuous_inf_right (a : β) : ScottContinuous fun b ↦ a ⊓ b :=
  .of_map_sSup (fun d _ _ ↦ by rw [inf_sSup_eq, sSup_image])

lemma scottContinuous_inf_left (b : β) : ScottContinuous fun a ↦ a ⊓ b :=
  .of_map_sSup (fun d _ _ ↦ by rw [sSup_inf_eq, sSup_image])

/- The meet operation is Scott continuous -/
lemma ScottContinuous.inf₂ : ScottContinuous fun (a, b) => (a ⊓ b : β) :=
  ScottContinuous.fromProd (fun a => scottContinuous_inf_right a) scottContinuous_inf_left

end CompleteLinearOrder
