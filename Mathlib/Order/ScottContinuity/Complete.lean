/-
Copyright (c) 2025 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Order.ScottContinuity.Prod

/-!
# Scott continuity on complete lattices

## Main results

- `scottContinuous_iff_map_sSup`: A function is Scott continuous if and only if it commutes with
  `sSup` on directed sets.

-/

public section

variable {α β : Type*}

section CompleteLattice

variable [CompleteLattice α] [CompleteLattice β]

/-- A restatement of the definition of `SupScottContinuous` using `sSup`. -/
@[to_dual
/-- A restatement of the definition of `InfScottContinuous` using `sInf`. -/]
lemma supScottContinuous_iff_map_sSup {f : α → β} :
    SupScottContinuous f ↔
      ∀ ⦃d : Set α⦄, d.Nonempty → DirectedOn (· ≤ ·) d → f (sSup d) = sSup (f '' d) where
  mp h _ d₁ d₂ := by rw [IsLUB.sSup_eq (h d₁ d₂ (isLUB_iff_sSup_eq.mpr rfl))]
  mpr h _ d₁ d₂ _ hda := by rw [isLUB_iff_sSup_eq, ← (h d₁ d₂), IsLUB.sSup_eq hda]

@[deprecated (since := "2026-11-08")]
alias scottContinuous_iff_map_sSup := supScottContinuous_iff_map_sSup

@[to_dual]
alias ⟨SupScottContinuous.map_sSup, SupScottContinuous.of_map_sSup⟩ :=
  supScottContinuous_iff_map_sSup

@[deprecated (since := "2026-11-08")]
alias ScottContinuous.map_sSup := SupScottContinuous.map_sSup
@[deprecated (since := "2026-11-08")]
alias ScottContinuous.of_map_sSup := SupScottContinuous.of_map_sSup

end CompleteLattice

/-!
In a complete linear order, the Scott Topology coincides with the upper topology, see
`Topology.IsScott.scott_eq_upper_of_completeLinearOrder`
-/

section CompleteLinearOrder

variable [CompleteLinearOrder β]

@[to_dual]
lemma supScottContinuous_inf_right (a : β) : SupScottContinuous fun b ↦ a ⊓ b :=
  .of_map_sSup (fun d _ _ ↦ by rw [inf_sSup_eq, sSup_image])

@[deprecated (since := "2026-11-08")]
alias scottContinuous_inf_right := supScottContinuous_inf_right

@[to_dual]
lemma supScottContinuous_inf_left (b : β) : SupScottContinuous fun a ↦ a ⊓ b :=
  .of_map_sSup (fun d _ _ ↦ by rw [sSup_inf_eq, sSup_image])

@[deprecated (since := "2026-11-08")]
alias scottContinuous_inf_left := supScottContinuous_inf_left

/- The meet operation is Scott continuous for suprema. -/
@[to_dual
/- The join operation is Scott continuous for infima. -/]
protected lemma SupScottContinuous.inf : SupScottContinuous fun b : β × β => b.1 ⊓ b.2 :=
  .fromProd supScottContinuous_inf_right supScottContinuous_inf_left

@[deprecated (since := "2026-11-08")]
alias ScottContinuous.inf₂ := SupScottContinuous.inf

end CompleteLinearOrder
