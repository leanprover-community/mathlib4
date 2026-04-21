/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Order.Filter.Cofinite

/-!
# Northcott Functions

In number theory, the height function `h` satisfies the *Northcott property* that the sets
`{a | h a ≤ b}` are finite. This file extracts this notion as a typeclass and provides some API.

## Main definitions

* `Northcott h`: A function `h : α → β` is Northcott if the sets `{a : α | h a ≤ b}` are all finite.

## Main theorems

* `Northcott.exists_min_image h s hs`: If `h` is Northcott to a linear order, then `h` has an
  absolute minimum on every nonempty set `s`.

## References

* [D. Northcott, *An inequality in the theory of arithmetic on algebraic varieties*](northcott1949)
-/

@[expose] public noncomputable section

variable {α β : Type*} (h : α → β)

/-- A function `h : α → β` is Northcott if the sets `{a : α | h a ≤ b}` are all finite. -/
@[mk_iff]
class Northcott [LE β] : Prop where
  finite_le : ∀ b, {a : α | h a ≤ b}.Finite

open Filter in
theorem northcott_iff_tendsto [LinearOrder β] [NoMaxOrder β] :
    Northcott h ↔ Tendsto h cofinite atTop := by
  simp_rw [northcott_iff, tendsto_atTop, eventually_cofinite, not_le]
  refine ⟨fun H b ↦ (H b).subset fun x ↦ le_of_lt, fun H b ↦ ?_⟩
  obtain ⟨b', hc⟩ := exists_gt b
  exact (H b').subset fun x hx ↦ lt_of_le_of_lt hx hc

theorem Northcott.exists_min_image [LinearOrder β] [Northcott h] (s : Set α) (hs : s.Nonempty) :
    ∃ a ∈ s, ∀ a' ∈ s, h a ≤ h a' := by
  obtain ⟨a₁, h₁⟩ := hs
  obtain ⟨a₂, h₂, h₃⟩ := Set.exists_min_image ({a | h a ≤ h a₁} ∩ s) h
    ((finite_le (h a₁)).inter_of_left s) ⟨a₁, le_rfl, h₁⟩
  grind
