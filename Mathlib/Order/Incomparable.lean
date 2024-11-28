/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Order.Antisymmetrization

/-!
# Incomparability relation

Two values in a preorder are incomparable whenever `¬ a ≤ b` and `¬ b ≤ a`. If so, we write `a ‖ b`.

## Main declarations

* `IncompRel`: The incomparability relation. `IncompRel r a b` means that `a` and `b` are related in
  neither direction by `r`.
-/

open Function OrderDual

variable {α : Type*} {a b c : α}

section Relation

variable (r : α → α → Prop)

/-- The incomparability relation `IncompRel r a b` means `¬ r a b` and `¬ r b c`. -/
def IncompRel : α → α → Prop :=
  AntisymmRel rᶜ

/-- The incomparability relation `a ‖ b` means that both `¬ a ≤ b` and `¬ b ≤ a`. -/
infix:50 " ‖ "  => IncompRel (· ≤ ·)

theorem incompRel_iff {r} : IncompRel r a b ↔ ¬ r a b ∧ ¬ r b a := Iff.rfl

theorem IncompRel.not_le [LE α] (h : a ‖ b) : ¬ a ≤ b := h.1
theorem IncompRel.not_ge [LE α] (h : a ‖ b) : ¬ b ≤ a := h.2
theorem IncompRel.not_lt [Preorder α] (h : a ‖ b) : ¬ a < b := mt le_of_lt h.not_le
theorem IncompRel.not_gt [Preorder α] (h : a ‖ b) : ¬ b < a := mt le_of_lt h.not_ge

@[simp]
theorem antisymmRel_compl : AntisymmRel rᶜ = IncompRel r :=
  rfl

@[simp]
theorem incompRel_compl : IncompRel rᶜ = AntisymmRel r := by
  simp [IncompRel, AntisymmRel, compl]

theorem incompRel_swap : IncompRel (swap r) = IncompRel r :=
  antisymmRel_swap _

@[refl]
theorem incompRel_refl [IsIrrefl α r] (a : α) : IncompRel r a a :=
  antisymmRel_refl _ _

variable {r}

@[symm]
theorem IncompRel.symm : IncompRel r a b → IncompRel r b a :=
  And.symm

instance IncompRel.decidableRel [DecidableRel r] : DecidableRel (IncompRel r) :=
  fun _ _ ↦ inferInstanceAs (Decidable (¬ _ ∧ ¬ _))

@[simp]
theorem not_incompRel [IsTotal α r] : ¬ IncompRel r a b := by
  rw [incompRel_iff, not_and_or, not_not, not_not]
  exact IsTotal.total a b

end Relation
