/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Order.Antisymmetrization

/-!
# Incomparability relation

Two values in a preorder are incomparable whenever `¬ a ≤ b` and `¬ b ≤ a`.

## Main declarations

* `IncompRel`: The incomparability relation. `IncompRel r a b` means that `a` and `b` are related in
  neither direction by `r`.
-/

open Function OrderDual

variable {α : Type*} {a b c d : α}

section Relation

variable (r : α → α → Prop)

/-- The incomparability relation `IncompRel r a b` means `¬ r a b` and `¬ r b a`. -/
def IncompRel : α → α → Prop :=
  AntisymmRel rᶜ

theorem incompRel_iff {r} : IncompRel r a b ↔ ¬ r a b ∧ ¬ r b a := Iff.rfl

theorem IncompRel.not_le [LE α] (h : IncompRel (· ≤ ·) a b) : ¬ a ≤ b := h.1
theorem IncompRel.not_ge [LE α] (h : IncompRel (· ≤ ·) a b) : ¬ b ≤ a := h.2
theorem LE.le.not_incompRel [LE α] (h : a ≤ b) : ¬ IncompRel (· ≤ ·) a b := fun h' ↦ h'.not_le h

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

instance [IsIrrefl α r] : IsRefl α (IncompRel r) where
  refl := incompRel_refl r

variable {r}

@[symm]
theorem IncompRel.symm : IncompRel r a b → IncompRel r b a :=
  And.symm

instance : IsSymm α (IncompRel r) where
  symm _ _ := IncompRel.symm

instance IncompRel.decidableRel [DecidableRel r] : DecidableRel (IncompRel r) :=
  fun _ _ ↦ inferInstanceAs (Decidable (¬ _ ∧ ¬ _))

theorem IncompRel.not_antisymmRel (h : IncompRel r a b) : ¬ AntisymmRel r a b :=
  fun h' ↦ h.1 h'.1

theorem AntisymmRel.not_incompRel (h : AntisymmRel r a b) : ¬ IncompRel r a b :=
  fun h' ↦ h'.1 h.1

@[simp]
theorem not_incompRel [IsTotal α r] : ¬ IncompRel r a b := by
  rw [incompRel_iff, not_and_or, not_not, not_not]
  exact IsTotal.total a b

end Relation

section Preorder

variable [Preorder α]

theorem IncompRel.not_lt (h : IncompRel (· ≤ ·) a b) : ¬ a < b := mt le_of_lt h.not_le
theorem IncompRel.not_gt (h : IncompRel (· ≤ ·) a b) : ¬ b < a := mt le_of_lt h.not_ge
theorem LT.lt.not_incompRel (h : a < b) : ¬ IncompRel (· ≤ ·) a b := fun h' ↦ h'.not_lt h

theorem not_le_iff_lt_or_incompRel : ¬ b ≤ a ↔ a < b ∨ IncompRel (· ≤ ·) a b := by
  rw [lt_iff_le_not_le, incompRel_iff]
  tauto

/-- Exactly one of the following is true. -/
theorem lt_or_antisymmRel_or_gt_or_incompRel (a b : α) :
    a < b ∨ AntisymmRel (· ≤ ·) a b ∨ b < a ∨ IncompRel (· ≤ ·) a b := by
  simp_rw [lt_iff_le_not_le]
  tauto

@[trans]
theorem incompRel_of_incompRel_of_antisymmRel
    (h₁ : IncompRel (· ≤ ·) a b) (h₂ : AntisymmRel (· ≤ ·) b c) : IncompRel (· ≤ ·) a c :=
  ⟨fun h ↦ h₁.not_le (h.trans h₂.ge), fun h ↦ h₁.not_ge (h₂.le.trans h)⟩

alias IncompRel.trans_antisymmRel := incompRel_of_incompRel_of_antisymmRel

instance : @Trans α α α (IncompRel (· ≤ ·)) (AntisymmRel (· ≤ ·)) (IncompRel (· ≤ ·)) where
  trans := incompRel_of_incompRel_of_antisymmRel

@[trans]
theorem incompRel_of_antisymmRel_of_incompRel
    (h₁ : AntisymmRel (· ≤ ·) a b) (h₂ : IncompRel (· ≤ ·) b c) : IncompRel (· ≤ ·) a c :=
  (h₂.symm.trans_antisymmRel h₁.symm).symm

alias AntisymmRel.trans_incompRel := incompRel_of_antisymmRel_of_incompRel

instance : @Trans α α α (AntisymmRel (· ≤ ·)) (IncompRel (· ≤ ·)) (IncompRel (· ≤ ·)) where
  trans := incompRel_of_antisymmRel_of_incompRel

theorem AntisymmRel.incompRel_congr (h₁ : AntisymmRel (· ≤ ·) a b) (h₂ : AntisymmRel (· ≤ ·) c d) :
    IncompRel (· ≤ ·) a c ↔ IncompRel (· ≤ ·) b d where
  mp h := (h₁.symm.trans_incompRel h).trans_antisymmRel h₂
  mpr h := (h₁.trans_incompRel h).trans_antisymmRel h₂.symm

theorem AntisymmRel.incompRel_congr_left (h : AntisymmRel (· ≤ ·) a b) :
    IncompRel (· ≤ ·) a c ↔ IncompRel (· ≤ ·) b c :=
  h.incompRel_congr (antisymmRel_refl _ c)

theorem AntisymmRel.incompRel_congr_right (h : AntisymmRel (· ≤ ·) b c) :
    IncompRel (· ≤ ·) a b ↔ IncompRel (· ≤ ·) a c :=
  (antisymmRel_refl _ a).incompRel_congr h

end Preorder

/-- Exactly one of the following is true. -/
theorem lt_or_eq_or_gt_or_incompRel [PartialOrder α] (a b : α) :
    a < b ∨ a = b ∨ b < a ∨ IncompRel (· ≤ ·) a b := by
  simpa using lt_or_antisymmRel_or_gt_or_incompRel a b
