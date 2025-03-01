/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Order.Antisymmetrization

/-!
# Comparability relation

Two values in a preorder are comparable whenever `a ≤ b` or `b ≤ a`.

## Main declarations

* `CompRel`: The comparability relation. `CompRel r a b` means that `a` and `b` is related in
  either direction by `r`.
-/

open Function OrderDual

variable {α : Type*} {a b c d : α}

section Relation

variable {r : α → α → Prop}

/-- The comparability relation `CompRel r a b` means that either `r a b` or `r b a`. -/
def CompRel (r : α → α → Prop) (a b : α) : Prop :=
  r a b ∨ r b a

theorem CompRel.of_rel {a b : α} (h : r a b) : CompRel r a b :=
  Or.inl h

theorem CompRel.of_rel_symm {a b : α} (h : r b a) : CompRel r a b :=
  Or.inr h

theorem compRel_swap (r : α → α → Prop) : CompRel (swap r) = CompRel r :=
  funext₂ fun _ _ ↦ propext or_comm

theorem compRel_swap_apply (r : α → α → Prop) : CompRel (swap r) a b ↔ CompRel r a b :=
  or_comm

@[refl]
theorem CompRel.refl (r : α → α → Prop) [IsRefl α r] (a : α) : CompRel r a a :=
  .of_rel (_root_.refl _)

theorem CompRel.rfl [IsRefl α r] {a : α} : CompRel r a a := .refl ..

instance [IsRefl α r] : IsRefl α (CompRel r) where
  refl := .refl r

@[symm]
theorem CompRel.symm : CompRel r a b → CompRel r b a :=
  Or.symm

instance : IsSymm α (CompRel r) where
  symm _ _ := CompRel.symm

instance CompRel.decidableRel [DecidableRel r] : DecidableRel (CompRel r) :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ ∨ _))

theorem AntisymmRel.compRel (h : AntisymmRel r a b) : CompRel r a b :=
  Or.inl h.1

@[simp]
theorem IsTotal.compRel [IsTotal α r] : CompRel r a b :=
  IsTotal.total a b

end Relation

section LE

variable [LE α]

theorem CompRel.of_le (h : a ≤ b) : CompRel (· ≤ ·) a b := .of_rel h
theorem CompRel.of_ge (h : b ≤ a) : CompRel (· ≤ ·) a b := .of_rel_symm h

alias LE.le.compRel := CompRel.of_le
alias LE.le.compRel_symm := CompRel.of_ge

end LE

section Preorder

variable [Preorder α]

theorem CompRel.of_lt (h : a < b) : CompRel (· ≤ ·) a b := h.le.compRel
theorem CompRel.of_gt (h : b < a) : CompRel (· ≤ ·) a b := h.le.compRel_symm

alias LT.lt.compRel := CompRel.of_lt
alias LT.lt.compRel_symm := CompRel.of_gt

theorem not_le_iff_lt_or_not_compRel : ¬ b ≤ a ↔ a < b ∨ ¬ CompRel (· ≤ ·) a b := by
  rw [lt_iff_le_not_le, CompRel]
  tauto

/-- Exactly one of the following is true. -/
theorem lt_or_antisymmRel_or_gt_or_not_compRel (a b : α) :
    a < b ∨ AntisymmRel (· ≤ ·) a b ∨ b < a ∨ ¬ CompRel (· ≤ ·) a b := by
  simp_rw [lt_iff_le_not_le, CompRel]
  tauto

@[trans]
theorem compRel_of_compRel_of_antisymmRel
    (h₁ : CompRel (· ≤ ·) a b) (h₂ : AntisymmRel (· ≤ ·) b c) : CompRel (· ≤ ·) a c := by
  obtain (h | h) := h₁
  · exact (h.trans h₂.le).compRel
  · exact (h₂.ge.trans h).compRel_symm

alias CompRel.trans_antisymmRel := compRel_of_compRel_of_antisymmRel

instance : @Trans α α α (CompRel (· ≤ ·)) (AntisymmRel (· ≤ ·)) (CompRel (· ≤ ·)) where
  trans := compRel_of_compRel_of_antisymmRel

@[trans]
theorem compRel_of_antisymmRel_of_compRel
    (h₁ : AntisymmRel (· ≤ ·) a b) (h₂ : CompRel (· ≤ ·) b c) : CompRel (· ≤ ·) a c :=
  (h₂.symm.trans_antisymmRel h₁.symm).symm

alias AntisymmRel.trans_compRel := compRel_of_antisymmRel_of_compRel

instance : @Trans α α α (AntisymmRel (· ≤ ·)) (CompRel (· ≤ ·)) (CompRel (· ≤ ·)) where
  trans := compRel_of_antisymmRel_of_compRel

theorem AntisymmRel.incompRel_congr (h₁ : AntisymmRel (· ≤ ·) a b) (h₂ : AntisymmRel (· ≤ ·) c d) :
    CompRel (· ≤ ·) a c ↔ CompRel (· ≤ ·) b d where
  mp h := (h₁.symm.trans_compRel h).trans_antisymmRel h₂
  mpr h := (h₁.trans_compRel h).trans_antisymmRel h₂.symm

theorem AntisymmRel.incompRel_congr_left (h : AntisymmRel (· ≤ ·) a b) :
    CompRel (· ≤ ·) a c ↔ CompRel (· ≤ ·) b c :=
  h.incompRel_congr .rfl

theorem AntisymmRel.incompRel_congr_right (h : AntisymmRel (· ≤ ·) b c) :
    CompRel (· ≤ ·) a b ↔ CompRel (· ≤ ·) a c :=
  AntisymmRel.rfl.incompRel_congr h

end Preorder

/-- Exactly one of the following is true. -/
theorem lt_or_eq_or_gt_or_notCompRel [PartialOrder α] (a b : α) :
    a < b ∨ a = b ∨ b < a ∨ ¬ CompRel (· ≤ ·) a b := by
  simpa using lt_or_antisymmRel_or_gt_or_not_compRel a b
