/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Order.Antisymmetrization

/-!
# Comparability and incomparability relations

Two values in a preorder are said to be comparable whenever `a ≤ b` or `b ≤ a`. We define both the
comparability and incomparability relations.

In a linear order, `CompRel (· ≤ ·) a b` is always true, and `IncompRel (· ≤ ·) a b` is always
false.

## Implementation notes

Although comparability and incomparability are negations of each other, both relations are
convenient in different contexts, and as such, it's useful to keep them distinct. To move from one
to the other, use `not_compRel_iff` and `not_incompRel_iff`.

## Main declarations

* `CompRel`: The comparability relation. `CompRel r a b` means that `a` and `b` is related in
  either direction by `r`.
* `IncompRel`: The incomparability relation. `IncompRel r a b` means that `a` and `b` are related in
  neither direction by `r`.

## Todo

These definitions should be linked to `IsChain` and `IsAntichain`.
-/

open Function

variable {α : Type*} {a b c d : α}

/-! ### Comparability -/

section Relation

variable {r : α → α → Prop}

/-- The comparability relation `CompRel r a b` means that either `r a b` or `r b a`. -/
def CompRel (r : α → α → Prop) (a b : α) : Prop :=
  r a b ∨ r b a

theorem CompRel.of_rel (h : r a b) : CompRel r a b :=
  Or.inl h

theorem CompRel.of_rel_symm (h : r b a) : CompRel r a b :=
  Or.inr h

theorem compRel_swap (r : α → α → Prop) : CompRel (swap r) = CompRel r :=
  funext₂ fun _ _ ↦ propext or_comm

theorem compRel_swap_apply (r : α → α → Prop) : CompRel (swap r) a b ↔ CompRel r a b :=
  or_comm

@[simp, refl]
theorem CompRel.refl (r : α → α → Prop) [IsRefl α r] (a : α) : CompRel r a a :=
  .of_rel (_root_.refl _)

theorem CompRel.rfl [IsRefl α r] : CompRel r a a := .refl ..

instance [IsRefl α r] : IsRefl α (CompRel r) where
  refl := .refl r

@[symm]
theorem CompRel.symm : CompRel r a b → CompRel r b a :=
  Or.symm

instance : IsSymm α (CompRel r) where
  symm _ _ := CompRel.symm

theorem compRel_comm {a b : α} : CompRel r a b ↔ CompRel r b a :=
  comm

instance CompRel.decidableRel [DecidableRel r] : DecidableRel (CompRel r) :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ ∨ _))

theorem AntisymmRel.compRel (h : AntisymmRel r a b) : CompRel r a b :=
  Or.inl h.1

@[simp]
theorem IsTotal.compRel [IsTotal α r] (a b : α) : CompRel r a b :=
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

@[trans]
theorem CompRel.of_compRel_of_antisymmRel
    (h₁ : CompRel (· ≤ ·) a b) (h₂ : AntisymmRel (· ≤ ·) b c) : CompRel (· ≤ ·) a c := by
  obtain (h | h) := h₁
  · exact (h.trans h₂.le).compRel
  · exact (h₂.ge.trans h).compRel_symm

alias CompRel.trans_antisymmRel := CompRel.of_compRel_of_antisymmRel

instance : @Trans α α α (CompRel (· ≤ ·)) (AntisymmRel (· ≤ ·)) (CompRel (· ≤ ·)) where
  trans := CompRel.of_compRel_of_antisymmRel

@[trans]
theorem CompRel.of_antisymmRel_of_compRel
    (h₁ : AntisymmRel (· ≤ ·) a b) (h₂ : CompRel (· ≤ ·) b c) : CompRel (· ≤ ·) a c :=
  (h₂.symm.trans_antisymmRel h₁.symm).symm

alias AntisymmRel.trans_compRel := CompRel.of_antisymmRel_of_compRel

instance : @Trans α α α (AntisymmRel (· ≤ ·)) (CompRel (· ≤ ·)) (CompRel (· ≤ ·)) where
  trans := CompRel.of_antisymmRel_of_compRel

theorem AntisymmRel.compRel_congr (h₁ : AntisymmRel (· ≤ ·) a b) (h₂ : AntisymmRel (· ≤ ·) c d) :
    CompRel (· ≤ ·) a c ↔ CompRel (· ≤ ·) b d where
  mp h := (h₁.symm.trans_compRel h).trans_antisymmRel h₂
  mpr h := (h₁.trans_compRel h).trans_antisymmRel h₂.symm

theorem AntisymmRel.compRel_congr_left (h : AntisymmRel (· ≤ ·) a b) :
    CompRel (· ≤ ·) a c ↔ CompRel (· ≤ ·) b c :=
  h.compRel_congr .rfl

theorem AntisymmRel.compRel_congr_right (h : AntisymmRel (· ≤ ·) b c) :
    CompRel (· ≤ ·) a b ↔ CompRel (· ≤ ·) a c :=
  AntisymmRel.rfl.compRel_congr h

end Preorder

/-- A partial order where any two elements are comparable is a linear order. -/
def linearOrderOfComprel [PartialOrder α]
    [decLE : DecidableLE α] [decLT : DecidableLT α] [decEq : DecidableEq α]
    (h : ∀ a b : α, CompRel (· ≤ ·) a b) : LinearOrder α where
  le_total := h
  toDecidableLE := decLE
  toDecidableEq := decEq
  toDecidableLT := decLT

/-! ### Incomparability relation -/

section Relation

variable (r : α → α → Prop)

/-- The incomparability relation `IncompRel r a b` means `¬ r a b` and `¬ r b a`. -/
def IncompRel (a b : α) : Prop :=
  ¬ r a b ∧ ¬ r b a

@[simp]
theorem antisymmRel_compl : AntisymmRel rᶜ = IncompRel r :=
  rfl

theorem antisymmRel_compl_apply : AntisymmRel rᶜ a b ↔ IncompRel r a b :=
  .rfl

@[simp]
theorem incompRel_compl : IncompRel rᶜ = AntisymmRel r := by
  simp [← antisymmRel_compl, AntisymmRel, compl]

@[simp]
theorem incompRel_compl_apply : IncompRel rᶜ a b ↔ AntisymmRel r a b := by
  simp

theorem incompRel_swap : IncompRel (swap r) = IncompRel r :=
  antisymmRel_swap rᶜ

theorem incompRel_swap_apply : IncompRel (swap r) a b ↔ IncompRel r a b :=
  antisymmRel_swap_apply rᶜ

@[simp, refl]
theorem IncompRel.refl [IsIrrefl α r] (a : α) : IncompRel r a a :=
  AntisymmRel.refl rᶜ a

variable {r} in
theorem IncompRel.rfl [IsIrrefl α r] {a : α} : IncompRel r a a := .refl ..

instance [IsIrrefl α r] : IsRefl α (IncompRel r) where
  refl := .refl r

variable {r}

@[symm]
theorem IncompRel.symm : IncompRel r a b → IncompRel r b a :=
  And.symm

instance : IsSymm α (IncompRel r) where
  symm _ _ := IncompRel.symm

theorem incompRel_comm {a b : α} : IncompRel r a b ↔ IncompRel r b a :=
  comm

instance IncompRel.decidableRel [DecidableRel r] : DecidableRel (IncompRel r) :=
  fun _ _ ↦ inferInstanceAs (Decidable (¬ _ ∧ ¬ _))

theorem IncompRel.not_antisymmRel (h : IncompRel r a b) : ¬ AntisymmRel r a b :=
  fun h' ↦ h.1 h'.1

theorem AntisymmRel.not_incompRel (h : AntisymmRel r a b) : ¬ IncompRel r a b :=
  fun h' ↦ h'.1 h.1

theorem not_compRel_iff : ¬ CompRel r a b ↔ IncompRel r a b := by
  simp [CompRel, IncompRel]

theorem not_incompRel_iff : ¬ IncompRel r a b ↔ CompRel r a b := by
  rw [← not_compRel_iff, not_not]

@[simp]
theorem IsTotal.not_incompRel [IsTotal α r] (a b : α) : ¬ IncompRel r a b := by
  rw [not_incompRel_iff]
  exact IsTotal.compRel a b

end Relation

section LE

variable [LE α]

theorem IncompRel.not_le (h : IncompRel (· ≤ ·) a b) : ¬ a ≤ b := h.1
theorem IncompRel.not_ge (h : IncompRel (· ≤ ·) a b) : ¬ b ≤ a := h.2
theorem LE.le.not_incompRel (h : a ≤ b) : ¬ IncompRel (· ≤ ·) a b := fun h' ↦ h'.not_le h

end LE

section Preorder

variable [Preorder α]

theorem IncompRel.not_lt (h : IncompRel (· ≤ ·) a b) : ¬ a < b := mt le_of_lt h.not_le
theorem IncompRel.not_gt (h : IncompRel (· ≤ ·) a b) : ¬ b < a := mt le_of_lt h.not_ge
theorem LT.lt.not_incompRel (h : a < b) : ¬ IncompRel (· ≤ ·) a b := fun h' ↦ h'.not_lt h

theorem not_le_iff_lt_or_incompRel : ¬ b ≤ a ↔ a < b ∨ IncompRel (· ≤ ·) a b := by
  rw [lt_iff_le_not_ge, IncompRel]
  tauto

/-- Exactly one of the following is true. -/
theorem lt_or_antisymmRel_or_gt_or_incompRel (a b : α) :
    a < b ∨ AntisymmRel (· ≤ ·) a b ∨ b < a ∨ IncompRel (· ≤ ·) a b := by
  simp_rw [lt_iff_le_not_ge]
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
  h.incompRel_congr AntisymmRel.rfl

theorem AntisymmRel.incompRel_congr_right (h : AntisymmRel (· ≤ ·) b c) :
    IncompRel (· ≤ ·) a b ↔ IncompRel (· ≤ ·) a c :=
  AntisymmRel.rfl.incompRel_congr h

end Preorder

/-- Exactly one of the following is true. -/
theorem lt_or_eq_or_gt_or_incompRel [PartialOrder α] (a b : α) :
    a < b ∨ a = b ∨ b < a ∨ IncompRel (· ≤ ·) a b := by
  simpa using lt_or_antisymmRel_or_gt_or_incompRel a b
