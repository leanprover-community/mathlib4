/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Order.Antisymmetrization

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

@[expose] public section

open Function

variable {α : Type*} {a b c d : α}

/-! ### Comparability -/

/-- A partial order where any two elements are comparable is a linear order. -/
def Relation.linearOrderOfSymmGen [PartialOrder α]
    [decLE : DecidableLE α] [decLT : DecidableLT α] [decEq : DecidableEq α]
    (h : ∀ a b : α, Relation.SymmGen (· ≤ ·) a b) : LinearOrder α where
  le_total := h
  toDecidableLE := decLE
  toDecidableEq := decEq
  toDecidableLT := decLT

@[deprecated (since := "2026-01-25")] alias CompRel := Relation.SymmGen

@[deprecated (since := "2026-01-25")] alias CompRel.of_rel := Relation.SymmGen.of_rel

@[deprecated (since := "2026-01-25")] alias CompRel.of_rel_symm := Relation.SymmGen.of_rel_symm

@[deprecated (since := "2026-01-25")] alias compRel_swap := Relation.symmGen_swap

@[deprecated (since := "2026-01-25")] alias compRel_swap_apply := Relation.symmGen_swap_apply

@[deprecated (since := "2026-01-25")] alias CompRel.refl := Relation.SymmGen.refl

@[deprecated (since := "2026-01-25")] alias CompRel.rfl := Relation.SymmGen.rfl

@[deprecated (since := "2026-01-25")] alias instReflCompRel := Relation.SymmGen.instRefl

@[deprecated (since := "2026-01-25")] alias CompRel.symm := Relation.SymmGen.symm

@[deprecated (since := "2026-01-25")] alias instSymmCompRel := Relation.SymmGen.instSymm

@[deprecated (since := "2026-01-25")] alias compRel_comm := Relation.symmGen_comm

@[deprecated (since := "2026-01-25")] alias CompRel.decidableRel := Relation.SymmGen.decidableRel

@[deprecated (since := "2026-01-25")] alias AntisymmRel.compRel := AntisymmRel.symmGen

@[deprecated (since := "2026-01-25")] alias compRel_of_total := Relation.symmGen_of_total

@[deprecated (since := "2026-01-13")] alias IsTotal.compRel := compRel_of_total

@[deprecated (since := "2026-01-25")] alias CompRel.of_le := Relation.SymmGen.of_le

@[deprecated (since := "2026-01-25")] alias CompRel.of_ge := Relation.SymmGen.of_ge

@[deprecated (since := "2026-01-25")] alias LE.le.compRel := CompRel.of_le

@[deprecated (since := "2026-01-25")] alias LE.le.compRel_symm := CompRel.of_ge

@[deprecated (since := "2026-01-25")] alias CompRel.of_lt := Relation.SymmGen.of_lt

@[deprecated (since := "2026-01-25")] alias CompRel.of_gt := Relation.SymmGen.of_gt

@[deprecated (since := "2026-01-25")] alias LT.lt.compRel := CompRel.of_lt

@[deprecated (since := "2026-01-25")] alias LT.lt.compRel_symm := CompRel.of_gt

@[deprecated (since := "2026-01-25")]
alias CompRel.of_compRel_of_antisymmRel := Relation.SymmGen.of_symmGen_of_antisymmRel

@[deprecated (since := "2026-01-25")]
alias CompRel.trans_antisymmRel := CompRel.of_compRel_of_antisymmRel

@[deprecated (since := "2026-01-25")]
alias instTransCompRelLeAntisymmRel := instTransSymmGenLeAntisymmRel

@[deprecated (since := "2026-01-25")]
alias CompRel.of_antisymmRel_of_compRel := Relation.SymmGen.of_antisymmRel_of_symmGen

@[deprecated (since := "2026-01-25")]
alias AntisymmRel.trans_compRel := CompRel.of_antisymmRel_of_compRel

@[deprecated (since := "2026-01-25")]
alias instTransAntisymmRelLeCompRel := instTransAntisymmRelLeSymmGen

@[deprecated (since := "2026-01-25")]
alias AntisymmRel.compRel_congr := AntisymmRel.symmGen_congr

@[deprecated (since := "2026-01-25")]
alias AntisymmRel.compRel_congr_left := AntisymmRel.symmGen_congr_left

@[deprecated (since := "2026-01-25")]
alias AntisymmRel.compRel_congr_right := AntisymmRel.symmGen_congr_right

@[deprecated (since := "2026-01-25")] alias linearOrderOfComprel := Relation.linearOrderOfSymmGen

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
  simp [← antisymmRel_compl, compl]

@[simp]
theorem incompRel_compl_apply : IncompRel rᶜ a b ↔ AntisymmRel r a b := by
  simp

theorem incompRel_swap : IncompRel (swap r) = IncompRel r :=
  antisymmRel_swap rᶜ

theorem incompRel_swap_apply : IncompRel (swap r) a b ↔ IncompRel r a b :=
  antisymmRel_swap_apply rᶜ

@[simp, refl]
theorem IncompRel.refl [Std.Irrefl r] (a : α) : IncompRel r a a :=
  AntisymmRel.refl rᶜ a

variable {r}

theorem IncompRel.rfl [Std.Irrefl r] {a : α} : IncompRel r a a := .refl ..

instance [Std.Irrefl r] : Std.Refl (IncompRel r) where
  refl := .refl r

@[symm]
theorem IncompRel.symm : IncompRel r a b → IncompRel r b a :=
  And.symm

instance : Std.Symm (IncompRel r) where
  symm _ _ := IncompRel.symm

theorem incompRel_comm {a b : α} : IncompRel r a b ↔ IncompRel r b a :=
  comm

instance IncompRel.decidableRel [DecidableRel r] : DecidableRel (IncompRel r) :=
  fun _ _ ↦ inferInstanceAs (Decidable (¬ _ ∧ ¬ _))

theorem IncompRel.not_antisymmRel (h : IncompRel r a b) : ¬ AntisymmRel r a b :=
  fun h' ↦ h.1 h'.1

theorem AntisymmRel.not_incompRel (h : AntisymmRel r a b) : ¬ IncompRel r a b :=
  fun h' ↦ h'.1 h.1

theorem not_symmGen_iff : ¬ Relation.SymmGen r a b ↔ IncompRel r a b := by
  simp [Relation.SymmGen, IncompRel]

@[deprecated (since := "2026-01-25")] alias not_compRel_iff := not_symmGen_iff

theorem not_incompRel_iff : ¬ IncompRel r a b ↔ Relation.SymmGen r a b := by
  rw [← not_symmGen_iff, not_not]

@[simp]
theorem not_incompRel_of_total [Std.Total r] (a b : α) : ¬ IncompRel r a b := by
  rw [not_incompRel_iff]
  exact Relation.symmGen_of_total a b

@[deprecated (since := "2026-01-13")] alias IsTotal.not_incompRel := not_incompRel_of_total

theorem IncompRel.ne [Std.Refl r] {a b : α} (h : IncompRel r a b) : a ≠ b := by
  rintro rfl
  exact h.1 <| refl_of r a

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
