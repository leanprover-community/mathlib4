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

variable {α : Type*}

section Relation

variable (r : α → α → Prop)

/-- The incomparability relation `IncompRel r a b` means `¬ r a b` and `¬ r b c`. -/
def IncompRel : α → α → Prop :=
  AntisymmRel rᶜ

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
theorem IncompRel.symm {a b : α} : IncompRel r a b → IncompRel r b a :=
  And.symm

@[trans]
theorem AntisymmRel.trans [IsTrans α r] {a b c : α} (hab : AntisymmRel r a b)
    (hbc : AntisymmRel r b c) : AntisymmRel r a c :=
  ⟨_root_.trans hab.1 hbc.1, _root_.trans hbc.2 hab.2⟩

instance AntisymmRel.decidableRel [DecidableRel r] : DecidableRel (AntisymmRel r) := fun _ _ =>
  instDecidableAnd

@[simp]
theorem antisymmRel_iff_eq [IsRefl α r] [IsAntisymm α r] {a b : α} : AntisymmRel r a b ↔ a = b :=
  antisymm_iff

alias ⟨AntisymmRel.eq, _⟩ := antisymmRel_iff_eq

end Relation
