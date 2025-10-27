/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Order.Interval.Set.OrdConnected

/-!
### Order instances on quotients

We define a `Preorder` instance on a general `Quotient`, as the transitive closure of the
`x ≤ y ∨ x ≈ y` relation. This is the quotient object in the category of preorders.

We show that in the case of a linear order with `Set.OrdConnected` equivalence classes, this
relation is automatically transitive (we don't need to take the transitive closure), and gives a
`LinearOrder` structure on the quotient. In that case, the resulting order is sometimes called a
**condensation**.
-/

open Set

variable {α : Type*} {s : Setoid α}

namespace Quotient

section LE
variable [LE α]

instance : LE (Quotient s) where
  le := Quotient.lift₂ (Relation.TransGen fun x y ↦ x ≤ y ∨ x ≈ y) <| by
    refine fun x₁ x₂ y₁ y₂ hx hy ↦ propext ⟨?_, ?_⟩ <;> intro h
    · exact .trans (.single <| .inr (symm hx)) <| .trans h (.single <| .inr hy)
    · exact .trans (.single <| .inr hx) <| .trans h (.single <| .inr (symm hy))

theorem le_def {x y : α} :
    Quotient.mk s x ≤ Quotient.mk s y ↔ Relation.TransGen (fun x y ↦ x ≤ y ∨ x ≈ y) x y := .rfl

instance : IsRefl (Quotient s) (· ≤ ·) where
  refl x := by
    induction x using Quotient.inductionOn with | h x
    exact .single <| .inr (refl x)

instance : IsTrans (Quotient s) (· ≤ ·) where
  trans x y z h₁ h₂ := by
    induction x using Quotient.inductionOn with | h x
    induction y using Quotient.inductionOn with | h y
    induction z using Quotient.inductionOn with | h z
    exact Relation.TransGen.trans h₁ h₂

instance [IsTotal α (· ≤ ·)] : IsTotal (Quotient s) (· ≤ ·) where
  total x y := by
    induction x using Quotient.inductionOn with | h x
    induction y using Quotient.inductionOn with | h y
    obtain h | h := total_of (· ≤ ·) x y
    · exact .inl <| .single <| .inl h
    · exact .inr <| .single <| .inl h

instance : Preorder (Quotient s) where
  le_refl := refl
  le_trans _ _ _ := _root_.trans

end LE

section Preorder
variable [Preorder α]

theorem mk_monotone : Monotone (Quotient.mk s) :=
  fun _ _ h ↦ .single (.inl h)

theorem lift_monotone {α β : Type*} [Preorder α] {s : Setoid α} [Preorder β]
    (f : α → β) (hf : Monotone f) (H : ∀ x₁ x₂, x₁ ≈ x₂ → f x₁ = f x₂) :
    Monotone (Quotient.lift f H) := by
  intro x y h
  induction x using Quotient.inductionOn with | h x
  induction y using Quotient.inductionOn with | h y
  induction h
  on_goal 2 => rename_i IH; apply IH.trans
  all_goals
    rename_i h
    cases h with
    | inl h => exact hf h
    | inr h => exact (H _ _ h).le

end Preorder

section LinearOrder
variable [LinearOrder α] [H : ∀ x, OrdConnected (Quotient.mk s ⁻¹' {x})]

theorem mk_le_mk {x y : α} : Quotient.mk s x ≤ Quotient.mk s y ↔ x ≤ y ∨ x ≈ y := by
  rw [← propext_iff]
  revert x y
  apply congrFun₂ (Relation.transGen_eq_self fun x y z h₁ h₂ ↦ ?_)
  cases h₁ <;> cases h₂ <;> rename_i h₁ h₂
  · exact .inl <| h₁.trans h₂
  · rw [or_iff_not_imp_left, not_le]
    rw [← Quotient.eq_iff_equiv] at *
    exact fun h ↦ ((H _).out h₂.symm rfl ⟨h.le, h₁⟩).trans h₂
  · rw [or_iff_not_imp_left, not_le]
    rw [← Quotient.eq_iff_equiv] at *
    exact fun h ↦ ((H _).out h₁.symm rfl ⟨h₂, h.le⟩).symm
  · exact .inr (_root_.trans h₁ h₂)

instance [DecidableRel (· ≈ · : α → α → Prop)] : LinearOrder (Quotient s) where
  le_antisymm x y h₁ h₂ := by
    induction x using Quotient.inductionOn with | h x
    induction y using Quotient.inductionOn with | h y
    rw [mk_le_mk] at h₁ h₂
    cases h₁ with
    | inr h => exact Quotient.sound h
    | inl h₁ =>
      cases h₂ with
      | inr h => exact (Quotient.sound h).symm
      | inl h₂ => exact congrArg _ (h₁.antisymm h₂)
  le_total := total_of _
  toDecidableLE x y := Quotient.recOnSubsingleton₂ x y fun x y ↦ decidable_of_iff' _ mk_le_mk

theorem mk_lt_mk {x y : α} : Quotient.mk s x < Quotient.mk s y ↔ x < y ∧ ¬ x ≈ y := by
  classical
  rw [← not_iff_not, not_and_or, not_lt, mk_le_mk, not_lt, comm_of (· ≈ ·), not_not]

theorem lt_of_mk_lt_mk {x y : α} (h : Quotient.mk s x < Quotient.mk s y) : x < y :=
  (mk_lt_mk.1 h).1

end LinearOrder
end Quotient
