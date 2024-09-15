/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Order.Defs

/-!
# Note about `Mathlib/Init/`
The files in `Mathlib/Init` are leftovers from the port from Mathlib3.
(They contain content moved from lean3 itself that Mathlib needed but was not moved to lean4.)

We intend to move all the content of these files out into the main `Mathlib` directory structure.
Contributions assisting with this are appreciated.

# Unbundled algebra classes

These classes were part of an incomplete refactor described
[here on the github Wiki](https://github.com/leanprover/lean/wiki/Refactoring-structures#encoding-the-algebraic-hierarchy-1).
However a subset of them are widely used in mathlib3,
and it has been tricky to clean this up as this file was in core Lean 3.
-/

set_option linter.deprecated false

universe u v

variable {α : Sort u} {β : Sort v}

@[deprecated (since := "2024-09-11")]
class IsLeftCancel (α : Sort u) (op : α → α → α) : Prop where
  left_cancel : ∀ a b c, op a b = op a c → b = c

@[deprecated (since := "2024-09-11")]
class IsRightCancel (α : Sort u) (op : α → α → α) : Prop where
  right_cancel : ∀ a b c, op a b = op c b → a = c

/-- `IsTotalPreorder X r` means that the binary relation `r` on `X` is total and a preorder. -/
@[deprecated (since := "2024-07-30")]
class IsTotalPreorder (α : Sort u) (r : α → α → Prop) extends IsTrans α r, IsTotal α r : Prop

/-- Every total pre-order is a pre-order. -/
instance (priority := 100) isTotalPreorder_isPreorder (α : Sort u) (r : α → α → Prop)
    [s : IsTotalPreorder α r] : IsPreorder α r where
  trans := s.trans
  refl a := Or.elim (@IsTotal.total _ r _ a a) id id

/-- `IsIncompTrans X lt` means that for `lt` a binary relation on `X`, the incomparable relation
`fun a b => ¬ lt a b ∧ ¬ lt b a` is transitive. -/
@[deprecated (since := "2024-07-30")]
class IsIncompTrans (α : Sort u) (lt : α → α → Prop) : Prop where
  incomp_trans : ∀ a b c, ¬lt a b ∧ ¬lt b a → ¬lt b c ∧ ¬lt c b → ¬lt a c ∧ ¬lt c a

@[deprecated (since := "2024-07-30")]
instance (priority := 100) (α : Sort u) (lt : α → α → Prop) [IsStrictWeakOrder α lt] :
    IsIncompTrans α lt := { ‹IsStrictWeakOrder α lt› with }

section

variable {α : Sort u} {r : α → α → Prop}

local infixl:50 " ≺ " => r

@[deprecated (since := "2024-07-30")]
theorem incomp_trans [IsIncompTrans α r] {a b c : α} :
    ¬a ≺ b ∧ ¬b ≺ a → ¬b ≺ c ∧ ¬c ≺ b → ¬a ≺ c ∧ ¬c ≺ a :=
  IsIncompTrans.incomp_trans _ _ _

section ExplicitRelationVariants

variable (r)

@[elab_without_expected_type, deprecated (since := "2024-07-30")]
theorem incomp_trans_of [IsIncompTrans α r] {a b c : α} :
    ¬a ≺ b ∧ ¬b ≺ a → ¬b ≺ c ∧ ¬c ≺ b → ¬a ≺ c ∧ ¬c ≺ a :=
  incomp_trans

end ExplicitRelationVariants

end

namespace StrictWeakOrder

section

variable {α : Sort u} {r : α → α → Prop}

local infixl:50 " ≺ " => r

@[deprecated (since := "2024-07-30")]
def Equiv (a b : α) : Prop :=
  ¬a ≺ b ∧ ¬b ≺ a

local infixl:50 " ≈ " => @Equiv _ r

@[deprecated (since := "2024-07-30")]
theorem esymm {a b : α} : a ≈ b → b ≈ a := fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩

@[deprecated (since := "2024-07-30")]
theorem not_lt_of_equiv {a b : α} : a ≈ b → ¬a ≺ b := fun h => h.1

@[deprecated (since := "2024-07-30")]
theorem not_lt_of_equiv' {a b : α} : a ≈ b → ¬b ≺ a := fun h => h.2

variable [IsStrictWeakOrder α r]

@[deprecated (since := "2024-07-30")]
theorem erefl (a : α) : a ≈ a :=
  ⟨irrefl a, irrefl a⟩

@[deprecated (since := "2024-07-30")]
theorem etrans {a b c : α} : a ≈ b → b ≈ c → a ≈ c :=
  incomp_trans

@[deprecated (since := "2024-07-30")]
instance isEquiv : IsEquiv α (@Equiv _ r) where
  refl := erefl
  trans _ _ _ := etrans
  symm _ _ := esymm

end

/-- The equivalence relation induced by `lt` -/
notation:50 a " ≈[" lt "]" b:50 => @Equiv _ lt a b

end StrictWeakOrder

@[deprecated (since := "2024-07-30")]
theorem isStrictWeakOrder_of_isTotalPreorder {α : Sort u} {le : α → α → Prop} {lt : α → α → Prop}
    [DecidableRel le] [IsTotalPreorder α le] (h : ∀ a b, lt a b ↔ ¬le b a) :
    IsStrictWeakOrder α lt :=
  { trans := fun a b c hab hbc =>
      have nba : ¬le b a := Iff.mp (h _ _) hab
      have ncb : ¬le c b := Iff.mp (h _ _) hbc
      have hab : le a b := Or.resolve_left (total_of le b a) nba
      have nca : ¬le c a := fun hca : le c a =>
        have hcb : le c b := trans_of le hca hab
        absurd hcb ncb
      Iff.mpr (h _ _) nca
    irrefl := fun a hlt => absurd (refl_of le a) (Iff.mp (h _ _) hlt)
    incomp_trans := fun a b c ⟨nab, nba⟩ ⟨nbc, ncb⟩ =>
      have hba : le b a := Decidable.of_not_not (Iff.mp (not_congr (h _ _)) nab)
      have hab : le a b := Decidable.of_not_not (Iff.mp (not_congr (h _ _)) nba)
      have hcb : le c b := Decidable.of_not_not (Iff.mp (not_congr (h _ _)) nbc)
      have hbc : le b c := Decidable.of_not_not (Iff.mp (not_congr (h _ _)) ncb)
      have hac : le a c := trans_of le hab hbc
      have hca : le c a := trans_of le hcb hba
      And.intro (fun n => absurd hca (Iff.mp (h _ _) n)) fun n => absurd hac (Iff.mp (h _ _) n) }

section LinearOrder
variable {α : Type*} [LinearOrder α]

set_option linter.deprecated false in
@[deprecated (since := "2024-07-30")]
instance : IsTotalPreorder α (· ≤ ·) where
  trans := @le_trans _ _
  total := le_total

set_option linter.deprecated false in
@[deprecated (since := "2024-07-30")]
instance isStrictWeakOrder_of_linearOrder : IsStrictWeakOrder α (· < ·) :=
  have : IsTotalPreorder α (· ≤ ·) := by infer_instance -- Porting note: added
  isStrictWeakOrder_of_isTotalPreorder lt_iff_not_ge

end LinearOrder

@[deprecated (since := "2024-07-30")]
theorem lt_of_lt_of_incomp {α : Sort u} {lt : α → α → Prop} [IsStrictWeakOrder α lt]
    [DecidableRel lt] : ∀ {a b c}, lt a b → ¬lt b c ∧ ¬lt c b → lt a c :=
  @fun a b c hab ⟨nbc, ncb⟩ =>
  have nca : ¬lt c a := fun hca => absurd (trans_of lt hca hab) ncb
  Decidable.byContradiction fun nac : ¬lt a c =>
    have : ¬lt a b ∧ ¬lt b a := incomp_trans_of lt ⟨nac, nca⟩ ⟨ncb, nbc⟩
    absurd hab this.1

@[deprecated (since := "2024-07-30")]
theorem lt_of_incomp_of_lt {α : Sort u} {lt : α → α → Prop} [IsStrictWeakOrder α lt]
    [DecidableRel lt] : ∀ {a b c}, ¬lt a b ∧ ¬lt b a → lt b c → lt a c :=
  @fun a b c ⟨nab, nba⟩ hbc =>
  have nca : ¬lt c a := fun hca => absurd (trans_of lt hbc hca) nba
  Decidable.byContradiction fun nac : ¬lt a c =>
    have : ¬lt b c ∧ ¬lt c b := incomp_trans_of lt ⟨nba, nab⟩ ⟨nac, nca⟩
    absurd hbc this.1

@[deprecated (since := "2024-07-30")]
theorem eq_of_incomp {α : Sort u} {lt : α → α → Prop} [IsTrichotomous α lt] {a b} :
    ¬lt a b ∧ ¬lt b a → a = b := fun ⟨nab, nba⟩ =>
  match trichotomous_of lt a b with
  | Or.inl hab => absurd hab nab
  | Or.inr (Or.inl hab) => hab
  | Or.inr (Or.inr hba) => absurd hba nba

@[deprecated (since := "2024-07-30")]
theorem eq_of_eqv_lt {α : Sort u} {lt : α → α → Prop} [IsTrichotomous α lt] {a b} :
    a ≈[lt]b → a = b :=
  eq_of_incomp

@[deprecated (since := "2024-07-30")]
theorem incomp_iff_eq {α : Sort u} {lt : α → α → Prop} [IsTrichotomous α lt] [IsIrrefl α lt] (a b) :
    ¬lt a b ∧ ¬lt b a ↔ a = b :=
  Iff.intro eq_of_incomp fun hab => hab ▸ And.intro (irrefl_of lt a) (irrefl_of lt a)

@[deprecated (since := "2024-07-30")]
theorem eqv_lt_iff_eq {α : Sort u} {lt : α → α → Prop} [IsTrichotomous α lt] [IsIrrefl α lt] (a b) :
    a ≈[lt]b ↔ a = b :=
  incomp_iff_eq a b
