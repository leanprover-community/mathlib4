/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Tactic.ToAdditive
public import Mathlib.Order.Max
public import Mathlib.Order.BoundedOrder.Basic

/-!
# Typeclasses expressing `IsBot 1` and `IsBot 0`
-/

public section

/-- A typeclass expressing that the `0` of a type is a bottom element. In a partial `OrderBot`, this
is equivalent to `⊥ = 0`. -/
class IsBotZeroClass (α : Type*) [LE α] [Zero α] : Prop where
  isBot_zero : IsBot (0 : α)

/-- A typeclass expressing that the `1` of a type is a bottom element. In a partial `OrderBot`, this
is equivalent to `⊥ = 1`. -/
@[to_additive existing]
class IsBotOneClass (α : Type*) [LE α] [One α] : Prop where
  isBot_one : IsBot (1 : α)

variable {α : Type*} {a b : α}

section LE
variable [LE α] [One α] [IsBotOneClass α]

@[to_additive]
theorem isBot_one : IsBot (1 : α) :=
  IsBotOneClass.isBot_one

@[to_additive (attr := simp) zero_le]
theorem one_le {a : α} : 1 ≤ a :=
  isBot_one a

-- TODO: deprecate
alias zero_le' := zero_le

end LE

-- See note [lower instance priority]
instance (priority := 100) [LE α] [Zero α] [One α] [IsBotZeroClass α] : ZeroLEOneClass α where
  zero_le_one := zero_le

section Preorder
variable [Preorder α] [One α] [IsBotOneClass α]

@[to_additive (attr := simp) not_lt_zero]
theorem not_lt_one : ¬ a < 1 := one_le.not_gt

@[deprecated (since := "2025-12-03")] alias not_neg := not_lt_zero

-- TODO: deprecate
alias not_lt_zero' := not_lt_zero

@[to_additive] -- `(attr := simp)` cannot be used here because `a` cannot be inferred by `simp`.
theorem one_lt_of_gt (h : a < b) : 1 < b :=
  one_le.trans_lt h

@[to_additive] alias LT.lt.one_lt := one_lt_of_gt

@[to_additive]
theorem ne_one_of_lt (h : a < b) : b ≠ 1 :=
  h.one_lt.ne'

@[to_additive] alias LT.lt.ne_one := ne_one_of_lt

end Preorder

section PartialOrder
variable [PartialOrder α] [One α] [IsBotOneClass α]

-- Not `simp`, as different types might have a different preferred form.
@[to_additive]
theorem bot_eq_one [OrderBot α] : (⊥ : α) = 1 := isBot_one.eq_bot.symm

-- TODO: deprecate
alias bot_eq_zero'' := bot_eq_zero

@[to_additive (attr := simp)]
theorem le_one_iff_eq_one : a ≤ 1 ↔ a = 1 :=
  one_le.ge_iff_eq'

-- TODO: deprecate
alias le_zero_iff := nonpos_iff_eq_zero

@[to_additive] alias ⟨eq_one_of_le_one, _⟩ := le_one_iff_eq_one
@[to_additive] alias LE.le.eq_one := eq_one_of_le_one

@[to_additive]
theorem one_lt_iff_ne_one : 1 < a ↔ a ≠ 1 :=
  one_le.lt_iff_ne.trans ne_comm

-- TODO: deprecate
alias zero_lt_iff := pos_iff_ne_zero

@[to_additive] alias ⟨_, one_lt_of_ne_one⟩ := one_lt_iff_ne_one
@[to_additive] alias Ne.one_lt := one_lt_of_ne_one

@[to_additive]
theorem eq_one_or_one_lt (a : α) : a = 1 ∨ 1 < a := one_le.eq_or_lt.imp_left Eq.symm

@[to_additive]
lemma one_notMem_iff [OrderBot α] {s : Set α} : 1 ∉ s ↔ ∀ x ∈ s, 1 < x :=
  bot_eq_one (α := α) ▸ bot_notMem_iff

@[deprecated (since := "2026-02-17")] alias NE.ne.pos := Ne.pos
@[deprecated (since := "2026-02-17")] alias NE.ne.one_lt := Ne.one_lt

end PartialOrder

section LinearOrder
variable [LinearOrder α] [One α] [IsBotOneClass α]

@[to_additive]
theorem one_min (a : α) : min 1 a = 1 :=
  min_eq_left one_le

@[to_additive]
theorem min_one (a : α) : min a 1 = 1 :=
  min_eq_right one_le

end LinearOrder

namespace NeZero
variable [Zero α]

theorem of_gt [Preorder α] [IsBotZeroClass α] (h : a < b) : NeZero b :=
  ⟨h.ne_zero⟩

theorem pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] : 0 < a :=
  NeZero.out.pos

-- 1 < p is still an often-used `Fact`, due to `Nat.Prime` implying it, and it implying `Nontrivial`
-- on `ZMod`'s ring structure. We cannot just set this to be any `x < y`, else that becomes a
-- metavariable and it will hugely slow down typeclass inference.
instance (priority := 10) of_gt' [Preorder α] [IsBotZeroClass α] [One α]
    [Fact (1 < a)] : NeZero a := of_gt <| @Fact.out (1 < a) _

theorem of_ge [PartialOrder α] [IsBotZeroClass α] [NeZero a] (h : a ≤ b) : NeZero b :=
  ⟨((pos a).trans_le h).ne_zero⟩

end NeZero
