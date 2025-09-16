/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl, Yuyang Zhao
-/
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
import Mathlib.Algebra.NeZero
import Mathlib.Order.BoundedOrder.Basic

/-!
# Canonically ordered monoids
-/

universe u

variable {α : Type u}

/-- An ordered additive monoid is `CanonicallyOrderedAdd`
  if the ordering coincides with the subtractibility relation,
  which is to say, `a ≤ b` iff there exists `c` with `b = a + c`.
  This is satisfied by the natural numbers, for example, but not
  the integers or other nontrivial `OrderedAddCommGroup`s.

  We have `a ≤ b + a` and `a ≤ a + b` as separate fields. In the commutative case the second field
  is redundant, but in the noncommutative case (satisfied most relevantly by the ordinals), this
  extra field allows us to prove more things without the extra commutativity assumption. -/
class CanonicallyOrderedAdd (α : Type*) [Add α] [LE α] : Prop
    extends ExistsAddOfLE α where
  /-- For any `a` and `b`, `a ≤ a + b` -/
  protected le_add_self : ∀ a b : α, a ≤ b + a
  protected le_self_add : ∀ a b : α, a ≤ a + b

attribute [instance 50] CanonicallyOrderedAdd.toExistsAddOfLE

/-- An ordered monoid is `CanonicallyOrderedMul`
  if the ordering coincides with the divisibility relation,
  which is to say, `a ≤ b` iff there exists `c` with `b = a * c`.
  Examples seem rare; it seems more likely that the `OrderDual`
  of a naturally-occurring lattice satisfies this than the lattice
  itself (for example, dual of the lattice of ideals of a PID or
  Dedekind domain satisfy this; collections of all things ≤ 1 seem to
  be more natural that collections of all things ≥ 1). -/
@[to_additive]
class CanonicallyOrderedMul (α : Type*) [Mul α] [LE α] : Prop
    extends ExistsMulOfLE α where
  /-- For any `a` and `b`, `a ≤ a * b` -/
  protected le_mul_self : ∀ a b : α, a ≤ b * a
  protected le_self_mul : ∀ a b : α, a ≤ a * b

attribute [instance 50] CanonicallyOrderedMul.toExistsMulOfLE

section Mul
variable [Mul α]

section LE
variable [LE α] [CanonicallyOrderedMul α] {a b c : α}

@[to_additive]
theorem le_mul_self : a ≤ b * a :=
  CanonicallyOrderedMul.le_mul_self _ _

@[to_additive]
theorem le_self_mul : a ≤ a * b :=
  CanonicallyOrderedMul.le_self_mul _ _

@[to_additive (attr := simp)]
theorem self_le_mul_left (a b : α) : a ≤ b * a :=
  le_mul_self

@[to_additive (attr := simp)]
theorem self_le_mul_right (a b : α) : a ≤ a * b :=
  le_self_mul

@[to_additive]
theorem le_iff_exists_mul : a ≤ b ↔ ∃ c, b = a * c :=
  ⟨exists_mul_of_le, by
    rintro ⟨c, rfl⟩
    exact le_self_mul⟩

end LE

section Preorder
variable [Preorder α] [CanonicallyOrderedMul α] {a b c : α}

@[to_additive]
theorem le_of_mul_le_left : a * b ≤ c → a ≤ c :=
  le_self_mul.trans

@[to_additive]
theorem le_mul_of_le_left : a ≤ b → a ≤ b * c :=
  le_self_mul.trans'

@[to_additive]
theorem le_of_mul_le_right : a * b ≤ c → b ≤ c :=
  le_mul_self.trans

@[to_additive]
theorem le_mul_of_le_right : a ≤ c → a ≤ b * c :=
  le_mul_self.trans'

@[to_additive] alias le_mul_left := le_mul_of_le_right
@[to_additive] alias le_mul_right := le_mul_of_le_left

end Preorder

end Mul

section CommMagma
variable [CommMagma α] [Preorder α] [CanonicallyOrderedMul α] {a b c : α}

@[to_additive]
theorem le_iff_exists_mul' : a ≤ b ↔ ∃ c, b = c * a := by
  simp only [mul_comm _ a, le_iff_exists_mul]

end CommMagma

section MulOneClass
variable [MulOneClass α]

section LE
variable [LE α] [CanonicallyOrderedMul α] {a b : α}

@[to_additive (attr := simp) zero_le]
theorem one_le (a : α) : 1 ≤ a :=
  le_self_mul.trans_eq (one_mul _)

@[to_additive] theorem isBot_one : IsBot (1 : α) := one_le

end LE

section Preorder
variable [Preorder α] [CanonicallyOrderedMul α] {a b : α}

@[to_additive] -- `(attr := simp)` cannot be used here because `a` cannot be inferred by `simp`.
theorem one_lt_of_gt (h : a < b) : 1 < b :=
  (one_le _).trans_lt h

alias LT.lt.pos := pos_of_gt
@[to_additive existing] alias LT.lt.one_lt := one_lt_of_gt

end Preorder

section PartialOrder
variable [PartialOrder α] [CanonicallyOrderedMul α] {a b c : α}

@[to_additive]
theorem bot_eq_one [OrderBot α] : (⊥ : α) = 1 := isBot_one.eq_bot.symm

@[to_additive (attr := simp)]
theorem le_one_iff_eq_one : a ≤ 1 ↔ a = 1 :=
  (one_le a).ge_iff_eq'

@[to_additive]
theorem one_lt_iff_ne_one : 1 < a ↔ a ≠ 1 :=
  (one_le a).lt_iff_ne.trans ne_comm

@[to_additive]
theorem one_lt_of_ne_one (h : a ≠ 1) : 1 < a :=
  one_lt_iff_ne_one.2 h

@[to_additive]
theorem eq_one_or_one_lt (a : α) : a = 1 ∨ 1 < a := (one_le a).eq_or_lt.imp_left Eq.symm

@[to_additive]
lemma one_notMem_iff [OrderBot α] {s : Set α} : 1 ∉ s ↔ ∀ x ∈ s, 1 < x :=
  bot_eq_one (α := α) ▸ bot_notMem_iff

@[deprecated (since := "2025-05-23")] alias zero_not_mem_iff := zero_notMem_iff
@[to_additive existing, deprecated (since := "2025-05-23")] alias one_not_mem_iff := one_notMem_iff

alias NE.ne.pos := pos_of_ne_zero
@[to_additive existing] alias NE.ne.one_lt := one_lt_of_ne_one

@[to_additive]
theorem exists_one_lt_mul_of_lt (h : a < b) : ∃ (c : _) (_ : 1 < c), a * c = b := by
  obtain ⟨c, hc⟩ := le_iff_exists_mul.1 h.le
  refine ⟨c, one_lt_iff_ne_one.2 ?_, hc.symm⟩
  rintro rfl
  simp [hc] at h

@[to_additive]
theorem lt_iff_exists_mul [MulLeftStrictMono α] : a < b ↔ ∃ c > 1, b = a * c := by
  rw [lt_iff_le_and_ne, le_iff_exists_mul, ← exists_and_right]
  apply exists_congr
  intro c
  rw [and_comm, and_congr_left_iff, gt_iff_lt]
  rintro rfl
  constructor
  · rw [one_lt_iff_ne_one]
    apply mt
    rintro rfl
    rw [mul_one]
  · rw [← (self_le_mul_right a c).lt_iff_ne]
    apply lt_mul_of_one_lt_right'

end PartialOrder

end MulOneClass

section Semigroup
variable [Semigroup α]

section LE
variable [LE α] [CanonicallyOrderedMul α]

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 10) CanonicallyOrderedMul.toMulLeftMono :
    MulLeftMono α where
  elim a b c hbc := by
    obtain ⟨c, hc, rfl⟩ := exists_mul_of_le hbc
    rw [le_iff_exists_mul]
    exact ⟨c, (mul_assoc _ _ _).symm⟩

end LE

end Semigroup

-- TODO: make it an instance
@[to_additive]
lemma CanonicallyOrderedMul.toIsOrderedMonoid
    [CommMonoid α] [PartialOrder α] [CanonicallyOrderedMul α] : IsOrderedMonoid α where
  mul_le_mul_left _ _ := mul_le_mul_left'

section Monoid
variable [Monoid α]

section PartialOrder
variable [PartialOrder α] [CanonicallyOrderedMul α] {a b c : α}

@[to_additive] instance CanonicallyOrderedCommMonoid.toUniqueUnits : Unique αˣ where
  uniq a := Units.ext <| le_one_iff_eq_one.mp (le_of_mul_le_left a.mul_inv.le)

end PartialOrder

end Monoid

section CommMonoid
variable [CommMonoid α]

section PartialOrder
variable [PartialOrder α] [CanonicallyOrderedMul α] {a b c : α}

@[to_additive (attr := simp) add_pos_iff]
theorem one_lt_mul_iff : 1 < a * b ↔ 1 < a ∨ 1 < b := by
  simp only [one_lt_iff_ne_one, Ne, mul_eq_one, not_and_or]

end PartialOrder

end CommMonoid

namespace NeZero

theorem pos {M} [AddZeroClass M] [PartialOrder M] [CanonicallyOrderedAdd M]
    (a : M) [NeZero a] : 0 < a :=
  (zero_le a).lt_of_ne <| NeZero.out.symm

theorem of_gt {M} [AddZeroClass M] [Preorder M] [CanonicallyOrderedAdd M]
    {x y : M} (h : x < y) : NeZero y :=
  of_pos <| pos_of_gt h

-- 1 < p is still an often-used `Fact`, due to `Nat.Prime` implying it, and it implying `Nontrivial`
-- on `ZMod`'s ring structure. We cannot just set this to be any `x < y`, else that becomes a
-- metavariable and it will hugely slow down typeclass inference.
instance (priority := 10) of_gt' {M : Type*} [AddZeroClass M] [Preorder M] [CanonicallyOrderedAdd M]
    [One M] {y : M}
    [Fact (1 < y)] : NeZero y := of_gt <| @Fact.out (1 < y) _

theorem of_ge {M} [AddZeroClass M] [PartialOrder M] [CanonicallyOrderedAdd M]
    {x y : M} [NeZero x] (h : x ≤ y) : NeZero y :=
  of_pos <| lt_of_lt_of_le (pos x) h

end NeZero

section CanonicallyLinearOrderedMonoid

variable [Monoid α] [LinearOrder α] [CanonicallyOrderedMul α]

@[to_additive]
theorem min_mul_distrib (a b c : α) : min a (b * c) = min a (min a b * min a c) := by
  rcases le_total a b with hb | hb
  · simp [hb, le_mul_right]
  · rcases le_total a c with hc | hc
    · simp [hc, le_mul_left]
    · simp [hb, hc]

@[to_additive]
theorem min_mul_distrib' (a b c : α) : min (a * b) c = min (min a c * min b c) c := by
  simpa [min_comm _ c] using min_mul_distrib c a b

@[to_additive]
theorem one_min (a : α) : min 1 a = 1 :=
  min_eq_left (one_le a)

@[to_additive]
theorem min_one (a : α) : min a 1 = 1 :=
  min_eq_right (one_le a)

/-- In a linearly ordered monoid, we are happy for `bot_eq_one` to be a `@[simp]` lemma. -/
@[to_additive (attr := simp)
  /-- In a linearly ordered monoid, we are happy for `bot_eq_zero` to be a `@[simp]` lemma -/]
theorem bot_eq_one' [OrderBot α] : (⊥ : α) = 1 :=
  bot_eq_one

end CanonicallyLinearOrderedMonoid
