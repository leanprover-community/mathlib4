/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Algebra.CovariantAndContravariant
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Order.Monoid.Lemmas
import Mathlib.Order.Lattice

#align_import algebra.order.sub.defs from "leanprover-community/mathlib"@"de29c328903507bb7aff506af9135f4bdaf1849c"

/-!
# Ordered Subtraction

This file proves lemmas relating (truncated) subtraction with an order. We provide a class
`OrderedSub` stating that `a - b ≤ c ↔ a ≤ c + b`.

The subtraction discussed here could both be normal subtraction in an additive group or truncated
subtraction on a canonically ordered monoid (`ℕ`, `Multiset`, `PartENat`, `ENNReal`, ...)

## Implementation details

`OrderedSub` is a mixin type-class, so that we can use the results in this file even in cases
where we don't have a `CanonicallyOrderedAddMonoid` instance
(even though that is our main focus). Conversely, this means we can use
`CanonicallyOrderedAddMonoid` without necessarily having to define a subtraction.

The results in this file are ordered by the type-class assumption needed to prove it.
This means that similar results might not be close to each other. Furthermore, we don't prove
implications if a bi-implication can be proven under the same assumptions.

Lemmas using this class are named using `tsub` instead of `sub` (short for "truncated subtraction").
This is to avoid naming conflicts with similar lemmas about ordered groups.

We provide a second version of most results that require `[ContravariantClass α α (+) (≤)]`. In the
second version we replace this type-class assumption by explicit `AddLECancellable` assumptions.

TODO: maybe we should make a multiplicative version of this, so that we can replace some identical
lemmas about subtraction/division in `Ordered[Add]CommGroup` with these.

TODO: generalize `Nat.le_of_le_of_sub_le_sub_right`, `Nat.sub_le_sub_right_iff`,
  `Nat.mul_self_sub_mul_self_eq`
-/


variable {α β : Type*}

/-- `OrderedSub α` means that `α` has a subtraction characterized by `a - b ≤ c ↔ a ≤ c + b`.
In other words, `a - b` is the least `c` such that `a ≤ b + c`.

This is satisfied both by the subtraction in additive ordered groups and by truncated subtraction
in canonically ordered monoids on many specific types.
-/
class OrderedSub (α : Type*) [LE α] [Add α] [Sub α] : Prop where
  /-- `a - b` provides a lower bound on `c` such that `a ≤ c + b`. -/
  tsub_le_iff_right : ∀ a b c : α, a - b ≤ c ↔ a ≤ c + b
#align has_ordered_sub OrderedSub

section Add

variable [Preorder α] [Add α] [Sub α] [OrderedSub α] {a b c d : α}

@[simp]
theorem tsub_le_iff_right : a - b ≤ c ↔ a ≤ c + b :=
  OrderedSub.tsub_le_iff_right a b c
#align tsub_le_iff_right tsub_le_iff_right

/-- See `add_tsub_cancel_right` for the equality if `ContravariantClass α α (+) (≤)`. -/
theorem add_tsub_le_right : a + b - b ≤ a :=
  tsub_le_iff_right.mpr le_rfl
#align add_tsub_le_right add_tsub_le_right

theorem le_tsub_add : b ≤ b - a + a :=
  tsub_le_iff_right.mp le_rfl
#align le_tsub_add le_tsub_add

end Add

/-! ### Preorder -/


section OrderedAddCommSemigroup

section Preorder

variable [Preorder α]

section AddCommSemigroup

variable [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

theorem tsub_le_iff_left : a - b ≤ c ↔ a ≤ b + c := by rw [tsub_le_iff_right, add_comm]
                                                       -- 🎉 no goals
#align tsub_le_iff_left tsub_le_iff_left

theorem le_add_tsub : a ≤ b + (a - b) :=
  tsub_le_iff_left.mp le_rfl
#align le_add_tsub le_add_tsub

/-- See `add_tsub_cancel_left` for the equality if `ContravariantClass α α (+) (≤)`. -/
theorem add_tsub_le_left : a + b - a ≤ b :=
  tsub_le_iff_left.mpr le_rfl
#align add_tsub_le_left add_tsub_le_left

theorem tsub_le_tsub_right (h : a ≤ b) (c : α) : a - c ≤ b - c :=
  tsub_le_iff_left.mpr <| h.trans le_add_tsub
#align tsub_le_tsub_right tsub_le_tsub_right

theorem tsub_le_iff_tsub_le : a - b ≤ c ↔ a - c ≤ b := by rw [tsub_le_iff_left, tsub_le_iff_right]
                                                          -- 🎉 no goals
#align tsub_le_iff_tsub_le tsub_le_iff_tsub_le

/-- See `tsub_tsub_cancel_of_le` for the equality. -/
theorem tsub_tsub_le : b - (b - a) ≤ a :=
  tsub_le_iff_right.mpr le_add_tsub
#align tsub_tsub_le tsub_tsub_le

section Cov

variable [CovariantClass α α (· + ·) (· ≤ ·)]

theorem tsub_le_tsub_left (h : a ≤ b) (c : α) : c - b ≤ c - a :=
  tsub_le_iff_left.mpr <| le_add_tsub.trans <| add_le_add_right h _
#align tsub_le_tsub_left tsub_le_tsub_left

theorem tsub_le_tsub (hab : a ≤ b) (hcd : c ≤ d) : a - d ≤ b - c :=
  (tsub_le_tsub_right hab _).trans <| tsub_le_tsub_left hcd _
#align tsub_le_tsub tsub_le_tsub

theorem antitone_const_tsub : Antitone fun x => c - x := fun _ _ hxy => tsub_le_tsub rfl.le hxy
#align antitone_const_tsub antitone_const_tsub

/-- See `add_tsub_assoc_of_le` for the equality. -/
theorem add_tsub_le_assoc : a + b - c ≤ a + (b - c) := by
  rw [tsub_le_iff_left, add_left_comm]
  -- ⊢ a + b ≤ a + (c + (b - c))
  exact add_le_add_left le_add_tsub a
  -- 🎉 no goals
#align add_tsub_le_assoc add_tsub_le_assoc

/-- See `tsub_add_eq_add_tsub` for the equality. -/
theorem add_tsub_le_tsub_add : a + b - c ≤ a - c + b := by
  rw [add_comm, add_comm _ b]
  -- ⊢ b + a - c ≤ b + (a - c)
  exact add_tsub_le_assoc
  -- 🎉 no goals
#align add_tsub_le_tsub_add add_tsub_le_tsub_add

theorem add_le_add_add_tsub : a + b ≤ a + c + (b - c) := by
  rw [add_assoc]
  -- ⊢ a + b ≤ a + (c + (b - c))
  exact add_le_add_left le_add_tsub a
  -- 🎉 no goals
#align add_le_add_add_tsub add_le_add_add_tsub

theorem le_tsub_add_add : a + b ≤ a - c + (b + c) := by
  rw [add_comm a, add_comm (a - c)]
  -- ⊢ b + a ≤ b + c + (a - c)
  exact add_le_add_add_tsub
  -- 🎉 no goals
#align le_tsub_add_add le_tsub_add_add

theorem tsub_le_tsub_add_tsub : a - c ≤ a - b + (b - c) := by
  rw [tsub_le_iff_left, ← add_assoc, add_right_comm]
  -- ⊢ a ≤ c + (b - c) + (a - b)
  exact le_add_tsub.trans (add_le_add_right le_add_tsub _)
  -- 🎉 no goals
#align tsub_le_tsub_add_tsub tsub_le_tsub_add_tsub

theorem tsub_tsub_tsub_le_tsub : c - a - (c - b) ≤ b - a := by
  rw [tsub_le_iff_left, tsub_le_iff_left, add_left_comm]
  -- ⊢ c ≤ c - b + (a + (b - a))
  exact le_tsub_add.trans (add_le_add_left le_add_tsub _)
  -- 🎉 no goals
#align tsub_tsub_tsub_le_tsub tsub_tsub_tsub_le_tsub

theorem tsub_tsub_le_tsub_add {a b c : α} : a - (b - c) ≤ a - b + c :=
  tsub_le_iff_right.2 <|
    calc
      a ≤ a - b + b := le_tsub_add
      _ ≤ a - b + (c + (b - c)) := add_le_add_left le_add_tsub _
      _ = a - b + c + (b - c) := (add_assoc _ _ _).symm
#align tsub_tsub_le_tsub_add tsub_tsub_le_tsub_add

/-- See `tsub_add_tsub_comm` for the equality. -/
theorem add_tsub_add_le_tsub_add_tsub : a + b - (c + d) ≤ a - c + (b - d) := by
  rw [add_comm c, tsub_le_iff_left, add_assoc, ← tsub_le_iff_left, ← tsub_le_iff_left]
  -- ⊢ a + b - d - c ≤ a - c + (b - d)
  refine' (tsub_le_tsub_right add_tsub_le_assoc c).trans _
  -- ⊢ a + (b - d) - c ≤ a - c + (b - d)
  rw [add_comm a, add_comm (a - c)]
  -- ⊢ b - d + a - c ≤ b - d + (a - c)
  exact add_tsub_le_assoc
  -- 🎉 no goals
#align add_tsub_add_le_tsub_add_tsub add_tsub_add_le_tsub_add_tsub

/-- See `add_tsub_add_eq_tsub_left` for the equality. -/
theorem add_tsub_add_le_tsub_left : a + b - (a + c) ≤ b - c := by
  rw [tsub_le_iff_left, add_assoc]
  -- ⊢ a + b ≤ a + (c + (b - c))
  exact add_le_add_left le_add_tsub _
  -- 🎉 no goals
#align add_tsub_add_le_tsub_left add_tsub_add_le_tsub_left

/-- See `add_tsub_add_eq_tsub_right` for the equality. -/
theorem add_tsub_add_le_tsub_right : a + c - (b + c) ≤ a - b := by
  rw [tsub_le_iff_left, add_right_comm]
  -- ⊢ a + c ≤ b + (a - b) + c
  exact add_le_add_right le_add_tsub c
  -- 🎉 no goals
#align add_tsub_add_le_tsub_right add_tsub_add_le_tsub_right

end Cov

/-! #### Lemmas that assume that an element is `AddLECancellable` -/


namespace AddLECancellable

protected theorem le_add_tsub_swap (hb : AddLECancellable b) : a ≤ b + a - b :=
  hb le_add_tsub
#align add_le_cancellable.le_add_tsub_swap AddLECancellable.le_add_tsub_swap

protected theorem le_add_tsub (hb : AddLECancellable b) : a ≤ a + b - b := by
  rw [add_comm]
  -- ⊢ a ≤ b + a - b
  exact hb.le_add_tsub_swap
  -- 🎉 no goals
#align add_le_cancellable.le_add_tsub AddLECancellable.le_add_tsub

protected theorem le_tsub_of_add_le_left (ha : AddLECancellable a) (h : a + b ≤ c) : b ≤ c - a :=
  ha <| h.trans le_add_tsub
#align add_le_cancellable.le_tsub_of_add_le_left AddLECancellable.le_tsub_of_add_le_left

protected theorem le_tsub_of_add_le_right (hb : AddLECancellable b) (h : a + b ≤ c) : a ≤ c - b :=
  hb.le_tsub_of_add_le_left <| by rwa [add_comm]
                                  -- 🎉 no goals
#align add_le_cancellable.le_tsub_of_add_le_right AddLECancellable.le_tsub_of_add_le_right

end AddLECancellable

/-! ### Lemmas where addition is order-reflecting -/


section Contra

variable [ContravariantClass α α (· + ·) (· ≤ ·)]

theorem le_add_tsub_swap : a ≤ b + a - b :=
  Contravariant.AddLECancellable.le_add_tsub_swap
#align le_add_tsub_swap le_add_tsub_swap

theorem le_add_tsub' : a ≤ a + b - b :=
  Contravariant.AddLECancellable.le_add_tsub
#align le_add_tsub' le_add_tsub'

theorem le_tsub_of_add_le_left (h : a + b ≤ c) : b ≤ c - a :=
  Contravariant.AddLECancellable.le_tsub_of_add_le_left h
#align le_tsub_of_add_le_left le_tsub_of_add_le_left

theorem le_tsub_of_add_le_right (h : a + b ≤ c) : a ≤ c - b :=
  Contravariant.AddLECancellable.le_tsub_of_add_le_right h
#align le_tsub_of_add_le_right le_tsub_of_add_le_right

end Contra

end AddCommSemigroup

variable [AddCommMonoid α] [Sub α] [OrderedSub α] {a b c d : α}

theorem tsub_nonpos : a - b ≤ 0 ↔ a ≤ b := by rw [tsub_le_iff_left, add_zero]
                                              -- 🎉 no goals
#align tsub_nonpos tsub_nonpos

alias ⟨_, tsub_nonpos_of_le⟩ := tsub_nonpos
#align tsub_nonpos_of_le tsub_nonpos_of_le

end Preorder

/-! ### Partial order -/


variable [PartialOrder α] [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

theorem tsub_tsub (b a c : α) : b - a - c = b - (a + c) := by
  apply le_antisymm
  -- ⊢ b - a - c ≤ b - (a + c)
  · rw [tsub_le_iff_left, tsub_le_iff_left, ← add_assoc, ← tsub_le_iff_left]
    -- 🎉 no goals
  · rw [tsub_le_iff_left, add_assoc, ← tsub_le_iff_left, ← tsub_le_iff_left]
    -- 🎉 no goals
#align tsub_tsub tsub_tsub

theorem tsub_add_eq_tsub_tsub (a b c : α) : a - (b + c) = a - b - c :=
  (tsub_tsub _ _ _).symm
#align tsub_add_eq_tsub_tsub tsub_add_eq_tsub_tsub

theorem tsub_add_eq_tsub_tsub_swap (a b c : α) : a - (b + c) = a - c - b := by
  rw [add_comm]
  -- ⊢ a - (c + b) = a - c - b
  apply tsub_add_eq_tsub_tsub
  -- 🎉 no goals
#align tsub_add_eq_tsub_tsub_swap tsub_add_eq_tsub_tsub_swap

theorem tsub_right_comm : a - b - c = a - c - b := by
  rw [←tsub_add_eq_tsub_tsub, tsub_add_eq_tsub_tsub_swap]
  -- 🎉 no goals
#align tsub_right_comm tsub_right_comm

/-! ### Lemmas that assume that an element is `AddLECancellable`. -/


namespace AddLECancellable

protected theorem tsub_eq_of_eq_add (hb : AddLECancellable b) (h : a = c + b) : a - b = c :=
  le_antisymm (tsub_le_iff_right.mpr h.le) <| by
    rw [h]
    -- ⊢ c ≤ c + b - b
    exact hb.le_add_tsub
    -- 🎉 no goals
#align add_le_cancellable.tsub_eq_of_eq_add AddLECancellable.tsub_eq_of_eq_add

protected theorem eq_tsub_of_add_eq (hc : AddLECancellable c) (h : a + c = b) : a = b - c :=
  (hc.tsub_eq_of_eq_add h.symm).symm
#align add_le_cancellable.eq_tsub_of_add_eq AddLECancellable.eq_tsub_of_add_eq

protected theorem tsub_eq_of_eq_add_rev (hb : AddLECancellable b) (h : a = b + c) : a - b = c :=
  hb.tsub_eq_of_eq_add <| by rw [add_comm, h]
                             -- 🎉 no goals
#align add_le_cancellable.tsub_eq_of_eq_add_rev AddLECancellable.tsub_eq_of_eq_add_rev

@[simp]
protected theorem add_tsub_cancel_right (hb : AddLECancellable b) : a + b - b = a :=
  hb.tsub_eq_of_eq_add <| by rw [add_comm]
                             -- 🎉 no goals
#align add_le_cancellable.add_tsub_cancel_right AddLECancellable.add_tsub_cancel_right

@[simp]
protected theorem add_tsub_cancel_left (ha : AddLECancellable a) : a + b - a = b :=
  ha.tsub_eq_of_eq_add <| add_comm a b
#align add_le_cancellable.add_tsub_cancel_left AddLECancellable.add_tsub_cancel_left

protected theorem lt_add_of_tsub_lt_left (hb : AddLECancellable b) (h : a - b < c) : a < b + c := by
  rw [lt_iff_le_and_ne, ← tsub_le_iff_left]
  -- ⊢ a - b ≤ c ∧ a ≠ b + c
  refine' ⟨h.le, _⟩
  -- ⊢ a ≠ b + c
  rintro rfl
  -- ⊢ False
  simp [hb] at h
  -- 🎉 no goals
#align add_le_cancellable.lt_add_of_tsub_lt_left AddLECancellable.lt_add_of_tsub_lt_left

protected theorem lt_add_of_tsub_lt_right (hc : AddLECancellable c) (h : a - c < b) :
    a < b + c := by
  rw [lt_iff_le_and_ne, ← tsub_le_iff_right]
  -- ⊢ a - c ≤ b ∧ a ≠ b + c
  refine' ⟨h.le, _⟩
  -- ⊢ a ≠ b + c
  rintro rfl
  -- ⊢ False
  simp [hc] at h
  -- 🎉 no goals
#align add_le_cancellable.lt_add_of_tsub_lt_right AddLECancellable.lt_add_of_tsub_lt_right

protected theorem lt_tsub_of_add_lt_right (hc : AddLECancellable c) (h : a + c < b) : a < b - c :=
  (hc.le_tsub_of_add_le_right h.le).lt_of_ne <| by
    rintro rfl
    -- ⊢ False
    exact h.not_le le_tsub_add
    -- 🎉 no goals
#align add_le_cancellable.lt_tsub_of_add_lt_right AddLECancellable.lt_tsub_of_add_lt_right

protected theorem lt_tsub_of_add_lt_left (ha : AddLECancellable a) (h : a + c < b) : c < b - a :=
  ha.lt_tsub_of_add_lt_right <| by rwa [add_comm]
                                   -- 🎉 no goals
#align add_le_cancellable.lt_tsub_of_add_lt_left AddLECancellable.lt_tsub_of_add_lt_left

end AddLECancellable

/-! #### Lemmas where addition is order-reflecting. -/


section Contra

variable [ContravariantClass α α (· + ·) (· ≤ ·)]

theorem tsub_eq_of_eq_add (h : a = c + b) : a - b = c :=
  Contravariant.AddLECancellable.tsub_eq_of_eq_add h
#align tsub_eq_of_eq_add tsub_eq_of_eq_add

theorem eq_tsub_of_add_eq (h : a + c = b) : a = b - c :=
  Contravariant.AddLECancellable.eq_tsub_of_add_eq h
#align eq_tsub_of_add_eq eq_tsub_of_add_eq

theorem tsub_eq_of_eq_add_rev (h : a = b + c) : a - b = c :=
  Contravariant.AddLECancellable.tsub_eq_of_eq_add_rev h
#align tsub_eq_of_eq_add_rev tsub_eq_of_eq_add_rev

@[simp]
theorem add_tsub_cancel_right (a b : α) : a + b - b = a :=
  Contravariant.AddLECancellable.add_tsub_cancel_right
#align add_tsub_cancel_right add_tsub_cancel_right

@[simp]
theorem add_tsub_cancel_left (a b : α) : a + b - a = b :=
  Contravariant.AddLECancellable.add_tsub_cancel_left
#align add_tsub_cancel_left add_tsub_cancel_left

theorem lt_add_of_tsub_lt_left (h : a - b < c) : a < b + c :=
  Contravariant.AddLECancellable.lt_add_of_tsub_lt_left h
#align lt_add_of_tsub_lt_left lt_add_of_tsub_lt_left

theorem lt_add_of_tsub_lt_right (h : a - c < b) : a < b + c :=
  Contravariant.AddLECancellable.lt_add_of_tsub_lt_right h
#align lt_add_of_tsub_lt_right lt_add_of_tsub_lt_right

/-- This lemma (and some of its corollaries) also holds for `ENNReal`, but this proof doesn't work
for it. Maybe we should add this lemma as field to `OrderedSub`? -/
theorem lt_tsub_of_add_lt_left : a + c < b → c < b - a :=
  Contravariant.AddLECancellable.lt_tsub_of_add_lt_left
#align lt_tsub_of_add_lt_left lt_tsub_of_add_lt_left

theorem lt_tsub_of_add_lt_right : a + c < b → a < b - c :=
  Contravariant.AddLECancellable.lt_tsub_of_add_lt_right
#align lt_tsub_of_add_lt_right lt_tsub_of_add_lt_right

end Contra

section Both

variable [CovariantClass α α (· + ·) (· ≤ ·)] [ContravariantClass α α (· + ·) (· ≤ ·)]

theorem add_tsub_add_eq_tsub_right (a c b : α) : a + c - (b + c) = a - b := by
  refine' add_tsub_add_le_tsub_right.antisymm (tsub_le_iff_right.2 <| le_of_add_le_add_right _)
  -- ⊢ α
  exact c
  -- ⊢ a + c ≤ a + c - (b + c) + b + c
  rw [add_assoc]
  -- ⊢ a + c ≤ a + c - (b + c) + (b + c)
  exact le_tsub_add
  -- 🎉 no goals
#align add_tsub_add_eq_tsub_right add_tsub_add_eq_tsub_right

theorem add_tsub_add_eq_tsub_left (a b c : α) : a + b - (a + c) = b - c := by
  rw [add_comm a b, add_comm a c, add_tsub_add_eq_tsub_right]
  -- 🎉 no goals
#align add_tsub_add_eq_tsub_left add_tsub_add_eq_tsub_left

end Both

end OrderedAddCommSemigroup

/-! ### Lemmas in a linearly ordered monoid. -/


section LinearOrder

variable {a b c d : α} [LinearOrder α] [AddCommSemigroup α] [Sub α] [OrderedSub α]

/-- See `lt_of_tsub_lt_tsub_right_of_le` for a weaker statement in a partial order. -/
theorem lt_of_tsub_lt_tsub_right (h : a - c < b - c) : a < b :=
  lt_imp_lt_of_le_imp_le (fun h => tsub_le_tsub_right h c) h
#align lt_of_tsub_lt_tsub_right lt_of_tsub_lt_tsub_right

/-- See `lt_tsub_iff_right_of_le` for a weaker statement in a partial order. -/
theorem lt_tsub_iff_right : a < b - c ↔ a + c < b :=
  lt_iff_lt_of_le_iff_le tsub_le_iff_right
#align lt_tsub_iff_right lt_tsub_iff_right

/-- See `lt_tsub_iff_left_of_le` for a weaker statement in a partial order. -/
theorem lt_tsub_iff_left : a < b - c ↔ c + a < b :=
  lt_iff_lt_of_le_iff_le tsub_le_iff_left
#align lt_tsub_iff_left lt_tsub_iff_left

theorem lt_tsub_comm : a < b - c ↔ c < b - a :=
  lt_tsub_iff_left.trans lt_tsub_iff_right.symm
#align lt_tsub_comm lt_tsub_comm

section Cov

variable [CovariantClass α α (· + ·) (· ≤ ·)]

/-- See `lt_of_tsub_lt_tsub_left_of_le` for a weaker statement in a partial order. -/
theorem lt_of_tsub_lt_tsub_left (h : a - b < a - c) : c < b :=
  lt_imp_lt_of_le_imp_le (fun h => tsub_le_tsub_left h a) h
#align lt_of_tsub_lt_tsub_left lt_of_tsub_lt_tsub_left

end Cov

end LinearOrder

section OrderedAddCommMonoid

variable [PartialOrder α] [AddCommMonoid α] [Sub α] [OrderedSub α]

@[simp]
theorem tsub_zero (a : α) : a - 0 = a :=
  AddLECancellable.tsub_eq_of_eq_add addLECancellable_zero (add_zero _).symm
#align tsub_zero tsub_zero

end OrderedAddCommMonoid
