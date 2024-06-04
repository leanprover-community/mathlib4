/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Finset.Preimage
import Mathlib.Order.Interval.Set.Image
import Mathlib.Order.Interval.Set.UnorderedInterval

#align_import order.locally_finite from "leanprover-community/mathlib"@"1d29de43a5ba4662dd33b5cfeecfc2a27a5a8a29"

/-!
# Locally finite orders

This file defines locally finite orders.

A locally finite order is an order for which all bounded intervals are finite. This allows to make
sense of `Icc`/`Ico`/`Ioc`/`Ioo` as lists, multisets, or finsets.
Further, if the order is bounded above (resp. below), then we can also make sense of the
"unbounded" intervals `Ici`/`Ioi` (resp. `Iic`/`Iio`).

Many theorems about these intervals can be found in `Order.Interval.Finset.Basic`.

## Examples

Naturally occurring locally finite orders are `ℕ`, `ℤ`, `ℕ+`, `Fin n`, `α × β` the product of two
locally finite orders, `α →₀ β` the finitely supported functions to a locally finite order `β`...

## Main declarations

In a `LocallyFiniteOrder`,
* `Finset.Icc`: Closed-closed interval as a finset.
* `Finset.Ico`: Closed-open interval as a finset.
* `Finset.Ioc`: Open-closed interval as a finset.
* `Finset.Ioo`: Open-open interval as a finset.
* `Finset.uIcc`: Unordered closed interval as a finset.

In a `LocallyFiniteOrderTop`,
* `Finset.Ici`: Closed-infinite interval as a finset.
* `Finset.Ioi`: Open-infinite interval as a finset.

In a `LocallyFiniteOrderBot`,
* `Finset.Iic`: Infinite-open interval as a finset.
* `Finset.Iio`: Infinite-closed interval as a finset.

## Instances

A `LocallyFiniteOrder` instance can be built
* for a subtype of a locally finite order. See `Subtype.locallyFiniteOrder`.
* for the product of two locally finite orders. See `Prod.locallyFiniteOrder`.
* for any fintype (but not as an instance). See `Fintype.toLocallyFiniteOrder`.
* from a definition of `Finset.Icc` alone. See `LocallyFiniteOrder.ofIcc`.
* by pulling back `LocallyFiniteOrder β` through an order embedding `f : α →o β`. See
  `OrderEmbedding.locallyFiniteOrder`.

Instances for concrete types are proved in their respective files:
* `ℕ` is in `Order.Interval.Finset.Nat`
* `ℤ` is in `Data.Int.Interval`
* `ℕ+` is in `Data.PNat.Interval`
* `Fin n` is in `Order.Interval.Finset.Fin`
* `Finset α` is in `Data.Finset.Interval`
* `Σ i, α i` is in `Data.Sigma.Interval`
Along, you will find lemmas about the cardinality of those finite intervals.

## TODO

Provide the `LocallyFiniteOrder` instance for `α ×ₗ β` where `LocallyFiniteOrder α` and
`Fintype β`.

Provide the `LocallyFiniteOrder` instance for `α →₀ β` where `β` is locally finite. Provide the
`LocallyFiniteOrder` instance for `Π₀ i, β i` where all the `β i` are locally finite.

From `LinearOrder α`, `NoMaxOrder α`, `LocallyFiniteOrder α`, we can also define an
order isomorphism `α ≃ ℕ` or `α ≃ ℤ`, depending on whether we have `OrderBot α` or
`NoMinOrder α` and `Nonempty α`. When `OrderBot α`, we can match `a : α` to `(Iio a).card`.

We can provide `SuccOrder α` from `LinearOrder α` and `LocallyFiniteOrder α` using

```lean
lemma exists_min_greater [LinearOrder α] [LocallyFiniteOrder α] {x ub : α} (hx : x < ub) :
    ∃ lub, x < lub ∧ ∀ y, x < y → lub ≤ y := by
  -- very non golfed
  have h : (Finset.Ioc x ub).Nonempty := ⟨ub, Finset.mem_Ioc.2 ⟨hx, le_rfl⟩⟩
  use Finset.min' (Finset.Ioc x ub) h
  constructor
  · exact (Finset.mem_Ioc.mp <| Finset.min'_mem _ h).1
  rintro y hxy
  obtain hy | hy := le_total y ub
  · refine Finset.min'_le (Ioc x ub) y ?_
    simp [*] at *
  · exact (Finset.min'_le _ _ (Finset.mem_Ioc.2 ⟨hx, le_rfl⟩)).trans hy
```
Note that the converse is not true. Consider `{-2^z | z : ℤ} ∪ {2^z | z : ℤ}`. Any element has a
successor (and actually a predecessor as well), so it is a `SuccOrder`, but it's not locally finite
as `Icc (-1) 1` is infinite.
-/

set_option autoImplicit true


open Finset Function

/-- This is a mixin class describing a locally finite order,
that is, is an order where bounded intervals are finite.
When you don't care too much about definitional equality, you can use `LocallyFiniteOrder.ofIcc` or
`LocallyFiniteOrder.ofFiniteIcc` to build a locally finite order from just `Finset.Icc`. -/
class LocallyFiniteOrder (α : Type*) [Preorder α] where
  /-- Left-closed right-closed interval -/
  finsetIcc : α → α → Finset α
  /-- Left-closed right-open interval -/
  finsetIco : α → α → Finset α
  /-- Left-open right-closed interval -/
  finsetIoc : α → α → Finset α
  /-- Left-open right-open interval -/
  finsetIoo : α → α → Finset α
  /-- `x ∈ finsetIcc a b ↔ a ≤ x ∧ x ≤ b` -/
  finset_mem_Icc : ∀ a b x : α, x ∈ finsetIcc a b ↔ a ≤ x ∧ x ≤ b
  /-- `x ∈ finsetIco a b ↔ a ≤ x ∧ x < b` -/
  finset_mem_Ico : ∀ a b x : α, x ∈ finsetIco a b ↔ a ≤ x ∧ x < b
  /-- `x ∈ finsetIoc a b ↔ a < x ∧ x ≤ b` -/
  finset_mem_Ioc : ∀ a b x : α, x ∈ finsetIoc a b ↔ a < x ∧ x ≤ b
  /-- `x ∈ finsetIoo a b ↔ a < x ∧ x < b` -/
  finset_mem_Ioo : ∀ a b x : α, x ∈ finsetIoo a b ↔ a < x ∧ x < b
#align locally_finite_order LocallyFiniteOrder

/-- This mixin class describes an order where all intervals bounded below are finite. This is
slightly weaker than `LocallyFiniteOrder` + `OrderTop` as it allows empty types. -/
class LocallyFiniteOrderTop (α : Type*) [Preorder α] where
  /-- Left-open right-infinite interval -/
  finsetIoi : α → Finset α
  /-- Left-closed right-infinite interval -/
  finsetIci : α → Finset α
  /-- `x ∈ finsetIci a ↔ a ≤ x` -/
  finset_mem_Ici : ∀ a x : α, x ∈ finsetIci a ↔ a ≤ x
  /-- `x ∈ finsetIoi a ↔ a < x` -/
  finset_mem_Ioi : ∀ a x : α, x ∈ finsetIoi a ↔ a < x
#align locally_finite_order_top LocallyFiniteOrderTop

/-- This mixin class describes an order where all intervals bounded above are finite. This is
slightly weaker than `LocallyFiniteOrder` + `OrderBot` as it allows empty types. -/
class LocallyFiniteOrderBot (α : Type*) [Preorder α] where
  /-- Left-infinite right-open interval -/
  finsetIio : α → Finset α
  /-- Left-infinite right-closed interval -/
  finsetIic : α → Finset α
  /-- `x ∈ finsetIic a ↔ x ≤ a` -/
  finset_mem_Iic : ∀ a x : α, x ∈ finsetIic a ↔ x ≤ a
  /-- `x ∈ finsetIio a ↔ x < a` -/
  finset_mem_Iio : ∀ a x : α, x ∈ finsetIio a ↔ x < a
#align locally_finite_order_bot LocallyFiniteOrderBot

/-- A constructor from a definition of `Finset.Icc` alone, the other ones being derived by removing
the ends. As opposed to `LocallyFiniteOrder.ofIcc`, this one requires `DecidableRel (· ≤ ·)` but
only `Preorder`. -/
def LocallyFiniteOrder.ofIcc' (α : Type*) [Preorder α] [DecidableRel ((· ≤ ·) : α → α → Prop)]
    (finsetIcc : α → α → Finset α) (mem_Icc : ∀ a b x, x ∈ finsetIcc a b ↔ a ≤ x ∧ x ≤ b) :
    LocallyFiniteOrder α :=
  { finsetIcc
    finsetIco := fun a b => (finsetIcc a b).filter fun x => ¬b ≤ x
    finsetIoc := fun a b => (finsetIcc a b).filter fun x => ¬x ≤ a
    finsetIoo := fun a b => (finsetIcc a b).filter fun x => ¬x ≤ a ∧ ¬b ≤ x
    finset_mem_Icc := mem_Icc
    finset_mem_Ico := fun a b x => by rw [Finset.mem_filter, mem_Icc, and_assoc, lt_iff_le_not_le]
    finset_mem_Ioc := fun a b x => by
      rw [Finset.mem_filter, mem_Icc, and_right_comm, lt_iff_le_not_le]
    finset_mem_Ioo := fun a b x => by
      rw [Finset.mem_filter, mem_Icc, and_and_and_comm, lt_iff_le_not_le, lt_iff_le_not_le] }
#align locally_finite_order.of_Icc' LocallyFiniteOrder.ofIcc'

/-- A constructor from a definition of `Finset.Icc` alone, the other ones being derived by removing
the ends. As opposed to `LocallyFiniteOrder.ofIcc'`, this one requires `PartialOrder` but only
`DecidableEq`. -/
def LocallyFiniteOrder.ofIcc (α : Type*) [PartialOrder α] [DecidableEq α]
    (finsetIcc : α → α → Finset α) (mem_Icc : ∀ a b x, x ∈ finsetIcc a b ↔ a ≤ x ∧ x ≤ b) :
    LocallyFiniteOrder α :=
  { finsetIcc
    finsetIco := fun a b => (finsetIcc a b).filter fun x => x ≠ b
    finsetIoc := fun a b => (finsetIcc a b).filter fun x => a ≠ x
    finsetIoo := fun a b => (finsetIcc a b).filter fun x => a ≠ x ∧ x ≠ b
    finset_mem_Icc := mem_Icc
    finset_mem_Ico := fun a b x => by rw [Finset.mem_filter, mem_Icc, and_assoc, lt_iff_le_and_ne]
    finset_mem_Ioc := fun a b x => by
      rw [Finset.mem_filter, mem_Icc, and_right_comm, lt_iff_le_and_ne]
    finset_mem_Ioo := fun a b x => by
      rw [Finset.mem_filter, mem_Icc, and_and_and_comm, lt_iff_le_and_ne, lt_iff_le_and_ne] }
#align locally_finite_order.of_Icc LocallyFiniteOrder.ofIcc

/-- A constructor from a definition of `Finset.Ici` alone, the other ones being derived by removing
the ends. As opposed to `LocallyFiniteOrderTop.ofIci`, this one requires `DecidableRel (· ≤ ·)` but
only `Preorder`. -/
def LocallyFiniteOrderTop.ofIci' (α : Type*) [Preorder α] [DecidableRel ((· ≤ ·) : α → α → Prop)]
    (finsetIci : α → Finset α) (mem_Ici : ∀ a x, x ∈ finsetIci a ↔ a ≤ x) :
    LocallyFiniteOrderTop α :=
  { finsetIci
    finsetIoi := fun a => (finsetIci a).filter fun x => ¬x ≤ a
    finset_mem_Ici := mem_Ici
    finset_mem_Ioi := fun a x => by rw [mem_filter, mem_Ici, lt_iff_le_not_le] }
#align locally_finite_order_top.of_Ici' LocallyFiniteOrderTop.ofIci'

/-- A constructor from a definition of `Finset.Ici` alone, the other ones being derived by removing
the ends. As opposed to `LocallyFiniteOrderTop.ofIci'`, this one requires `PartialOrder` but
only `DecidableEq`. -/
def LocallyFiniteOrderTop.ofIci (α : Type*) [PartialOrder α] [DecidableEq α]
    (finsetIci : α → Finset α) (mem_Ici : ∀ a x, x ∈ finsetIci a ↔ a ≤ x) :
    LocallyFiniteOrderTop α :=
  { finsetIci
    finsetIoi := fun a => (finsetIci a).filter fun x => a ≠ x
    finset_mem_Ici := mem_Ici
    finset_mem_Ioi := fun a x => by rw [mem_filter, mem_Ici, lt_iff_le_and_ne] }
#align locally_finite_order_top.of_Ici LocallyFiniteOrderTop.ofIci

/-- A constructor from a definition of `Finset.Iic` alone, the other ones being derived by removing
the ends. As opposed to `LocallyFiniteOrderBot.ofIic`, this one requires `DecidableRel (· ≤ ·)` but
only `Preorder`. -/
def LocallyFiniteOrderBot.ofIic' (α : Type*) [Preorder α] [DecidableRel ((· ≤ ·) : α → α → Prop)]
    (finsetIic : α → Finset α) (mem_Iic : ∀ a x, x ∈ finsetIic a ↔ x ≤ a) :
    LocallyFiniteOrderBot α :=
  { finsetIic
    finsetIio := fun a => (finsetIic a).filter fun x => ¬a ≤ x
    finset_mem_Iic := mem_Iic
    finset_mem_Iio := fun a x => by rw [mem_filter, mem_Iic, lt_iff_le_not_le] }
#align locally_finite_order_bot.of_Iic' LocallyFiniteOrderBot.ofIic'

/-- A constructor from a definition of `Finset.Iic` alone, the other ones being derived by removing
the ends. As opposed to `LocallyFiniteOrderBot.ofIic'`, this one requires `PartialOrder` but
only `DecidableEq`. -/
def LocallyFiniteOrderBot.ofIic (α : Type*) [PartialOrder α] [DecidableEq α]
    (finsetIic : α → Finset α) (mem_Iic : ∀ a x, x ∈ finsetIic a ↔ x ≤ a) :
    LocallyFiniteOrderBot α :=
  { finsetIic
    finsetIio := fun a => (finsetIic a).filter fun x => x ≠ a
    finset_mem_Iic := mem_Iic
    finset_mem_Iio := fun a x => by rw [mem_filter, mem_Iic, lt_iff_le_and_ne] }
-- Note: this was in the wrong namespace in Mathlib 3.
#align locally_finite_order_top.of_Iic LocallyFiniteOrderBot.ofIic

variable {α β : Type*}

-- See note [reducible non-instances]
/-- An empty type is locally finite.

This is not an instance as it would not be defeq to more specific instances. -/
protected abbrev IsEmpty.toLocallyFiniteOrder [Preorder α] [IsEmpty α] : LocallyFiniteOrder α where
  finsetIcc := isEmptyElim
  finsetIco := isEmptyElim
  finsetIoc := isEmptyElim
  finsetIoo := isEmptyElim
  finset_mem_Icc := isEmptyElim
  finset_mem_Ico := isEmptyElim
  finset_mem_Ioc := isEmptyElim
  finset_mem_Ioo := isEmptyElim
#align is_empty.to_locally_finite_order IsEmpty.toLocallyFiniteOrder

-- See note [reducible non-instances]
/-- An empty type is locally finite.

This is not an instance as it would not be defeq to more specific instances. -/
protected abbrev IsEmpty.toLocallyFiniteOrderTop [Preorder α] [IsEmpty α] :
    LocallyFiniteOrderTop α where
  finsetIci := isEmptyElim
  finsetIoi := isEmptyElim
  finset_mem_Ici := isEmptyElim
  finset_mem_Ioi := isEmptyElim
#align is_empty.to_locally_finite_order_top IsEmpty.toLocallyFiniteOrderTop

-- See note [reducible non-instances]
/-- An empty type is locally finite.

This is not an instance as it would not be defeq to more specific instances. -/
protected abbrev IsEmpty.toLocallyFiniteOrderBot [Preorder α] [IsEmpty α] :
    LocallyFiniteOrderBot α where
  finsetIic := isEmptyElim
  finsetIio := isEmptyElim
  finset_mem_Iic := isEmptyElim
  finset_mem_Iio := isEmptyElim
#align is_empty.to_locally_finite_order_bot IsEmpty.toLocallyFiniteOrderBot

/-! ### Intervals as finsets -/


namespace Finset

section Preorder

variable [Preorder α]

section LocallyFiniteOrder

variable [LocallyFiniteOrder α] {a b x : α}

/-- The finset of elements `x` such that `a ≤ x` and `x ≤ b`. Basically `Set.Icc a b` as a finset.
-/
def Icc (a b : α) : Finset α :=
  LocallyFiniteOrder.finsetIcc a b
#align finset.Icc Finset.Icc

/-- The finset of elements `x` such that `a ≤ x` and `x < b`. Basically `Set.Ico a b` as a finset.
-/
def Ico (a b : α) : Finset α :=
  LocallyFiniteOrder.finsetIco a b
#align finset.Ico Finset.Ico

/-- The finset of elements `x` such that `a < x` and `x ≤ b`. Basically `Set.Ioc a b` as a finset.
-/
def Ioc (a b : α) : Finset α :=
  LocallyFiniteOrder.finsetIoc a b
#align finset.Ioc Finset.Ioc

/-- The finset of elements `x` such that `a < x` and `x < b`. Basically `Set.Ioo a b` as a finset.
-/
def Ioo (a b : α) : Finset α :=
  LocallyFiniteOrder.finsetIoo a b
#align finset.Ioo Finset.Ioo

@[simp]
theorem mem_Icc : x ∈ Icc a b ↔ a ≤ x ∧ x ≤ b :=
  LocallyFiniteOrder.finset_mem_Icc a b x
#align finset.mem_Icc Finset.mem_Icc

@[simp]
theorem mem_Ico : x ∈ Ico a b ↔ a ≤ x ∧ x < b :=
  LocallyFiniteOrder.finset_mem_Ico a b x
#align finset.mem_Ico Finset.mem_Ico

@[simp]
theorem mem_Ioc : x ∈ Ioc a b ↔ a < x ∧ x ≤ b :=
  LocallyFiniteOrder.finset_mem_Ioc a b x
#align finset.mem_Ioc Finset.mem_Ioc

@[simp]
theorem mem_Ioo : x ∈ Ioo a b ↔ a < x ∧ x < b :=
  LocallyFiniteOrder.finset_mem_Ioo a b x
#align finset.mem_Ioo Finset.mem_Ioo

@[simp, norm_cast]
theorem coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b :=
  Set.ext fun _ => mem_Icc
#align finset.coe_Icc Finset.coe_Icc

@[simp, norm_cast]
theorem coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b :=
  Set.ext fun _ => mem_Ico
#align finset.coe_Ico Finset.coe_Ico

@[simp, norm_cast]
theorem coe_Ioc (a b : α) : (Ioc a b : Set α) = Set.Ioc a b :=
  Set.ext fun _ => mem_Ioc
#align finset.coe_Ioc Finset.coe_Ioc

@[simp, norm_cast]
theorem coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b :=
  Set.ext fun _ => mem_Ioo
#align finset.coe_Ioo Finset.coe_Ioo

end LocallyFiniteOrder

section LocallyFiniteOrderTop

variable [LocallyFiniteOrderTop α] {a x : α}

/-- The finset of elements `x` such that `a ≤ x`. Basically `Set.Ici a` as a finset. -/
def Ici (a : α) : Finset α :=
  LocallyFiniteOrderTop.finsetIci a
#align finset.Ici Finset.Ici

/-- The finset of elements `x` such that `a < x`. Basically `Set.Ioi a` as a finset. -/
def Ioi (a : α) : Finset α :=
  LocallyFiniteOrderTop.finsetIoi a
#align finset.Ioi Finset.Ioi

@[simp]
theorem mem_Ici : x ∈ Ici a ↔ a ≤ x :=
  LocallyFiniteOrderTop.finset_mem_Ici _ _
#align finset.mem_Ici Finset.mem_Ici

@[simp]
theorem mem_Ioi : x ∈ Ioi a ↔ a < x :=
  LocallyFiniteOrderTop.finset_mem_Ioi _ _
#align finset.mem_Ioi Finset.mem_Ioi

@[simp, norm_cast]
theorem coe_Ici (a : α) : (Ici a : Set α) = Set.Ici a :=
  Set.ext fun _ => mem_Ici
#align finset.coe_Ici Finset.coe_Ici

@[simp, norm_cast]
theorem coe_Ioi (a : α) : (Ioi a : Set α) = Set.Ioi a :=
  Set.ext fun _ => mem_Ioi
#align finset.coe_Ioi Finset.coe_Ioi

end LocallyFiniteOrderTop

section LocallyFiniteOrderBot

variable [LocallyFiniteOrderBot α] {a x : α}

/-- The finset of elements `x` such that `a ≤ x`. Basically `Set.Iic a` as a finset. -/
def Iic (a : α) : Finset α :=
  LocallyFiniteOrderBot.finsetIic a
#align finset.Iic Finset.Iic

/-- The finset of elements `x` such that `a < x`. Basically `Set.Iio a` as a finset. -/
def Iio (a : α) : Finset α :=
  LocallyFiniteOrderBot.finsetIio a
#align finset.Iio Finset.Iio

@[simp]
theorem mem_Iic : x ∈ Iic a ↔ x ≤ a :=
  LocallyFiniteOrderBot.finset_mem_Iic _ _
#align finset.mem_Iic Finset.mem_Iic

@[simp]
theorem mem_Iio : x ∈ Iio a ↔ x < a :=
  LocallyFiniteOrderBot.finset_mem_Iio _ _
#align finset.mem_Iio Finset.mem_Iio

@[simp, norm_cast]
theorem coe_Iic (a : α) : (Iic a : Set α) = Set.Iic a :=
  Set.ext fun _ => mem_Iic
#align finset.coe_Iic Finset.coe_Iic

@[simp, norm_cast]
theorem coe_Iio (a : α) : (Iio a : Set α) = Set.Iio a :=
  Set.ext fun _ => mem_Iio
#align finset.coe_Iio Finset.coe_Iio

end LocallyFiniteOrderBot

section OrderTop

variable [LocallyFiniteOrder α] [OrderTop α] {a x : α}

-- See note [lower priority instance]
instance (priority := 100) _root_.LocallyFiniteOrder.toLocallyFiniteOrderTop :
    LocallyFiniteOrderTop α where
  finsetIci b := Icc b ⊤
  finsetIoi b := Ioc b ⊤
  finset_mem_Ici a x := by rw [mem_Icc, and_iff_left le_top]
  finset_mem_Ioi a x := by rw [mem_Ioc, and_iff_left le_top]
#align locally_finite_order.to_locally_finite_order_top LocallyFiniteOrder.toLocallyFiniteOrderTop

theorem Ici_eq_Icc (a : α) : Ici a = Icc a ⊤ :=
  rfl
#align finset.Ici_eq_Icc Finset.Ici_eq_Icc

theorem Ioi_eq_Ioc (a : α) : Ioi a = Ioc a ⊤ :=
  rfl
#align finset.Ioi_eq_Ioc Finset.Ioi_eq_Ioc

end OrderTop

section OrderBot

variable [OrderBot α] [LocallyFiniteOrder α] {b x : α}

-- See note [lower priority instance]
instance (priority := 100) LocallyFiniteOrder.toLocallyFiniteOrderBot :
    LocallyFiniteOrderBot α where
  finsetIic := Icc ⊥
  finsetIio := Ico ⊥
  finset_mem_Iic a x := by rw [mem_Icc, and_iff_right bot_le]
  finset_mem_Iio a x := by rw [mem_Ico, and_iff_right bot_le]
#align finset.locally_finite_order.to_locally_finite_order_bot Finset.LocallyFiniteOrder.toLocallyFiniteOrderBot

theorem Iic_eq_Icc : Iic = Icc (⊥ : α) :=
  rfl
#align finset.Iic_eq_Icc Finset.Iic_eq_Icc

theorem Iio_eq_Ico : Iio = Ico (⊥ : α) :=
  rfl
#align finset.Iio_eq_Ico Finset.Iio_eq_Ico

end OrderBot

end Preorder

section Lattice

variable [Lattice α] [LocallyFiniteOrder α] {a b x : α}

/-- `Finset.uIcc a b` is the set of elements lying between `a` and `b`, with `a` and `b` included.
Note that we define it more generally in a lattice as `Finset.Icc (a ⊓ b) (a ⊔ b)`. In a
product type, `Finset.uIcc` corresponds to the bounding box of the two elements. -/
def uIcc (a b : α) : Finset α :=
  Icc (a ⊓ b) (a ⊔ b)
#align finset.uIcc Finset.uIcc

@[inherit_doc]
scoped[FinsetInterval] notation "[[" a ", " b "]]" => Finset.uIcc a b

@[simp]
theorem mem_uIcc : x ∈ uIcc a b ↔ a ⊓ b ≤ x ∧ x ≤ a ⊔ b :=
  mem_Icc
#align finset.mem_uIcc Finset.mem_uIcc

@[simp, norm_cast]
theorem coe_uIcc (a b : α) : (Finset.uIcc a b : Set α) = Set.uIcc a b :=
  coe_Icc _ _
#align finset.coe_uIcc Finset.coe_uIcc

end Lattice

end Finset

/-! ### Finiteness of `Set` intervals -/


namespace Set

section Preorder

variable [Preorder α] [LocallyFiniteOrder α] (a b : α)

instance fintypeIcc : Fintype (Icc a b) := Fintype.ofFinset (Finset.Icc a b) fun _ => Finset.mem_Icc
#align set.fintype_Icc Set.fintypeIcc

instance fintypeIco : Fintype (Ico a b) := Fintype.ofFinset (Finset.Ico a b) fun _ => Finset.mem_Ico
#align set.fintype_Ico Set.fintypeIco

instance fintypeIoc : Fintype (Ioc a b) := Fintype.ofFinset (Finset.Ioc a b) fun _ => Finset.mem_Ioc
#align set.fintype_Ioc Set.fintypeIoc

instance fintypeIoo : Fintype (Ioo a b) := Fintype.ofFinset (Finset.Ioo a b) fun _ => Finset.mem_Ioo
#align set.fintype_Ioo Set.fintypeIoo

theorem finite_Icc : (Icc a b).Finite :=
  (Icc a b).toFinite
#align set.finite_Icc Set.finite_Icc

theorem finite_Ico : (Ico a b).Finite :=
  (Ico a b).toFinite
#align set.finite_Ico Set.finite_Ico

theorem finite_Ioc : (Ioc a b).Finite :=
  (Ioc a b).toFinite
#align set.finite_Ioc Set.finite_Ioc

theorem finite_Ioo : (Ioo a b).Finite :=
  (Ioo a b).toFinite
#align set.finite_Ioo Set.finite_Ioo

end Preorder

section OrderTop

variable [Preorder α] [LocallyFiniteOrderTop α] (a : α)

instance fintypeIci : Fintype (Ici a) := Fintype.ofFinset (Finset.Ici a) fun _ => Finset.mem_Ici
#align set.fintype_Ici Set.fintypeIci

instance fintypeIoi : Fintype (Ioi a) := Fintype.ofFinset (Finset.Ioi a) fun _ => Finset.mem_Ioi
#align set.fintype_Ioi Set.fintypeIoi

theorem finite_Ici : (Ici a).Finite :=
  (Ici a).toFinite
#align set.finite_Ici Set.finite_Ici

theorem finite_Ioi : (Ioi a).Finite :=
  (Ioi a).toFinite
#align set.finite_Ioi Set.finite_Ioi

end OrderTop

section OrderBot

variable [Preorder α] [LocallyFiniteOrderBot α] (b : α)

instance fintypeIic : Fintype (Iic b) := Fintype.ofFinset (Finset.Iic b) fun _ => Finset.mem_Iic
#align set.fintype_Iic Set.fintypeIic

instance fintypeIio : Fintype (Iio b) := Fintype.ofFinset (Finset.Iio b) fun _ => Finset.mem_Iio
#align set.fintype_Iio Set.fintypeIio

theorem finite_Iic : (Iic b).Finite :=
  (Iic b).toFinite
#align set.finite_Iic Set.finite_Iic

theorem finite_Iio : (Iio b).Finite :=
  (Iio b).toFinite
#align set.finite_Iio Set.finite_Iio

end OrderBot

section Lattice
variable [Lattice α] [LocallyFiniteOrder α] (a b : α)

instance fintypeUIcc : Fintype (uIcc a b) :=
  Fintype.ofFinset (Finset.uIcc a b) fun _ => Finset.mem_uIcc
#align set.fintype_uIcc Set.fintypeUIcc

@[simp]
theorem finite_interval : (uIcc a b).Finite := (uIcc _ _).toFinite
#align set.finite_interval Set.finite_interval

end Lattice

end Set

/-! ### Instances -/


open Finset

section Preorder

variable [Preorder α] [Preorder β]

/-- A noncomputable constructor from the finiteness of all closed intervals. -/
noncomputable def LocallyFiniteOrder.ofFiniteIcc (h : ∀ a b : α, (Set.Icc a b).Finite) :
    LocallyFiniteOrder α :=
  @LocallyFiniteOrder.ofIcc' α _ (Classical.decRel _) (fun a b => (h a b).toFinset) fun a b x => by
    rw [Set.Finite.mem_toFinset, Set.mem_Icc]
#align locally_finite_order.of_finite_Icc LocallyFiniteOrder.ofFiniteIcc

/-- A fintype is a locally finite order.

This is not an instance as it would not be defeq to better instances such as
`Fin.locallyFiniteOrder`.
-/
abbrev Fintype.toLocallyFiniteOrder [Fintype α] [@DecidableRel α (· < ·)]
    [@DecidableRel α (· ≤ ·)] : LocallyFiniteOrder α where
  finsetIcc a b := (Set.Icc a b).toFinset
  finsetIco a b := (Set.Ico a b).toFinset
  finsetIoc a b := (Set.Ioc a b).toFinset
  finsetIoo a b := (Set.Ioo a b).toFinset
  finset_mem_Icc a b x := by simp only [Set.mem_toFinset, Set.mem_Icc]
  finset_mem_Ico a b x := by simp only [Set.mem_toFinset, Set.mem_Ico]
  finset_mem_Ioc a b x := by simp only [Set.mem_toFinset, Set.mem_Ioc]
  finset_mem_Ioo a b x := by simp only [Set.mem_toFinset, Set.mem_Ioo]
#align fintype.to_locally_finite_order Fintype.toLocallyFiniteOrder

instance : Subsingleton (LocallyFiniteOrder α) :=
  Subsingleton.intro fun h₀ h₁ => by
    cases' h₀ with h₀_finset_Icc h₀_finset_Ico h₀_finset_Ioc h₀_finset_Ioo
      h₀_finset_mem_Icc h₀_finset_mem_Ico h₀_finset_mem_Ioc h₀_finset_mem_Ioo
    cases' h₁ with h₁_finset_Icc h₁_finset_Ico h₁_finset_Ioc h₁_finset_Ioo
      h₁_finset_mem_Icc h₁_finset_mem_Ico h₁_finset_mem_Ioc h₁_finset_mem_Ioo
    have hIcc : h₀_finset_Icc = h₁_finset_Icc := by
      ext a b x
      rw [h₀_finset_mem_Icc, h₁_finset_mem_Icc]
    have hIco : h₀_finset_Ico = h₁_finset_Ico := by
      ext a b x
      rw [h₀_finset_mem_Ico, h₁_finset_mem_Ico]
    have hIoc : h₀_finset_Ioc = h₁_finset_Ioc := by
      ext a b x
      rw [h₀_finset_mem_Ioc, h₁_finset_mem_Ioc]
    have hIoo : h₀_finset_Ioo = h₁_finset_Ioo := by
      ext a b x
      rw [h₀_finset_mem_Ioo, h₁_finset_mem_Ioo]
    simp_rw [hIcc, hIco, hIoc, hIoo]

instance : Subsingleton (LocallyFiniteOrderTop α) :=
  Subsingleton.intro fun h₀ h₁ => by
    cases' h₀ with h₀_finset_Ioi h₀_finset_Ici h₀_finset_mem_Ici h₀_finset_mem_Ioi
    cases' h₁ with h₁_finset_Ioi h₁_finset_Ici h₁_finset_mem_Ici h₁_finset_mem_Ioi
    have hIci : h₀_finset_Ici = h₁_finset_Ici := by
      ext a b
      rw [h₀_finset_mem_Ici, h₁_finset_mem_Ici]
    have hIoi : h₀_finset_Ioi = h₁_finset_Ioi := by
      ext a b
      rw [h₀_finset_mem_Ioi, h₁_finset_mem_Ioi]
    simp_rw [hIci, hIoi]

instance : Subsingleton (LocallyFiniteOrderBot α) :=
  Subsingleton.intro fun h₀ h₁ => by
    cases' h₀ with h₀_finset_Iio h₀_finset_Iic h₀_finset_mem_Iic h₀_finset_mem_Iio
    cases' h₁ with h₁_finset_Iio h₁_finset_Iic h₁_finset_mem_Iic h₁_finset_mem_Iio
    have hIic : h₀_finset_Iic = h₁_finset_Iic := by
      ext a b
      rw [h₀_finset_mem_Iic, h₁_finset_mem_Iic]
    have hIio : h₀_finset_Iio = h₁_finset_Iio := by
      ext a b
      rw [h₀_finset_mem_Iio, h₁_finset_mem_Iio]
    simp_rw [hIic, hIio]

-- Should this be called `LocallyFiniteOrder.lift`?
/-- Given an order embedding `α ↪o β`, pulls back the `LocallyFiniteOrder` on `β` to `α`. -/
protected noncomputable def OrderEmbedding.locallyFiniteOrder [LocallyFiniteOrder β] (f : α ↪o β) :
    LocallyFiniteOrder α where
  finsetIcc a b := (Icc (f a) (f b)).preimage f (f.toEmbedding.injective.injOn _)
  finsetIco a b := (Ico (f a) (f b)).preimage f (f.toEmbedding.injective.injOn _)
  finsetIoc a b := (Ioc (f a) (f b)).preimage f (f.toEmbedding.injective.injOn _)
  finsetIoo a b := (Ioo (f a) (f b)).preimage f (f.toEmbedding.injective.injOn _)
  finset_mem_Icc a b x := by rw [mem_preimage, mem_Icc, f.le_iff_le, f.le_iff_le]
  finset_mem_Ico a b x := by rw [mem_preimage, mem_Ico, f.le_iff_le, f.lt_iff_lt]
  finset_mem_Ioc a b x := by rw [mem_preimage, mem_Ioc, f.lt_iff_lt, f.le_iff_le]
  finset_mem_Ioo a b x := by rw [mem_preimage, mem_Ioo, f.lt_iff_lt, f.lt_iff_lt]
#align order_embedding.locally_finite_order OrderEmbedding.locallyFiniteOrder

open OrderDual

section LocallyFiniteOrder

variable [LocallyFiniteOrder α] (a b : α)

/-- Note we define `Icc (toDual a) (toDual b)` as `Icc α _ _ b a` (which has type `Finset α` not
`Finset αᵒᵈ`!) instead of `(Icc b a).map toDual.toEmbedding` as this means the
following is defeq:
```
lemma this : (Icc (toDual (toDual a)) (toDual (toDual b)) : _) = (Icc a b : _) := rfl
```
-/
instance OrderDual.instLocallyFiniteOrder : LocallyFiniteOrder αᵒᵈ where
  finsetIcc a b := @Icc α _ _ (ofDual b) (ofDual a)
  finsetIco a b := @Ioc α _ _ (ofDual b) (ofDual a)
  finsetIoc a b := @Ico α _ _ (ofDual b) (ofDual a)
  finsetIoo a b := @Ioo α _ _ (ofDual b) (ofDual a)
  finset_mem_Icc _ _ _ := (mem_Icc (α := α)).trans and_comm
  finset_mem_Ico _ _ _ := (mem_Ioc (α := α)).trans and_comm
  finset_mem_Ioc _ _ _ := (mem_Ico (α := α)).trans and_comm
  finset_mem_Ioo _ _ _ := (mem_Ioo (α := α)).trans and_comm

theorem Icc_toDual : Icc (toDual a) (toDual b) = (Icc b a).map toDual.toEmbedding := map_refl.symm
#align Icc_to_dual Icc_toDual

theorem Ico_toDual : Ico (toDual a) (toDual b) = (Ioc b a).map toDual.toEmbedding := map_refl.symm
#align Ico_to_dual Ico_toDual

theorem Ioc_toDual : Ioc (toDual a) (toDual b) = (Ico b a).map toDual.toEmbedding := map_refl.symm
#align Ioc_to_dual Ioc_toDual

theorem Ioo_toDual : Ioo (toDual a) (toDual b) = (Ioo b a).map toDual.toEmbedding := map_refl.symm
#align Ioo_to_dual Ioo_toDual

theorem Icc_ofDual (a b : αᵒᵈ) : Icc (ofDual a) (ofDual b) = (Icc b a).map ofDual.toEmbedding :=
  map_refl.symm
#align Icc_of_dual Icc_ofDual

theorem Ico_ofDual (a b : αᵒᵈ) : Ico (ofDual a) (ofDual b) = (Ioc b a).map ofDual.toEmbedding :=
  map_refl.symm
#align Ico_of_dual Ico_ofDual

theorem Ioc_ofDual (a b : αᵒᵈ) : Ioc (ofDual a) (ofDual b) = (Ico b a).map ofDual.toEmbedding :=
  map_refl.symm
#align Ioc_of_dual Ioc_ofDual

theorem Ioo_ofDual (a b : αᵒᵈ) : Ioo (ofDual a) (ofDual b) = (Ioo b a).map ofDual.toEmbedding :=
  map_refl.symm
#align Ioo_of_dual Ioo_ofDual

end LocallyFiniteOrder

section LocallyFiniteOrderTop

variable [LocallyFiniteOrderTop α]

/-- Note we define `Iic (toDual a)` as `Ici a` (which has type `Finset α` not `Finset αᵒᵈ`!)
instead of `(Ici a).map toDual.toEmbedding` as this means the following is defeq:
```
lemma this : (Iic (toDual (toDual a)) : _) = (Iic a : _) := rfl
```
-/
instance OrderDual.instLocallyFiniteOrderBot : LocallyFiniteOrderBot αᵒᵈ where
  finsetIic a := @Ici α _ _ (ofDual a)
  finsetIio a := @Ioi α _ _ (ofDual a)
  finset_mem_Iic _ _ := mem_Ici (α := α)
  finset_mem_Iio _ _ := mem_Ioi (α := α)

theorem Iic_toDual (a : α) : Iic (toDual a) = (Ici a).map toDual.toEmbedding :=
  map_refl.symm
#align Iic_to_dual Iic_toDual

theorem Iio_toDual (a : α) : Iio (toDual a) = (Ioi a).map toDual.toEmbedding :=
  map_refl.symm
#align Iio_to_dual Iio_toDual

theorem Ici_ofDual (a : αᵒᵈ) : Ici (ofDual a) = (Iic a).map ofDual.toEmbedding :=
  map_refl.symm
#align Ici_of_dual Ici_ofDual

theorem Ioi_ofDual (a : αᵒᵈ) : Ioi (ofDual a) = (Iio a).map ofDual.toEmbedding :=
  map_refl.symm
#align Ioi_of_dual Ioi_ofDual

end LocallyFiniteOrderTop

section LocallyFiniteOrderTop

variable [LocallyFiniteOrderBot α]

/-- Note we define `Ici (toDual a)` as `Iic a` (which has type `Finset α` not `Finset αᵒᵈ`!)
instead of `(Iic a).map toDual.toEmbedding` as this means the following is defeq:
```
lemma this : (Ici (toDual (toDual a)) : _) = (Ici a : _) := rfl
```
-/
instance OrderDual.instLocallyFiniteOrderTop : LocallyFiniteOrderTop αᵒᵈ where
  finsetIci a := @Iic α _ _ (ofDual a)
  finsetIoi a := @Iio α _ _ (ofDual a)
  finset_mem_Ici _ _ := mem_Iic (α := α)
  finset_mem_Ioi _ _ := mem_Iio (α := α)

theorem Ici_toDual (a : α) : Ici (toDual a) = (Iic a).map toDual.toEmbedding :=
  map_refl.symm
#align Ici_to_dual Ici_toDual

theorem Ioi_toDual (a : α) : Ioi (toDual a) = (Iio a).map toDual.toEmbedding :=
  map_refl.symm
#align Ioi_to_dual Ioi_toDual

theorem Iic_ofDual (a : αᵒᵈ) : Iic (ofDual a) = (Ici a).map ofDual.toEmbedding :=
  map_refl.symm
#align Iic_of_dual Iic_ofDual

theorem Iio_ofDual (a : αᵒᵈ) : Iio (ofDual a) = (Ioi a).map ofDual.toEmbedding :=
  map_refl.symm
#align Iio_of_dual Iio_ofDual

end LocallyFiniteOrderTop

namespace Prod

instance [LocallyFiniteOrder α] [LocallyFiniteOrder β]
    [DecidableRel ((· ≤ ·) : α × β → α × β → Prop)] : LocallyFiniteOrder (α × β) :=
  LocallyFiniteOrder.ofIcc' (α × β) (fun a b => Icc a.fst b.fst ×ˢ Icc a.snd b.snd) fun a b x => by
    rw [mem_product, mem_Icc, mem_Icc, and_and_and_comm, le_def, le_def]

instance [LocallyFiniteOrderTop α] [LocallyFiniteOrderTop β]
    [DecidableRel ((· ≤ ·) : α × β → α × β → Prop)] : LocallyFiniteOrderTop (α × β) :=
  LocallyFiniteOrderTop.ofIci' (α × β) (fun a => Ici a.fst ×ˢ Ici a.snd) fun a x => by
    rw [mem_product, mem_Ici, mem_Ici, le_def]

instance [LocallyFiniteOrderBot α] [LocallyFiniteOrderBot β]
    [DecidableRel ((· ≤ ·) : α × β → α × β → Prop)] : LocallyFiniteOrderBot (α × β) :=
  LocallyFiniteOrderBot.ofIic' (α × β) (fun a => Iic a.fst ×ˢ Iic a.snd) fun a x => by
    rw [mem_product, mem_Iic, mem_Iic, le_def]

theorem Icc_eq [LocallyFiniteOrder α] [LocallyFiniteOrder β]
    [DecidableRel ((· ≤ ·) : α × β → α × β → Prop)] (p q : α × β) :
    Finset.Icc p q = Finset.Icc p.1 q.1 ×ˢ Finset.Icc p.2 q.2 :=
  rfl
#align prod.Icc_eq Prod.Icc_eq

@[simp]
theorem Icc_mk_mk [LocallyFiniteOrder α] [LocallyFiniteOrder β]
    [DecidableRel ((· ≤ ·) : α × β → α × β → Prop)] (a₁ a₂ : α) (b₁ b₂ : β) :
    Finset.Icc (a₁, b₁) (a₂, b₂) = Finset.Icc a₁ a₂ ×ˢ Finset.Icc b₁ b₂ :=
  rfl
#align prod.Icc_mk_mk Prod.Icc_mk_mk

theorem card_Icc [LocallyFiniteOrder α] [LocallyFiniteOrder β]
    [DecidableRel ((· ≤ ·) : α × β → α × β → Prop)] (p q : α × β) :
    (Finset.Icc p q).card = (Finset.Icc p.1 q.1).card * (Finset.Icc p.2 q.2).card :=
  Finset.card_product _ _
#align prod.card_Icc Prod.card_Icc

end Prod

end Preorder

namespace Prod

variable [Lattice α] [Lattice β]

theorem uIcc_eq [LocallyFiniteOrder α] [LocallyFiniteOrder β]
    [DecidableRel ((· ≤ ·) : α × β → α × β → Prop)] (p q : α × β) :
    Finset.uIcc p q = Finset.uIcc p.1 q.1 ×ˢ Finset.uIcc p.2 q.2 :=
  rfl
#align prod.uIcc_eq Prod.uIcc_eq

@[simp]
theorem uIcc_mk_mk [LocallyFiniteOrder α] [LocallyFiniteOrder β]
    [DecidableRel ((· ≤ ·) : α × β → α × β → Prop)] (a₁ a₂ : α) (b₁ b₂ : β) :
    Finset.uIcc (a₁, b₁) (a₂, b₂) = Finset.uIcc a₁ a₂ ×ˢ Finset.uIcc b₁ b₂ :=
  rfl
#align prod.uIcc_mk_mk Prod.uIcc_mk_mk

theorem card_uIcc [LocallyFiniteOrder α] [LocallyFiniteOrder β]
    [DecidableRel ((· ≤ ·) : α × β → α × β → Prop)] (p q : α × β) :
    (Finset.uIcc p q).card = (Finset.uIcc p.1 q.1).card * (Finset.uIcc p.2 q.2).card :=
  Prod.card_Icc _ _
#align prod.card_uIcc Prod.card_uIcc

end Prod

/-!
#### `WithTop`, `WithBot`

Adding a `⊤` to a locally finite `OrderTop` keeps it locally finite.
Adding a `⊥` to a locally finite `OrderBot` keeps it locally finite.
-/


namespace WithTop

variable (α) [PartialOrder α] [OrderTop α] [LocallyFiniteOrder α]

-- Porting note: removed attribute [local match_pattern] coe

attribute [local simp] Option.mem_iff

private lemma aux (x : α) (p : α → Prop) :
    (∃ a : α, p a ∧ Option.some a = Option.some x) ↔ p x := by
  -- Porting note: `simp [Option.some_inj]` has no effect
  constructor
  · rintro ⟨x', hx, hx'⟩
    obtain rfl := Option.some_inj.mp hx'
    exact hx
  · exact fun h => ⟨x, h, rfl⟩

instance locallyFiniteOrder : LocallyFiniteOrder (WithTop α) where
  finsetIcc a b :=
    match a, b with
    | ⊤, ⊤ => {⊤}
    | ⊤, (b : α) => ∅
    | (a : α), ⊤ => insertNone (Ici a)
    | (a : α), (b : α) => (Icc a b).map Embedding.some
  finsetIco a b :=
    match a, b with
    | ⊤, _ => ∅
    | (a : α), ⊤ => (Ici a).map Embedding.some
    | (a : α), (b : α) => (Ico a b).map Embedding.some
  finsetIoc a b :=
    match a, b with
    | ⊤, _ => ∅
    | (a : α), ⊤ => insertNone (Ioi a)
    | (a : α), (b : α) => (Ioc a b).map Embedding.some
  finsetIoo a b :=
    match a, b with
    | ⊤, _ => ∅
    | (a : α), ⊤ => (Ioi a).map Embedding.some
    | (a : α), (b : α) => (Ioo a b).map Embedding.some
  -- Porting note: the proofs below got much worse
  finset_mem_Icc a b x :=
    match a, b, x with
    | ⊤, ⊤, x => mem_singleton.trans (le_antisymm_iff.trans and_comm)
    | ⊤, (b : α), x =>
      iff_of_false (not_mem_empty _) fun h => (h.1.trans h.2).not_lt <| coe_lt_top _
    | (a : α), ⊤, ⊤ => by simp [WithTop.some, WithTop.top, insertNone]
    | (a : α), ⊤, (x : α) => by
        simp only [some_eq_coe, le_eq_subset, coe_le_coe, le_top, and_true]
        rw [← some_eq_coe, some_mem_insertNone, mem_Ici]
    | (a : α), (b : α), ⊤ => by
        simp only [Embedding.some, mem_map, mem_Icc, and_false, exists_const, some, le_top,
          top_le_iff]
    | (a : α), (b : α), (x : α) => by
        simp only [some_eq_coe, le_eq_subset, Embedding.some, mem_map, mem_Icc, Embedding.coeFn_mk,
          coe_le_coe]
        -- This used to be in the above `simp` before leanprover/lean4#2644
        erw [aux]
  finset_mem_Ico a b x :=
    match a, b, x with
    | ⊤, b, x => iff_of_false (not_mem_empty _) fun h => not_top_lt <| h.1.trans_lt h.2
    | (a : α), ⊤, ⊤ => by simp [some, Embedding.some]
    | (a : α), ⊤, (x : α) => by
        simp only [some_eq_coe, none_eq_top, Embedding.some, mem_map, mem_Ici, Embedding.coeFn_mk,
          coe_le_coe, aux, coe_lt_top, and_true]
        -- This used to be in the above `simp` before leanprover/lean4#2644
        erw [aux]
    | (a : α), (b : α), ⊤ => by simp [some, Embedding.some]
    | (a : α), (b : α), (x : α) => by simp [some, Embedding.some, aux]
                                      -- This used to be in the above `simp` before
                                      -- leanprover/lean4#2644
                                      erw [aux]
  finset_mem_Ioc a b x :=
    match a, b, x with
    | ⊤, b, x => iff_of_false (not_mem_empty _) fun h => not_top_lt <| h.1.trans_le h.2
    | (a : α), ⊤, ⊤ => by simp [some, insertNone, top]
    | (a : α), ⊤, (x : α) => by simp [some, Embedding.some, insertNone, aux]
                                -- This used to be in the above `simp` before
                                -- leanprover/lean4#2644
                                erw [aux]
    | (a : α), (b : α), ⊤ => by simp [some, Embedding.some, insertNone]
    | (a : α), (b : α), (x : α) => by simp [some, Embedding.some, insertNone, aux]
                                      -- This used to be in the above `simp` before
                                      -- leanprover/lean4#2644
                                      erw [aux]
  finset_mem_Ioo a b x :=
    match a, b, x with
    | ⊤, b, x => iff_of_false (not_mem_empty _) fun h => not_top_lt <| h.1.trans h.2
    | (a : α), ⊤, ⊤ => by simp [some, Embedding.some, insertNone]
    | (a : α), ⊤, (x : α) => by simp [some, Embedding.some, insertNone, aux, top]
                                -- This used to be in the above `simp` before
                                -- leanprover/lean4#2644
                                erw [aux]
    | (a : α), (b : α), ⊤ => by simp [some, Embedding.some, insertNone]
    | (a : α), (b : α), (x : α) => by
      simp [some, Embedding.some, insertNone, aux]
      -- This used to be in the above `simp` before
      -- leanprover/lean4#2644
      erw [aux]

variable (a b : α)

theorem Icc_coe_top : Icc (a : WithTop α) ⊤ = insertNone (Ici a) :=
  rfl
#align with_top.Icc_coe_top WithTop.Icc_coe_top

theorem Icc_coe_coe : Icc (a : WithTop α) b = (Icc a b).map Embedding.some :=
  rfl
#align with_top.Icc_coe_coe WithTop.Icc_coe_coe

theorem Ico_coe_top : Ico (a : WithTop α) ⊤ = (Ici a).map Embedding.some :=
  rfl
#align with_top.Ico_coe_top WithTop.Ico_coe_top

theorem Ico_coe_coe : Ico (a : WithTop α) b = (Ico a b).map Embedding.some :=
  rfl
#align with_top.Ico_coe_coe WithTop.Ico_coe_coe

theorem Ioc_coe_top : Ioc (a : WithTop α) ⊤ = insertNone (Ioi a) :=
  rfl
#align with_top.Ioc_coe_top WithTop.Ioc_coe_top

theorem Ioc_coe_coe : Ioc (a : WithTop α) b = (Ioc a b).map Embedding.some :=
  rfl
#align with_top.Ioc_coe_coe WithTop.Ioc_coe_coe

theorem Ioo_coe_top : Ioo (a : WithTop α) ⊤ = (Ioi a).map Embedding.some :=
  rfl
#align with_top.Ioo_coe_top WithTop.Ioo_coe_top

theorem Ioo_coe_coe : Ioo (a : WithTop α) b = (Ioo a b).map Embedding.some :=
  rfl
#align with_top.Ioo_coe_coe WithTop.Ioo_coe_coe

end WithTop

namespace WithBot

variable (α) [PartialOrder α] [OrderBot α] [LocallyFiniteOrder α]

instance instLocallyFiniteOrder : LocallyFiniteOrder (WithBot α) :=
  OrderDual.instLocallyFiniteOrder (α := WithTop αᵒᵈ)

variable (a b : α)

theorem Icc_bot_coe : Icc (⊥ : WithBot α) b = insertNone (Iic b) :=
  rfl
#align with_bot.Icc_bot_coe WithBot.Icc_bot_coe

theorem Icc_coe_coe : Icc (a : WithBot α) b = (Icc a b).map Embedding.some :=
  rfl
#align with_bot.Icc_coe_coe WithBot.Icc_coe_coe

theorem Ico_bot_coe : Ico (⊥ : WithBot α) b = insertNone (Iio b) :=
  rfl
#align with_bot.Ico_bot_coe WithBot.Ico_bot_coe

theorem Ico_coe_coe : Ico (a : WithBot α) b = (Ico a b).map Embedding.some :=
  rfl
#align with_bot.Ico_coe_coe WithBot.Ico_coe_coe

theorem Ioc_bot_coe : Ioc (⊥ : WithBot α) b = (Iic b).map Embedding.some :=
  rfl
#align with_bot.Ioc_bot_coe WithBot.Ioc_bot_coe

theorem Ioc_coe_coe : Ioc (a : WithBot α) b = (Ioc a b).map Embedding.some :=
  rfl
#align with_bot.Ioc_coe_coe WithBot.Ioc_coe_coe

theorem Ioo_bot_coe : Ioo (⊥ : WithBot α) b = (Iio b).map Embedding.some :=
  rfl
#align with_bot.Ioo_bot_coe WithBot.Ioo_bot_coe

theorem Ioo_coe_coe : Ioo (a : WithBot α) b = (Ioo a b).map Embedding.some :=
  rfl
#align with_bot.Ioo_coe_coe WithBot.Ioo_coe_coe

end WithBot

namespace OrderIso

variable [Preorder α] [Preorder β]

/-! #### Transfer locally finite orders across order isomorphisms -/


-- See note [reducible non-instances]
/-- Transfer `LocallyFiniteOrder` across an `OrderIso`. -/
abbrev locallyFiniteOrder [LocallyFiniteOrder β] (f : α ≃o β) : LocallyFiniteOrder α where
  finsetIcc a b := (Icc (f a) (f b)).map f.symm.toEquiv.toEmbedding
  finsetIco a b := (Ico (f a) (f b)).map f.symm.toEquiv.toEmbedding
  finsetIoc a b := (Ioc (f a) (f b)).map f.symm.toEquiv.toEmbedding
  finsetIoo a b := (Ioo (f a) (f b)).map f.symm.toEquiv.toEmbedding
  finset_mem_Icc := by simp
  finset_mem_Ico := by simp
  finset_mem_Ioc := by simp
  finset_mem_Ioo := by simp
#align order_iso.locally_finite_order OrderIso.locallyFiniteOrder

-- See note [reducible non-instances]
/-- Transfer `LocallyFiniteOrderTop` across an `OrderIso`. -/
abbrev locallyFiniteOrderTop [LocallyFiniteOrderTop β] (f : α ≃o β) : LocallyFiniteOrderTop α where
  finsetIci a := (Ici (f a)).map f.symm.toEquiv.toEmbedding
  finsetIoi a := (Ioi (f a)).map f.symm.toEquiv.toEmbedding
  finset_mem_Ici := by simp
  finset_mem_Ioi := by simp
#align order_iso.locally_finite_order_top OrderIso.locallyFiniteOrderTop

-- See note [reducible non-instances]
/-- Transfer `LocallyFiniteOrderBot` across an `OrderIso`. -/
abbrev locallyFiniteOrderBot [LocallyFiniteOrderBot β] (f : α ≃o β) : LocallyFiniteOrderBot α where
  finsetIic a := (Iic (f a)).map f.symm.toEquiv.toEmbedding
  finsetIio a := (Iio (f a)).map f.symm.toEquiv.toEmbedding
  finset_mem_Iic := by simp
  finset_mem_Iio := by simp
#align order_iso.locally_finite_order_bot OrderIso.locallyFiniteOrderBot

end OrderIso

/-! #### Subtype of a locally finite order -/


variable [Preorder α] (p : α → Prop) [DecidablePred p]

instance Subtype.instLocallyFiniteOrder [LocallyFiniteOrder α] :
    LocallyFiniteOrder (Subtype p) where
  finsetIcc a b := (Icc (a : α) b).subtype p
  finsetIco a b := (Ico (a : α) b).subtype p
  finsetIoc a b := (Ioc (a : α) b).subtype p
  finsetIoo a b := (Ioo (a : α) b).subtype p
  finset_mem_Icc a b x := by simp_rw [Finset.mem_subtype, mem_Icc, Subtype.coe_le_coe]
  finset_mem_Ico a b x := by
    simp_rw [Finset.mem_subtype, mem_Ico, Subtype.coe_le_coe, Subtype.coe_lt_coe]
  finset_mem_Ioc a b x := by
    simp_rw [Finset.mem_subtype, mem_Ioc, Subtype.coe_le_coe, Subtype.coe_lt_coe]
  finset_mem_Ioo a b x := by simp_rw [Finset.mem_subtype, mem_Ioo, Subtype.coe_lt_coe]

instance Subtype.instLocallyFiniteOrderTop [LocallyFiniteOrderTop α] :
    LocallyFiniteOrderTop (Subtype p) where
  finsetIci a := (Ici (a : α)).subtype p
  finsetIoi a := (Ioi (a : α)).subtype p
  finset_mem_Ici a x := by simp_rw [Finset.mem_subtype, mem_Ici, Subtype.coe_le_coe]
  finset_mem_Ioi a x := by simp_rw [Finset.mem_subtype, mem_Ioi, Subtype.coe_lt_coe]

instance Subtype.instLocallyFiniteOrderBot [LocallyFiniteOrderBot α] :
    LocallyFiniteOrderBot (Subtype p) where
  finsetIic a := (Iic (a : α)).subtype p
  finsetIio a := (Iio (a : α)).subtype p
  finset_mem_Iic a x := by simp_rw [Finset.mem_subtype, mem_Iic, Subtype.coe_le_coe]
  finset_mem_Iio a x := by simp_rw [Finset.mem_subtype, mem_Iio, Subtype.coe_lt_coe]

namespace Finset

section LocallyFiniteOrder

variable [LocallyFiniteOrder α] (a b : Subtype p)

theorem subtype_Icc_eq : Icc a b = (Icc (a : α) b).subtype p :=
  rfl
#align finset.subtype_Icc_eq Finset.subtype_Icc_eq

theorem subtype_Ico_eq : Ico a b = (Ico (a : α) b).subtype p :=
  rfl
#align finset.subtype_Ico_eq Finset.subtype_Ico_eq

theorem subtype_Ioc_eq : Ioc a b = (Ioc (a : α) b).subtype p :=
  rfl
#align finset.subtype_Ioc_eq Finset.subtype_Ioc_eq

theorem subtype_Ioo_eq : Ioo a b = (Ioo (a : α) b).subtype p :=
  rfl
#align finset.subtype_Ioo_eq Finset.subtype_Ioo_eq

variable (hp : ∀ ⦃a b x⦄, a ≤ x → x ≤ b → p a → p b → p x)

theorem map_subtype_embedding_Icc : (Icc a b).map (Embedding.subtype p) = (Icc a b : Finset α) := by
  rw [subtype_Icc_eq]
  refine Finset.subtype_map_of_mem fun x hx => ?_
  rw [mem_Icc] at hx
  exact hp hx.1 hx.2 a.prop b.prop
#align finset.map_subtype_embedding_Icc Finset.map_subtype_embedding_Icc

theorem map_subtype_embedding_Ico : (Ico a b).map (Embedding.subtype p) = (Ico a b : Finset α) := by
  rw [subtype_Ico_eq]
  refine Finset.subtype_map_of_mem fun x hx => ?_
  rw [mem_Ico] at hx
  exact hp hx.1 hx.2.le a.prop b.prop
#align finset.map_subtype_embedding_Ico Finset.map_subtype_embedding_Ico

theorem map_subtype_embedding_Ioc : (Ioc a b).map (Embedding.subtype p) = (Ioc a b : Finset α) := by
  rw [subtype_Ioc_eq]
  refine Finset.subtype_map_of_mem fun x hx => ?_
  rw [mem_Ioc] at hx
  exact hp hx.1.le hx.2 a.prop b.prop
#align finset.map_subtype_embedding_Ioc Finset.map_subtype_embedding_Ioc

theorem map_subtype_embedding_Ioo : (Ioo a b).map (Embedding.subtype p) = (Ioo a b : Finset α) := by
  rw [subtype_Ioo_eq]
  refine Finset.subtype_map_of_mem fun x hx => ?_
  rw [mem_Ioo] at hx
  exact hp hx.1.le hx.2.le a.prop b.prop
#align finset.map_subtype_embedding_Ioo Finset.map_subtype_embedding_Ioo

end LocallyFiniteOrder

section LocallyFiniteOrderTop

variable [LocallyFiniteOrderTop α] (a : Subtype p)

theorem subtype_Ici_eq : Ici a = (Ici (a : α)).subtype p :=
  rfl
#align finset.subtype_Ici_eq Finset.subtype_Ici_eq

theorem subtype_Ioi_eq : Ioi a = (Ioi (a : α)).subtype p :=
  rfl
#align finset.subtype_Ioi_eq Finset.subtype_Ioi_eq

variable (hp : ∀ ⦃a x⦄, a ≤ x → p a → p x)

theorem map_subtype_embedding_Ici : (Ici a).map (Embedding.subtype p) = (Ici a : Finset α) := by
  rw [subtype_Ici_eq]
  exact Finset.subtype_map_of_mem fun x hx => hp (mem_Ici.1 hx) a.prop
#align finset.map_subtype_embedding_Ici Finset.map_subtype_embedding_Ici

theorem map_subtype_embedding_Ioi : (Ioi a).map (Embedding.subtype p) = (Ioi a : Finset α) := by
  rw [subtype_Ioi_eq]
  exact Finset.subtype_map_of_mem fun x hx => hp (mem_Ioi.1 hx).le a.prop
#align finset.map_subtype_embedding_Ioi Finset.map_subtype_embedding_Ioi

end LocallyFiniteOrderTop

section LocallyFiniteOrderBot

variable [LocallyFiniteOrderBot α] (a : Subtype p)

theorem subtype_Iic_eq : Iic a = (Iic (a : α)).subtype p :=
  rfl
#align finset.subtype_Iic_eq Finset.subtype_Iic_eq

theorem subtype_Iio_eq : Iio a = (Iio (a : α)).subtype p :=
  rfl
#align finset.subtype_Iio_eq Finset.subtype_Iio_eq

variable (hp : ∀ ⦃a x⦄, x ≤ a → p a → p x)

theorem map_subtype_embedding_Iic : (Iic a).map (Embedding.subtype p) = (Iic a : Finset α) := by
  rw [subtype_Iic_eq]
  exact Finset.subtype_map_of_mem fun x hx => hp (mem_Iic.1 hx) a.prop
#align finset.map_subtype_embedding_Iic Finset.map_subtype_embedding_Iic

theorem map_subtype_embedding_Iio : (Iio a).map (Embedding.subtype p) = (Iio a : Finset α) := by
  rw [subtype_Iio_eq]
  exact Finset.subtype_map_of_mem fun x hx => hp (mem_Iio.1 hx).le a.prop
#align finset.map_subtype_embedding_Iio Finset.map_subtype_embedding_Iio

end LocallyFiniteOrderBot

end Finset

section Finite

variable {α : Type*} {s : Set α}

theorem BddBelow.finite_of_bddAbove [Preorder α] [LocallyFiniteOrder α]
    {s : Set α} (h₀ : BddBelow s) (h₁ : BddAbove s) :
    s.Finite :=
  let ⟨a, ha⟩ := h₀
  let ⟨b, hb⟩ := h₁
  (Set.finite_Icc a b).subset fun _x hx ↦ ⟨ha hx, hb hx⟩
#align bdd_below.finite_of_bdd_above BddBelow.finite_of_bddAbove

theorem Set.finite_iff_bddAbove [SemilatticeSup α] [LocallyFiniteOrder α] [OrderBot α] :
    s.Finite ↔ BddAbove s :=
  ⟨fun h ↦ ⟨h.toFinset.sup id, fun _ hx ↦ Finset.le_sup (f := id) ((Finite.mem_toFinset h).mpr hx)⟩,
    fun ⟨m, hm⟩ ↦ (Set.finite_Icc ⊥ m).subset (fun _ hx ↦ ⟨bot_le, hm hx⟩)⟩

theorem Set.finite_iff_bddBelow [SemilatticeInf α] [LocallyFiniteOrder α] [OrderTop α] :
    s.Finite ↔ BddBelow s :=
  finite_iff_bddAbove (α := αᵒᵈ)

theorem Set.finite_iff_bddBelow_bddAbove [Nonempty α] [Lattice α] [LocallyFiniteOrder α] :
    s.Finite ↔ BddBelow s ∧ BddAbove s := by
  obtain (rfl | hs) := s.eq_empty_or_nonempty
  · simp only [Set.finite_empty, bddBelow_empty, bddAbove_empty, and_self]
  exact ⟨fun h ↦ ⟨⟨h.toFinset.inf' ((Finite.toFinset_nonempty h).mpr hs) id,
    fun x hx ↦ Finset.inf'_le id ((Finite.mem_toFinset h).mpr hx)⟩,
    ⟨h.toFinset.sup' ((Finite.toFinset_nonempty h).mpr hs) id, fun x hx ↦ Finset.le_sup' id
    ((Finite.mem_toFinset h).mpr hx)⟩⟩,
    fun ⟨h₀, h₁⟩ ↦ BddBelow.finite_of_bddAbove h₀ h₁⟩

end Finite

/-! We make the instances below low priority
so when alternative constructions are available they are preferred. -/

instance (priority := low) [Preorder α] [DecidableRel ((· : α) ≤ ·)] [LocallyFiniteOrder α] :
    LocallyFiniteOrderTop { x : α // x ≤ y } where
  finsetIoi a := Finset.Ioc a ⟨y, by rfl⟩
  finsetIci a := Finset.Icc a ⟨y, by rfl⟩
  finset_mem_Ici a b := by
    simp only [Finset.mem_Icc, and_iff_left_iff_imp]
    exact fun _ => b.property
  finset_mem_Ioi a b := by
    simp only [Finset.mem_Ioc, and_iff_left_iff_imp]
    exact fun _ => b.property

instance (priority := low) [Preorder α] [DecidableRel ((· : α) < ·)] [LocallyFiniteOrder α] :
    LocallyFiniteOrderTop { x : α // x < y } where
  finsetIoi a := (Finset.Ioo ↑a y).subtype _
  finsetIci a := (Finset.Ico ↑a y).subtype _
  finset_mem_Ici a b := by
    simp only [Finset.mem_subtype, Finset.mem_Ico, Subtype.coe_le_coe, and_iff_left_iff_imp]
    exact fun _ => b.property
  finset_mem_Ioi a b := by
    simp only [Finset.mem_subtype, Finset.mem_Ioo, Subtype.coe_lt_coe, and_iff_left_iff_imp]
    exact fun _ => b.property

instance (priority := low) [Preorder α] [DecidableRel ((· : α) ≤ ·)] [LocallyFiniteOrder α] :
    LocallyFiniteOrderBot { x : α // y ≤ x } where
  finsetIio a := Finset.Ico ⟨y, by rfl⟩ a
  finsetIic a := Finset.Icc ⟨y, by rfl⟩ a
  finset_mem_Iic a b := by
    simp only [Finset.mem_Icc, and_iff_right_iff_imp]
    exact fun _ => b.property
  finset_mem_Iio a b := by
    simp only [Finset.mem_Ico, and_iff_right_iff_imp]
    exact fun _ => b.property

instance (priority := low) [Preorder α] [DecidableRel ((· : α) < ·)] [LocallyFiniteOrder α] :
    LocallyFiniteOrderBot { x : α // y < x } where
  finsetIio a := (Finset.Ioo y ↑a).subtype _
  finsetIic a := (Finset.Ioc y ↑a).subtype _
  finset_mem_Iic a b := by
    simp only [Finset.mem_subtype, Finset.mem_Ioc, Subtype.coe_le_coe, and_iff_right_iff_imp]
    exact fun _ => b.property
  finset_mem_Iio a b := by
    simp only [Finset.mem_subtype, Finset.mem_Ioo, Subtype.coe_lt_coe, and_iff_right_iff_imp]
    exact fun _ => b.property

instance [Preorder α] [LocallyFiniteOrderBot α] : Finite { x : α // x ≤ y } := by
  simpa only  [coe_Iic] using (Finset.Iic y).finite_toSet

instance [Preorder α] [LocallyFiniteOrderBot α] : Finite { x : α // x < y } := by
  simpa only [coe_Iio] using (Finset.Iio y).finite_toSet

instance [Preorder α] [LocallyFiniteOrderTop α] : Finite { x : α // y ≤ x } := by
  simpa only [coe_Ici] using (Finset.Ici y).finite_toSet

instance [Preorder α] [LocallyFiniteOrderTop α] : Finite { x : α // y < x } := by
  simpa only [coe_Ioi] using (Finset.Ioi y).finite_toSet

namespace Set
variable {α : Type*} [Preorder α]

section LocallyFiniteOrder
variable [LocallyFiniteOrder α]

@[simp] lemma toFinset_Icc (a b : α) [Fintype (Icc a b)] : (Icc a b).toFinset = Finset.Icc a b := by
  ext; simp

@[simp] lemma toFinset_Ico (a b : α) [Fintype (Ico a b)] : (Ico a b).toFinset = Finset.Ico a b := by
  ext; simp

@[simp] lemma toFinset_Ioc (a b : α) [Fintype (Ioc a b)] : (Ioc a b).toFinset = Finset.Ioc a b := by
  ext; simp

@[simp] lemma toFinset_Ioo (a b : α) [Fintype (Ioo a b)] : (Ioo a b).toFinset = Finset.Ioo a b := by
  ext; simp

end LocallyFiniteOrder

section LocallyFiniteOrderTop
variable [LocallyFiniteOrderTop α]

@[simp]
lemma toFinset_Ici (a : α) [Fintype (Ici a)] : (Ici a).toFinset = Finset.Ici a := by ext; simp

@[simp]
lemma toFinset_Ioi (a : α) [Fintype (Ioi a)] : (Ioi a).toFinset = Finset.Ioi a := by ext; simp

end LocallyFiniteOrderTop

section LocallyFiniteOrderBot
variable [LocallyFiniteOrderBot α]

@[simp]
lemma toFinset_Iic (a : α) [Fintype (Iic a)] : (Iic a).toFinset = Finset.Iic a := by ext; simp

@[simp]
lemma toFinset_Iio (a : α) [Fintype (Iio a)] : (Iio a).toFinset = Finset.Iio a := by ext; simp

end LocallyFiniteOrderBot
end Set
