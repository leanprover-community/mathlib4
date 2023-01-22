/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.locally_finite
! leanprover-community/mathlib commit 2445c98ae4b87eabebdde552593519b9b6dc350c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.Preimage
import Mathbin.Data.Set.Intervals.UnorderedInterval

/-!
# Locally finite orders

This file defines locally finite orders.

A locally finite order is an order for which all bounded intervals are finite. This allows to make
sense of `Icc`/`Ico`/`Ioc`/`Ioo` as lists, multisets, or finsets.
Further, if the order is bounded above (resp. below), then we can also make sense of the
"unbounded" intervals `Ici`/`Ioi` (resp. `Iic`/`Iio`).

Many theorems about these intervals can be found in `data.finset.locally_finite`.

## Examples

Naturally occurring locally finite orders are `ℕ`, `ℤ`, `ℕ+`, `fin n`, `α × β` the product of two
locally finite orders, `α →₀ β` the finitely supported functions to a locally finite order `β`...

## Main declarations

In a `locally_finite_order`,
* `finset.Icc`: Closed-closed interval as a finset.
* `finset.Ico`: Closed-open interval as a finset.
* `finset.Ioc`: Open-closed interval as a finset.
* `finset.Ioo`: Open-open interval as a finset.
* `finset.uIcc`: Unordered closed interval as a finset.
* `multiset.Icc`: Closed-closed interval as a multiset.
* `multiset.Ico`: Closed-open interval as a multiset.
* `multiset.Ioc`: Open-closed interval as a multiset.
* `multiset.Ioo`: Open-open interval as a multiset.

In a `locally_finite_order_top`,
* `finset.Ici`: Closed-infinite interval as a finset.
* `finset.Ioi`: Open-infinite interval as a finset.
* `multiset.Ici`: Closed-infinite interval as a multiset.
* `multiset.Ioi`: Open-infinite interval as a multiset.

In a `locally_finite_order_bot`,
* `finset.Iic`: Infinite-open interval as a finset.
* `finset.Iio`: Infinite-closed interval as a finset.
* `multiset.Iic`: Infinite-open interval as a multiset.
* `multiset.Iio`: Infinite-closed interval as a multiset.

## Instances

A `locally_finite_order` instance can be built
* for a subtype of a locally finite order. See `subtype.locally_finite_order`.
* for the product of two locally finite orders. See `prod.locally_finite_order`.
* for any fintype (but not as an instance). See `fintype.to_locally_finite_order`.
* from a definition of `finset.Icc` alone. See `locally_finite_order.of_Icc`.
* by pulling back `locally_finite_order β` through an order embedding `f : α →o β`. See
  `order_embedding.locally_finite_order`.

Instances for concrete types are proved in their respective files:
* `ℕ` is in `data.nat.interval`
* `ℤ` is in `data.int.interval`
* `ℕ+` is in `data.pnat.interval`
* `fin n` is in `data.fin.interval`
* `finset α` is in `data.finset.interval`
* `Σ i, α i` is in `data.sigma.interval`
Along, you will find lemmas about the cardinality of those finite intervals.

## TODO

Provide the `locally_finite_order` instance for `α ×ₗ β` where `locally_finite_order α` and
`fintype β`.

Provide the `locally_finite_order` instance for `α →₀ β` where `β` is locally finite. Provide the
`locally_finite_order` instance for `Π₀ i, β i` where all the `β i` are locally finite.

From `linear_order α`, `no_max_order α`, `locally_finite_order α`, we can also define an
order isomorphism `α ≃ ℕ` or `α ≃ ℤ`, depending on whether we have `order_bot α` or
`no_min_order α` and `nonempty α`. When `order_bot α`, we can match `a : α` to `(Iio a).card`.

We can provide `succ_order α` from `linear_order α` and `locally_finite_order α` using

```lean
lemma exists_min_greater [linear_order α] [locally_finite_order α] {x ub : α} (hx : x < ub) :
  ∃ lub, x < lub ∧ ∀ y, x < y → lub ≤ y :=
begin -- very non golfed
  have h : (finset.Ioc x ub).nonempty := ⟨ub, finset.mem_Ioc_iff.2 ⟨hx, le_rfl⟩⟩,
  use finset.min' (finset.Ioc x ub) h,
  split,
  { have := finset.min'_mem _ h,
    simp * at * },
  rintro y hxy,
  obtain hy | hy := le_total y ub,
  apply finset.min'_le,
  simp * at *,
  exact (finset.min'_le _ _ (finset.mem_Ioc_iff.2 ⟨hx, le_rfl⟩)).trans hy,
end
```
Note that the converse is not true. Consider `{-2^z | z : ℤ} ∪ {2^z | z : ℤ}`. Any element has a
successor (and actually a predecessor as well), so it is a `succ_order`, but it's not locally finite
as `Icc (-1) 1` is infinite.
-/


open Finset Function

/-- A locally finite order is an order where bounded intervals are finite. When you don't care too
much about definitional equality, you can use `locally_finite_order.of_Icc` or
`locally_finite_order.of_finite_Icc` to build a locally finite order from just `finset.Icc`. -/
class LocallyFiniteOrder (α : Type _) [Preorder α] where
  finsetIcc : α → α → Finset α
  finsetIco : α → α → Finset α
  finsetIoc : α → α → Finset α
  finsetIoo : α → α → Finset α
  finset_mem_Icc : ∀ a b x : α, x ∈ finset_Icc a b ↔ a ≤ x ∧ x ≤ b
  finset_mem_Ico : ∀ a b x : α, x ∈ finset_Ico a b ↔ a ≤ x ∧ x < b
  finset_mem_Ioc : ∀ a b x : α, x ∈ finset_Ioc a b ↔ a < x ∧ x ≤ b
  finset_mem_Ioo : ∀ a b x : α, x ∈ finset_Ioo a b ↔ a < x ∧ x < b
#align locally_finite_order LocallyFiniteOrder

/-- A locally finite order top is an order where all intervals bounded above are finite. This is
slightly weaker than `locally_finite_order` + `order_top` as it allows empty types. -/
class LocallyFiniteOrderTop (α : Type _) [Preorder α] where
  finsetIoi : α → Finset α
  finsetIci : α → Finset α
  finset_mem_Ici : ∀ a x : α, x ∈ finset_Ici a ↔ a ≤ x
  finset_mem_Ioi : ∀ a x : α, x ∈ finset_Ioi a ↔ a < x
#align locally_finite_order_top LocallyFiniteOrderTop

/-- A locally finite order bot is an order where all intervals bounded below are finite. This is
slightly weaker than `locally_finite_order` + `order_bot` as it allows empty types. -/
class LocallyFiniteOrderBot (α : Type _) [Preorder α] where
  finsetIio : α → Finset α
  finsetIic : α → Finset α
  finset_mem_Iic : ∀ a x : α, x ∈ finset_Iic a ↔ x ≤ a
  finset_mem_Iio : ∀ a x : α, x ∈ finset_Iio a ↔ x < a
#align locally_finite_order_bot LocallyFiniteOrderBot

/-- A constructor from a definition of `finset.Icc` alone, the other ones being derived by removing
the ends. As opposed to `locally_finite_order.of_Icc`, this one requires `decidable_rel (≤)` but
only `preorder`. -/
def LocallyFiniteOrder.ofIcc' (α : Type _) [Preorder α] [DecidableRel ((· ≤ ·) : α → α → Prop)]
    (finset_Icc : α → α → Finset α) (mem_Icc : ∀ a b x, x ∈ finset_Icc a b ↔ a ≤ x ∧ x ≤ b) :
    LocallyFiniteOrder α :=
  { finsetIcc
    finsetIco := fun a b => (finset_Icc a b).filter fun x => ¬b ≤ x
    finsetIoc := fun a b => (finset_Icc a b).filter fun x => ¬x ≤ a
    finsetIoo := fun a b => (finset_Icc a b).filter fun x => ¬x ≤ a ∧ ¬b ≤ x
    finset_mem_Icc := mem_Icc
    finset_mem_Ico := fun a b x => by rw [Finset.mem_filter, mem_Icc, and_assoc', lt_iff_le_not_le]
    finset_mem_Ioc := fun a b x => by
      rw [Finset.mem_filter, mem_Icc, and_right_comm, lt_iff_le_not_le]
    finset_mem_Ioo := fun a b x => by
      rw [Finset.mem_filter, mem_Icc, and_and_and_comm, lt_iff_le_not_le, lt_iff_le_not_le] }
#align locally_finite_order.of_Icc' LocallyFiniteOrder.ofIcc'

/-- A constructor from a definition of `finset.Icc` alone, the other ones being derived by removing
the ends. As opposed to `locally_finite_order.of_Icc`, this one requires `partial_order` but only
`decidable_eq`. -/
def LocallyFiniteOrder.ofIcc (α : Type _) [PartialOrder α] [DecidableEq α]
    (finset_Icc : α → α → Finset α) (mem_Icc : ∀ a b x, x ∈ finset_Icc a b ↔ a ≤ x ∧ x ≤ b) :
    LocallyFiniteOrder α :=
  { finsetIcc
    finsetIco := fun a b => (finset_Icc a b).filter fun x => x ≠ b
    finsetIoc := fun a b => (finset_Icc a b).filter fun x => a ≠ x
    finsetIoo := fun a b => (finset_Icc a b).filter fun x => a ≠ x ∧ x ≠ b
    finset_mem_Icc := mem_Icc
    finset_mem_Ico := fun a b x => by rw [Finset.mem_filter, mem_Icc, and_assoc', lt_iff_le_and_ne]
    finset_mem_Ioc := fun a b x => by
      rw [Finset.mem_filter, mem_Icc, and_right_comm, lt_iff_le_and_ne]
    finset_mem_Ioo := fun a b x => by
      rw [Finset.mem_filter, mem_Icc, and_and_and_comm, lt_iff_le_and_ne, lt_iff_le_and_ne] }
#align locally_finite_order.of_Icc LocallyFiniteOrder.ofIcc

/-- A constructor from a definition of `finset.Iic` alone, the other ones being derived by removing
the ends. As opposed to `locally_finite_order_top.of_Ici`, this one requires `decidable_rel (≤)` but
only `preorder`. -/
def LocallyFiniteOrderTop.ofIci' (α : Type _) [Preorder α] [DecidableRel ((· ≤ ·) : α → α → Prop)]
    (finset_Ici : α → Finset α) (mem_Ici : ∀ a x, x ∈ finset_Ici a ↔ a ≤ x) :
    LocallyFiniteOrderTop α :=
  { finsetIci
    finsetIoi := fun a => (finset_Ici a).filter fun x => ¬x ≤ a
    finset_mem_Ici := mem_Ici
    finset_mem_Ioi := fun a x => by rw [mem_filter, mem_Ici, lt_iff_le_not_le] }
#align locally_finite_order_top.of_Ici' LocallyFiniteOrderTop.ofIci'

/-- A constructor from a definition of `finset.Iic` alone, the other ones being derived by removing
the ends. As opposed to `locally_finite_order_top.of_Ici'`, this one requires `partial_order` but
only `decidable_eq`. -/
def LocallyFiniteOrderTop.ofIci (α : Type _) [PartialOrder α] [DecidableEq α]
    (finset_Ici : α → Finset α) (mem_Ici : ∀ a x, x ∈ finset_Ici a ↔ a ≤ x) :
    LocallyFiniteOrderTop α :=
  { finsetIci
    finsetIoi := fun a => (finset_Ici a).filter fun x => a ≠ x
    finset_mem_Ici := mem_Ici
    finset_mem_Ioi := fun a x => by rw [mem_filter, mem_Ici, lt_iff_le_and_ne] }
#align locally_finite_order_top.of_Ici LocallyFiniteOrderTop.ofIci

/-- A constructor from a definition of `finset.Iic` alone, the other ones being derived by removing
the ends. As opposed to `locally_finite_order.of_Icc`, this one requires `decidable_rel (≤)` but
only `preorder`. -/
def LocallyFiniteOrderBot.ofIic' (α : Type _) [Preorder α] [DecidableRel ((· ≤ ·) : α → α → Prop)]
    (finset_Iic : α → Finset α) (mem_Iic : ∀ a x, x ∈ finset_Iic a ↔ x ≤ a) :
    LocallyFiniteOrderBot α :=
  { finsetIic
    finsetIio := fun a => (finset_Iic a).filter fun x => ¬a ≤ x
    finset_mem_Iic := mem_Iic
    finset_mem_Iio := fun a x => by rw [mem_filter, mem_Iic, lt_iff_le_not_le] }
#align locally_finite_order_bot.of_Iic' LocallyFiniteOrderBot.ofIic'

/-- A constructor from a definition of `finset.Iic` alone, the other ones being derived by removing
the ends. As opposed to `locally_finite_order_top.of_Ici'`, this one requires `partial_order` but
only `decidable_eq`. -/
def LocallyFiniteOrderTop.ofIic (α : Type _) [PartialOrder α] [DecidableEq α]
    (finset_Iic : α → Finset α) (mem_Iic : ∀ a x, x ∈ finset_Iic a ↔ x ≤ a) :
    LocallyFiniteOrderBot α :=
  { finsetIic
    finsetIio := fun a => (finset_Iic a).filter fun x => x ≠ a
    finset_mem_Iic := mem_Iic
    finset_mem_Iio := fun a x => by rw [mem_filter, mem_Iic, lt_iff_le_and_ne] }
#align locally_finite_order_top.of_Iic LocallyFiniteOrderTop.ofIic

variable {α β : Type _}

-- See note [reducible non-instances]
/-- An empty type is locally finite.

This is not an instance as it would not be defeq to more specific instances. -/
@[reducible]
protected def IsEmpty.toLocallyFiniteOrder [Preorder α] [IsEmpty α] : LocallyFiniteOrder α
    where
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
@[reducible]
protected def IsEmpty.toLocallyFiniteOrderTop [Preorder α] [IsEmpty α] : LocallyFiniteOrderTop α
    where
  finsetIci := isEmptyElim
  finsetIoi := isEmptyElim
  finset_mem_Ici := isEmptyElim
  finset_mem_Ioi := isEmptyElim
#align is_empty.to_locally_finite_order_top IsEmpty.toLocallyFiniteOrderTop

-- See note [reducible non-instances]
/-- An empty type is locally finite.

This is not an instance as it would not be defeq to more specific instances. -/
@[reducible]
protected def IsEmpty.toLocallyFiniteOrderBot [Preorder α] [IsEmpty α] : LocallyFiniteOrderBot α
    where
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

/-- The finset of elements `x` such that `a ≤ x` and `x ≤ b`. Basically `set.Icc a b` as a finset.
-/
def icc (a b : α) : Finset α :=
  LocallyFiniteOrder.finsetIcc a b
#align finset.Icc Finset.icc

/-- The finset of elements `x` such that `a ≤ x` and `x < b`. Basically `set.Ico a b` as a finset.
-/
def ico (a b : α) : Finset α :=
  LocallyFiniteOrder.finsetIco a b
#align finset.Ico Finset.ico

/-- The finset of elements `x` such that `a < x` and `x ≤ b`. Basically `set.Ioc a b` as a finset.
-/
def ioc (a b : α) : Finset α :=
  LocallyFiniteOrder.finsetIoc a b
#align finset.Ioc Finset.ioc

/-- The finset of elements `x` such that `a < x` and `x < b`. Basically `set.Ioo a b` as a finset.
-/
def ioo (a b : α) : Finset α :=
  LocallyFiniteOrder.finsetIoo a b
#align finset.Ioo Finset.ioo

@[simp]
theorem mem_icc : x ∈ icc a b ↔ a ≤ x ∧ x ≤ b :=
  LocallyFiniteOrder.finset_mem_Icc a b x
#align finset.mem_Icc Finset.mem_icc

@[simp]
theorem mem_ico : x ∈ ico a b ↔ a ≤ x ∧ x < b :=
  LocallyFiniteOrder.finset_mem_Ico a b x
#align finset.mem_Ico Finset.mem_ico

@[simp]
theorem mem_ioc : x ∈ ioc a b ↔ a < x ∧ x ≤ b :=
  LocallyFiniteOrder.finset_mem_Ioc a b x
#align finset.mem_Ioc Finset.mem_ioc

@[simp]
theorem mem_ioo : x ∈ ioo a b ↔ a < x ∧ x < b :=
  LocallyFiniteOrder.finset_mem_Ioo a b x
#align finset.mem_Ioo Finset.mem_ioo

@[simp, norm_cast]
theorem coe_icc (a b : α) : (icc a b : Set α) = Set.Icc a b :=
  Set.ext fun _ => mem_icc
#align finset.coe_Icc Finset.coe_icc

@[simp, norm_cast]
theorem coe_ico (a b : α) : (ico a b : Set α) = Set.Ico a b :=
  Set.ext fun _ => mem_ico
#align finset.coe_Ico Finset.coe_ico

@[simp, norm_cast]
theorem coe_ioc (a b : α) : (ioc a b : Set α) = Set.Ioc a b :=
  Set.ext fun _ => mem_ioc
#align finset.coe_Ioc Finset.coe_ioc

@[simp, norm_cast]
theorem coe_ioo (a b : α) : (ioo a b : Set α) = Set.Ioo a b :=
  Set.ext fun _ => mem_ioo
#align finset.coe_Ioo Finset.coe_ioo

end LocallyFiniteOrder

section LocallyFiniteOrderTop

variable [LocallyFiniteOrderTop α] {a x : α}

/-- The finset of elements `x` such that `a ≤ x`. Basically `set.Ici a` as a finset. -/
def ici (a : α) : Finset α :=
  LocallyFiniteOrderTop.finsetIci a
#align finset.Ici Finset.ici

/-- The finset of elements `x` such that `a < x`. Basically `set.Ioi a` as a finset. -/
def ioi (a : α) : Finset α :=
  LocallyFiniteOrderTop.finsetIoi a
#align finset.Ioi Finset.ioi

@[simp]
theorem mem_ici : x ∈ ici a ↔ a ≤ x :=
  LocallyFiniteOrderTop.finset_mem_Ici _ _
#align finset.mem_Ici Finset.mem_ici

@[simp]
theorem mem_ioi : x ∈ ioi a ↔ a < x :=
  LocallyFiniteOrderTop.finset_mem_Ioi _ _
#align finset.mem_Ioi Finset.mem_ioi

@[simp, norm_cast]
theorem coe_ici (a : α) : (ici a : Set α) = Set.Ici a :=
  Set.ext fun _ => mem_ici
#align finset.coe_Ici Finset.coe_ici

@[simp, norm_cast]
theorem coe_ioi (a : α) : (ioi a : Set α) = Set.Ioi a :=
  Set.ext fun _ => mem_ioi
#align finset.coe_Ioi Finset.coe_ioi

end LocallyFiniteOrderTop

section LocallyFiniteOrderBot

variable [LocallyFiniteOrderBot α] {a x : α}

/-- The finset of elements `x` such that `a ≤ x`. Basically `set.Iic a` as a finset. -/
def iic (a : α) : Finset α :=
  LocallyFiniteOrderBot.finsetIic a
#align finset.Iic Finset.iic

/-- The finset of elements `x` such that `a < x`. Basically `set.Iio a` as a finset. -/
def iio (a : α) : Finset α :=
  LocallyFiniteOrderBot.finsetIio a
#align finset.Iio Finset.iio

@[simp]
theorem mem_iic : x ∈ iic a ↔ x ≤ a :=
  LocallyFiniteOrderBot.finset_mem_Iic _ _
#align finset.mem_Iic Finset.mem_iic

@[simp]
theorem mem_iio : x ∈ iio a ↔ x < a :=
  LocallyFiniteOrderBot.finset_mem_Iio _ _
#align finset.mem_Iio Finset.mem_iio

@[simp, norm_cast]
theorem coe_iic (a : α) : (iic a : Set α) = Set.Iic a :=
  Set.ext fun _ => mem_iic
#align finset.coe_Iic Finset.coe_iic

@[simp, norm_cast]
theorem coe_iio (a : α) : (iio a : Set α) = Set.Iio a :=
  Set.ext fun _ => mem_iio
#align finset.coe_Iio Finset.coe_iio

end LocallyFiniteOrderBot

section OrderTop

variable [LocallyFiniteOrder α] [OrderTop α] {a x : α}

-- See note [lower priority instance]
instance (priority := 100) LocallyFiniteOrder.toLocallyFiniteOrderTop : LocallyFiniteOrderTop α
    where
  finsetIci b := icc b ⊤
  finsetIoi b := ioc b ⊤
  finset_mem_Ici a x := by rw [mem_Icc, and_iff_left le_top]
  finset_mem_Ioi a x := by rw [mem_Ioc, and_iff_left le_top]
#align locally_finite_order.to_locally_finite_order_top LocallyFiniteOrder.toLocallyFiniteOrderTop

theorem ici_eq_icc (a : α) : ici a = icc a ⊤ :=
  rfl
#align finset.Ici_eq_Icc Finset.ici_eq_icc

theorem ioi_eq_ioc (a : α) : ioi a = ioc a ⊤ :=
  rfl
#align finset.Ioi_eq_Ioc Finset.ioi_eq_ioc

end OrderTop

section OrderBot

variable [OrderBot α] [LocallyFiniteOrder α] {b x : α}

-- See note [lower priority instance]
instance (priority := 100) LocallyFiniteOrder.toLocallyFiniteOrderBot : LocallyFiniteOrderBot α
    where
  finsetIic := icc ⊥
  finsetIio := ico ⊥
  finset_mem_Iic a x := by rw [mem_Icc, and_iff_right bot_le]
  finset_mem_Iio a x := by rw [mem_Ico, and_iff_right bot_le]
#align finset.locally_finite_order.to_locally_finite_order_bot Finset.LocallyFiniteOrder.toLocallyFiniteOrderBot

theorem iic_eq_icc : Iic = icc (⊥ : α) :=
  rfl
#align finset.Iic_eq_Icc Finset.iic_eq_icc

theorem iio_eq_ico : Iio = ico (⊥ : α) :=
  rfl
#align finset.Iio_eq_Ico Finset.iio_eq_ico

end OrderBot

end Preorder

section Lattice

variable [Lattice α] [LocallyFiniteOrder α] {a b x : α}

/-- `finset.uIcc a b` is the set of elements lying between `a` and `b`, with `a` and `b` included.
Note that we define it more generally in a lattice as `finset.Icc (a ⊓ b) (a ⊔ b)`. In a
product type, `finset.uIcc` corresponds to the bounding box of the two elements. -/
def uIcc (a b : α) : Finset α :=
  icc (a ⊓ b) (a ⊔ b)
#align finset.uIcc Finset.uIcc

-- mathport name: finset.uIcc
scoped[FinsetInterval] notation "[" a ", " b "]" => Finset.uIcc a b

@[simp]
theorem mem_uIcc : x ∈ uIcc a b ↔ a ⊓ b ≤ x ∧ x ≤ a ⊔ b :=
  mem_Icc
#align finset.mem_uIcc Finset.mem_uIcc

@[simp, norm_cast]
theorem coe_uIcc (a b : α) : ([a, b] : Set α) = Set.uIcc a b :=
  coe_icc _ _
#align finset.coe_uIcc Finset.coe_uIcc

end Lattice

end Finset

/-! ### Intervals as multisets -/


namespace Multiset

variable [Preorder α]

section LocallyFiniteOrder

variable [LocallyFiniteOrder α]

/-- The multiset of elements `x` such that `a ≤ x` and `x ≤ b`. Basically `set.Icc a b` as a
multiset. -/
def icc (a b : α) : Multiset α :=
  (Finset.icc a b).val
#align multiset.Icc Multiset.icc

/-- The multiset of elements `x` such that `a ≤ x` and `x < b`. Basically `set.Ico a b` as a
multiset. -/
def ico (a b : α) : Multiset α :=
  (Finset.ico a b).val
#align multiset.Ico Multiset.ico

/-- The multiset of elements `x` such that `a < x` and `x ≤ b`. Basically `set.Ioc a b` as a
multiset. -/
def ioc (a b : α) : Multiset α :=
  (Finset.ioc a b).val
#align multiset.Ioc Multiset.ioc

/-- The multiset of elements `x` such that `a < x` and `x < b`. Basically `set.Ioo a b` as a
multiset. -/
def ioo (a b : α) : Multiset α :=
  (Finset.ioo a b).val
#align multiset.Ioo Multiset.ioo

@[simp]
theorem mem_icc {a b x : α} : x ∈ icc a b ↔ a ≤ x ∧ x ≤ b := by
  rw [Icc, ← Finset.mem_def, Finset.mem_icc]
#align multiset.mem_Icc Multiset.mem_icc

@[simp]
theorem mem_ico {a b x : α} : x ∈ ico a b ↔ a ≤ x ∧ x < b := by
  rw [Ico, ← Finset.mem_def, Finset.mem_ico]
#align multiset.mem_Ico Multiset.mem_ico

@[simp]
theorem mem_ioc {a b x : α} : x ∈ ioc a b ↔ a < x ∧ x ≤ b := by
  rw [Ioc, ← Finset.mem_def, Finset.mem_ioc]
#align multiset.mem_Ioc Multiset.mem_ioc

@[simp]
theorem mem_ioo {a b x : α} : x ∈ ioo a b ↔ a < x ∧ x < b := by
  rw [Ioo, ← Finset.mem_def, Finset.mem_ioo]
#align multiset.mem_Ioo Multiset.mem_ioo

end LocallyFiniteOrder

section LocallyFiniteOrderTop

variable [LocallyFiniteOrderTop α]

/-- The multiset of elements `x` such that `a ≤ x`. Basically `set.Ici a` as a multiset. -/
def ici (a : α) : Multiset α :=
  (Finset.ici a).val
#align multiset.Ici Multiset.ici

/-- The multiset of elements `x` such that `a < x`. Basically `set.Ioi a` as a multiset. -/
def ioi (a : α) : Multiset α :=
  (Finset.ioi a).val
#align multiset.Ioi Multiset.ioi

@[simp]
theorem mem_ici {a x : α} : x ∈ ici a ↔ a ≤ x := by rw [Ici, ← Finset.mem_def, Finset.mem_ici]
#align multiset.mem_Ici Multiset.mem_ici

@[simp]
theorem mem_ioi {a x : α} : x ∈ ioi a ↔ a < x := by rw [Ioi, ← Finset.mem_def, Finset.mem_ioi]
#align multiset.mem_Ioi Multiset.mem_ioi

end LocallyFiniteOrderTop

section LocallyFiniteOrderBot

variable [LocallyFiniteOrderBot α]

/-- The multiset of elements `x` such that `x ≤ b`. Basically `set.Iic b` as a multiset. -/
def iic (b : α) : Multiset α :=
  (Finset.iic b).val
#align multiset.Iic Multiset.iic

/-- The multiset of elements `x` such that `x < b`. Basically `set.Iio b` as a multiset. -/
def iio (b : α) : Multiset α :=
  (Finset.iio b).val
#align multiset.Iio Multiset.iio

@[simp]
theorem mem_iic {b x : α} : x ∈ iic b ↔ x ≤ b := by rw [Iic, ← Finset.mem_def, Finset.mem_iic]
#align multiset.mem_Iic Multiset.mem_iic

@[simp]
theorem mem_iio {b x : α} : x ∈ iio b ↔ x < b := by rw [Iio, ← Finset.mem_def, Finset.mem_iio]
#align multiset.mem_Iio Multiset.mem_iio

end LocallyFiniteOrderBot

end Multiset

/-! ### Finiteness of `set` intervals -/


namespace Set

section Preorder

variable [Preorder α] [LocallyFiniteOrder α] (a b : α)

instance fintypeIcc : Fintype (Icc a b) :=
  Fintype.ofFinset (Finset.icc a b) fun x => by rw [Finset.mem_icc, mem_Icc]
#align set.fintype_Icc Set.fintypeIcc

instance fintypeIco : Fintype (Ico a b) :=
  Fintype.ofFinset (Finset.ico a b) fun x => by rw [Finset.mem_ico, mem_Ico]
#align set.fintype_Ico Set.fintypeIco

instance fintypeIoc : Fintype (Ioc a b) :=
  Fintype.ofFinset (Finset.ioc a b) fun x => by rw [Finset.mem_ioc, mem_Ioc]
#align set.fintype_Ioc Set.fintypeIoc

instance fintypeIoo : Fintype (Ioo a b) :=
  Fintype.ofFinset (Finset.ioo a b) fun x => by rw [Finset.mem_ioo, mem_Ioo]
#align set.fintype_Ioo Set.fintypeIoo

theorem finite_icc : (Icc a b).Finite :=
  (Icc a b).toFinite
#align set.finite_Icc Set.finite_icc

theorem finite_ico : (Ico a b).Finite :=
  (Ico a b).toFinite
#align set.finite_Ico Set.finite_ico

theorem finite_ioc : (Ioc a b).Finite :=
  (Ioc a b).toFinite
#align set.finite_Ioc Set.finite_ioc

theorem finite_ioo : (Ioo a b).Finite :=
  (Ioo a b).toFinite
#align set.finite_Ioo Set.finite_ioo

end Preorder

section OrderTop

variable [Preorder α] [LocallyFiniteOrderTop α] (a : α)

instance fintypeIci : Fintype (Ici a) :=
  Fintype.ofFinset (Finset.ici a) fun x => by rw [Finset.mem_ici, mem_Ici]
#align set.fintype_Ici Set.fintypeIci

instance fintypeIoi : Fintype (Ioi a) :=
  Fintype.ofFinset (Finset.ioi a) fun x => by rw [Finset.mem_ioi, mem_Ioi]
#align set.fintype_Ioi Set.fintypeIoi

theorem finite_ici : (Ici a).Finite :=
  (Ici a).toFinite
#align set.finite_Ici Set.finite_ici

theorem finite_ioi : (Ioi a).Finite :=
  (Ioi a).toFinite
#align set.finite_Ioi Set.finite_ioi

end OrderTop

section OrderBot

variable [Preorder α] [LocallyFiniteOrderBot α] (b : α)

instance fintypeIic : Fintype (Iic b) :=
  Fintype.ofFinset (Finset.iic b) fun x => by rw [Finset.mem_iic, mem_Iic]
#align set.fintype_Iic Set.fintypeIic

instance fintypeIio : Fintype (Iio b) :=
  Fintype.ofFinset (Finset.iio b) fun x => by rw [Finset.mem_iio, mem_Iio]
#align set.fintype_Iio Set.fintypeIio

theorem finite_iic : (Iic b).Finite :=
  (Iic b).toFinite
#align set.finite_Iic Set.finite_iic

theorem finite_iio : (Iio b).Finite :=
  (Iio b).toFinite
#align set.finite_Iio Set.finite_iio

end OrderBot

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
`fin.locally_finite_order`.
-/
@[reducible]
def Fintype.toLocallyFiniteOrder [Fintype α] [@DecidableRel α (· < ·)] [@DecidableRel α (· ≤ ·)] :
    LocallyFiniteOrder α where
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
    cases h₀
    cases h₁
    have hIcc : h₀_finset_Icc = h₁_finset_Icc :=
      by
      ext (a b x)
      rw [h₀_finset_mem_Icc, h₁_finset_mem_Icc]
    have hIco : h₀_finset_Ico = h₁_finset_Ico :=
      by
      ext (a b x)
      rw [h₀_finset_mem_Ico, h₁_finset_mem_Ico]
    have hIoc : h₀_finset_Ioc = h₁_finset_Ioc :=
      by
      ext (a b x)
      rw [h₀_finset_mem_Ioc, h₁_finset_mem_Ioc]
    have hIoo : h₀_finset_Ioo = h₁_finset_Ioo :=
      by
      ext (a b x)
      rw [h₀_finset_mem_Ioo, h₁_finset_mem_Ioo]
    simp_rw [hIcc, hIco, hIoc, hIoo]

instance : Subsingleton (LocallyFiniteOrderTop α) :=
  Subsingleton.intro fun h₀ h₁ => by
    cases h₀
    cases h₁
    have hIci : h₀_finset_Ici = h₁_finset_Ici :=
      by
      ext (a b x)
      rw [h₀_finset_mem_Ici, h₁_finset_mem_Ici]
    have hIoi : h₀_finset_Ioi = h₁_finset_Ioi :=
      by
      ext (a b x)
      rw [h₀_finset_mem_Ioi, h₁_finset_mem_Ioi]
    simp_rw [hIci, hIoi]

instance : Subsingleton (LocallyFiniteOrderBot α) :=
  Subsingleton.intro fun h₀ h₁ => by
    cases h₀
    cases h₁
    have hIic : h₀_finset_Iic = h₁_finset_Iic :=
      by
      ext (a b x)
      rw [h₀_finset_mem_Iic, h₁_finset_mem_Iic]
    have hIio : h₀_finset_Iio = h₁_finset_Iio :=
      by
      ext (a b x)
      rw [h₀_finset_mem_Iio, h₁_finset_mem_Iio]
    simp_rw [hIic, hIio]

-- Should this be called `locally_finite_order.lift`?
/-- Given an order embedding `α ↪o β`, pulls back the `locally_finite_order` on `β` to `α`. -/
protected noncomputable def OrderEmbedding.locallyFiniteOrder [LocallyFiniteOrder β] (f : α ↪o β) :
    LocallyFiniteOrder α
    where
  finsetIcc a b := (icc (f a) (f b)).Preimage f (f.toEmbedding.Injective.InjOn _)
  finsetIco a b := (ico (f a) (f b)).Preimage f (f.toEmbedding.Injective.InjOn _)
  finsetIoc a b := (ioc (f a) (f b)).Preimage f (f.toEmbedding.Injective.InjOn _)
  finsetIoo a b := (ioo (f a) (f b)).Preimage f (f.toEmbedding.Injective.InjOn _)
  finset_mem_Icc a b x := by rw [mem_preimage, mem_Icc, f.le_iff_le, f.le_iff_le]
  finset_mem_Ico a b x := by rw [mem_preimage, mem_Ico, f.le_iff_le, f.lt_iff_lt]
  finset_mem_Ioc a b x := by rw [mem_preimage, mem_Ioc, f.lt_iff_lt, f.le_iff_le]
  finset_mem_Ioo a b x := by rw [mem_preimage, mem_Ioo, f.lt_iff_lt, f.lt_iff_lt]
#align order_embedding.locally_finite_order OrderEmbedding.locallyFiniteOrder

open OrderDual

section LocallyFiniteOrder

variable [LocallyFiniteOrder α] (a b : α)

/-- Note we define `Icc (to_dual a) (to_dual b)` as `Icc α _ _ b a` (which has type `finset α` not
`finset αᵒᵈ`!) instead of `(Icc b a).map to_dual.to_embedding` as this means the
following is defeq:
```
lemma this : (Icc (to_dual (to_dual a)) (to_dual (to_dual b)) : _) = (Icc a b : _) := rfl
```
-/
instance : LocallyFiniteOrder αᵒᵈ
    where
  finsetIcc a b := @icc α _ _ (ofDual b) (ofDual a)
  finsetIco a b := @ioc α _ _ (ofDual b) (ofDual a)
  finsetIoc a b := @ico α _ _ (ofDual b) (ofDual a)
  finsetIoo a b := @ioo α _ _ (ofDual b) (ofDual a)
  finset_mem_Icc a b x := mem_icc.trans (and_comm' _ _)
  finset_mem_Ico a b x := mem_ioc.trans (and_comm' _ _)
  finset_mem_Ioc a b x := mem_ico.trans (and_comm' _ _)
  finset_mem_Ioo a b x := mem_ioo.trans (and_comm' _ _)

theorem icc_toDual : icc (toDual a) (toDual b) = (icc b a).map toDual.toEmbedding :=
  by
  refine' Eq.trans _ map_refl.symm
  ext c
  rw [mem_Icc, mem_Icc]
  exact and_comm' _ _
#align Icc_to_dual icc_toDual

theorem ico_toDual : ico (toDual a) (toDual b) = (ioc b a).map toDual.toEmbedding :=
  by
  refine' Eq.trans _ map_refl.symm
  ext c
  rw [mem_Ico, mem_Ioc]
  exact and_comm' _ _
#align Ico_to_dual ico_toDual

theorem ioc_toDual : ioc (toDual a) (toDual b) = (ico b a).map toDual.toEmbedding :=
  by
  refine' Eq.trans _ map_refl.symm
  ext c
  rw [mem_Ioc, mem_Ico]
  exact and_comm' _ _
#align Ioc_to_dual ioc_toDual

theorem ioo_toDual : ioo (toDual a) (toDual b) = (ioo b a).map toDual.toEmbedding :=
  by
  refine' Eq.trans _ map_refl.symm
  ext c
  rw [mem_Ioo, mem_Ioo]
  exact and_comm' _ _
#align Ioo_to_dual ioo_toDual

theorem icc_ofDual (a b : αᵒᵈ) : icc (ofDual a) (ofDual b) = (icc b a).map ofDual.toEmbedding :=
  by
  refine' Eq.trans _ map_refl.symm
  ext c
  rw [mem_Icc, mem_Icc]
  exact and_comm' _ _
#align Icc_of_dual icc_ofDual

theorem ico_ofDual (a b : αᵒᵈ) : ico (ofDual a) (ofDual b) = (ioc b a).map ofDual.toEmbedding :=
  by
  refine' Eq.trans _ map_refl.symm
  ext c
  rw [mem_Ico, mem_Ioc]
  exact and_comm' _ _
#align Ico_of_dual ico_ofDual

theorem ioc_ofDual (a b : αᵒᵈ) : ioc (ofDual a) (ofDual b) = (ico b a).map ofDual.toEmbedding :=
  by
  refine' Eq.trans _ map_refl.symm
  ext c
  rw [mem_Ioc, mem_Ico]
  exact and_comm' _ _
#align Ioc_of_dual ioc_ofDual

theorem ioo_ofDual (a b : αᵒᵈ) : ioo (ofDual a) (ofDual b) = (ioo b a).map ofDual.toEmbedding :=
  by
  refine' Eq.trans _ map_refl.symm
  ext c
  rw [mem_Ioo, mem_Ioo]
  exact and_comm' _ _
#align Ioo_of_dual ioo_ofDual

end LocallyFiniteOrder

section LocallyFiniteOrderTop

variable [LocallyFiniteOrderTop α]

/-- Note we define `Iic (to_dual a)` as `Ici a` (which has type `finset α` not `finset αᵒᵈ`!)
instead of `(Ici a).map to_dual.to_embedding` as this means the following is defeq:
```
lemma this : (Iic (to_dual (to_dual a)) : _) = (Iic a : _) := rfl
```
-/
instance : LocallyFiniteOrderBot αᵒᵈ
    where
  finsetIic a := @ici α _ _ (ofDual a)
  finsetIio a := @ioi α _ _ (ofDual a)
  finset_mem_Iic a x := mem_ici
  finset_mem_Iio a x := mem_ioi

theorem iic_toDual (a : α) : iic (toDual a) = (ici a).map toDual.toEmbedding :=
  map_refl.symm
#align Iic_to_dual iic_toDual

theorem iio_toDual (a : α) : iio (toDual a) = (ioi a).map toDual.toEmbedding :=
  map_refl.symm
#align Iio_to_dual iio_toDual

theorem ici_ofDual (a : αᵒᵈ) : ici (ofDual a) = (iic a).map ofDual.toEmbedding :=
  map_refl.symm
#align Ici_of_dual ici_ofDual

theorem ioi_ofDual (a : αᵒᵈ) : ioi (ofDual a) = (iio a).map ofDual.toEmbedding :=
  map_refl.symm
#align Ioi_of_dual ioi_ofDual

end LocallyFiniteOrderTop

section LocallyFiniteOrderTop

variable [LocallyFiniteOrderBot α]

/-- Note we define `Ici (to_dual a)` as `Iic a` (which has type `finset α` not `finset αᵒᵈ`!)
instead of `(Iic a).map to_dual.to_embedding` as this means the following is defeq:
```
lemma this : (Ici (to_dual (to_dual a)) : _) = (Ici a : _) := rfl
```
-/
instance : LocallyFiniteOrderTop αᵒᵈ
    where
  finsetIci a := @iic α _ _ (ofDual a)
  finsetIoi a := @iio α _ _ (ofDual a)
  finset_mem_Ici a x := mem_iic
  finset_mem_Ioi a x := mem_iio

theorem ici_toDual (a : α) : ici (toDual a) = (iic a).map toDual.toEmbedding :=
  map_refl.symm
#align Ici_to_dual ici_toDual

theorem ioi_toDual (a : α) : ioi (toDual a) = (iio a).map toDual.toEmbedding :=
  map_refl.symm
#align Ioi_to_dual ioi_toDual

theorem iic_ofDual (a : αᵒᵈ) : iic (ofDual a) = (ici a).map ofDual.toEmbedding :=
  map_refl.symm
#align Iic_of_dual iic_ofDual

theorem iio_ofDual (a : αᵒᵈ) : iio (ofDual a) = (ioi a).map ofDual.toEmbedding :=
  map_refl.symm
#align Iio_of_dual iio_ofDual

end LocallyFiniteOrderTop

namespace Prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
instance [LocallyFiniteOrder α] [LocallyFiniteOrder β]
    [DecidableRel ((· ≤ ·) : α × β → α × β → Prop)] : LocallyFiniteOrder (α × β) :=
  LocallyFiniteOrder.ofIcc' (α × β) (fun a b => icc a.fst b.fst ×ˢ icc a.snd b.snd) fun a b x =>
    by
    rw [mem_product, mem_Icc, mem_Icc, and_and_and_comm]
    rfl

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
instance [LocallyFiniteOrderTop α] [LocallyFiniteOrderTop β]
    [DecidableRel ((· ≤ ·) : α × β → α × β → Prop)] : LocallyFiniteOrderTop (α × β) :=
  LocallyFiniteOrderTop.ofIci' (α × β) (fun a => ici a.fst ×ˢ ici a.snd) fun a x =>
    by
    rw [mem_product, mem_Ici, mem_Ici]
    rfl

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
instance [LocallyFiniteOrderBot α] [LocallyFiniteOrderBot β]
    [DecidableRel ((· ≤ ·) : α × β → α × β → Prop)] : LocallyFiniteOrderBot (α × β) :=
  LocallyFiniteOrderBot.ofIic' (α × β) (fun a => iic a.fst ×ˢ iic a.snd) fun a x =>
    by
    rw [mem_product, mem_Iic, mem_Iic]
    rfl

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem icc_eq [LocallyFiniteOrder α] [LocallyFiniteOrder β]
    [DecidableRel ((· ≤ ·) : α × β → α × β → Prop)] (p q : α × β) :
    Finset.icc p q = Finset.icc p.1 q.1 ×ˢ Finset.icc p.2 q.2 :=
  rfl
#align prod.Icc_eq Prod.icc_eq

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem icc_mk_mk [LocallyFiniteOrder α] [LocallyFiniteOrder β]
    [DecidableRel ((· ≤ ·) : α × β → α × β → Prop)] (a₁ a₂ : α) (b₁ b₂ : β) :
    Finset.icc (a₁, b₁) (a₂, b₂) = Finset.icc a₁ a₂ ×ˢ Finset.icc b₁ b₂ :=
  rfl
#align prod.Icc_mk_mk Prod.icc_mk_mk

theorem card_icc [LocallyFiniteOrder α] [LocallyFiniteOrder β]
    [DecidableRel ((· ≤ ·) : α × β → α × β → Prop)] (p q : α × β) :
    (Finset.icc p q).card = (Finset.icc p.1 q.1).card * (Finset.icc p.2 q.2).card :=
  Finset.card_product _ _
#align prod.card_Icc Prod.card_icc

end Prod

end Preorder

namespace Prod

variable [Lattice α] [Lattice β]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem uIcc_eq [LocallyFiniteOrder α] [LocallyFiniteOrder β]
    [DecidableRel ((· ≤ ·) : α × β → α × β → Prop)] (p q : α × β) :
    Finset.uIcc p q = Finset.uIcc p.1 q.1 ×ˢ Finset.uIcc p.2 q.2 :=
  rfl
#align prod.uIcc_eq Prod.uIcc_eq

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem uIcc_mk_mk [LocallyFiniteOrder α] [LocallyFiniteOrder β]
    [DecidableRel ((· ≤ ·) : α × β → α × β → Prop)] (a₁ a₂ : α) (b₁ b₂ : β) :
    Finset.uIcc (a₁, b₁) (a₂, b₂) = Finset.uIcc a₁ a₂ ×ˢ Finset.uIcc b₁ b₂ :=
  rfl
#align prod.uIcc_mk_mk Prod.uIcc_mk_mk

theorem card_uIcc [LocallyFiniteOrder α] [LocallyFiniteOrder β]
    [DecidableRel ((· ≤ ·) : α × β → α × β → Prop)] (p q : α × β) :
    (Finset.uIcc p q).card = (Finset.uIcc p.1 q.1).card * (Finset.uIcc p.2 q.2).card :=
  Prod.card_icc _ _
#align prod.card_uIcc Prod.card_uIcc

end Prod

/-!
#### `with_top`, `with_bot`

Adding a `⊤` to a locally finite `order_top` keeps it locally finite.
Adding a `⊥` to a locally finite `order_bot` keeps it locally finite.
-/


namespace WithTop

variable (α) [PartialOrder α] [OrderTop α] [LocallyFiniteOrder α]

attribute [local match_pattern] coe

attribute [local simp] Option.mem_iff

instance : LocallyFiniteOrder (WithTop α)
    where
  finsetIcc a b :=
    match a, b with
    | ⊤, ⊤ => {⊤}
    | ⊤, (b : α) => ∅
    | (a : α), ⊤ => insertNone (ici a)
    | (a : α), (b : α) => (icc a b).map Embedding.some
  finsetIco a b :=
    match a, b with
    | ⊤, _ => ∅
    | (a : α), ⊤ => (ici a).map Embedding.some
    | (a : α), (b : α) => (ico a b).map Embedding.some
  finsetIoc a b :=
    match a, b with
    | ⊤, _ => ∅
    | (a : α), ⊤ => insertNone (ioi a)
    | (a : α), (b : α) => (ioc a b).map Embedding.some
  finsetIoo a b :=
    match a, b with
    | ⊤, _ => ∅
    | (a : α), ⊤ => (ioi a).map Embedding.some
    | (a : α), (b : α) => (ioo a b).map Embedding.some
  finset_mem_Icc a b x :=
    match a, b, x with
    | ⊤, ⊤, x => mem_singleton.trans (le_antisymm_iff.trans <| and_comm' _ _)
    | ⊤, (b : α), x =>
      iff_of_false (not_mem_empty _) fun h => (h.1.trans h.2).not_lt <| coe_lt_top _
    | (a : α), ⊤, ⊤ => by simp [WithTop.LocallyFiniteOrder._match1]
    | (a : α), ⊤, (x : α) => by simp [WithTop.LocallyFiniteOrder._match1, coe_eq_coe]
    | (a : α), (b : α), ⊤ => by simp [WithTop.LocallyFiniteOrder._match1]
    | (a : α), (b : α), (x : α) => by simp [WithTop.LocallyFiniteOrder._match1, coe_eq_coe]
  finset_mem_Ico a b x :=
    match a, b, x with
    | ⊤, b, x => iff_of_false (not_mem_empty _) fun h => not_top_lt <| h.1.trans_lt h.2
    | (a : α), ⊤, ⊤ => by simp [WithTop.LocallyFiniteOrder._match2]
    | (a : α), ⊤, (x : α) => by simp [WithTop.LocallyFiniteOrder._match2, coe_eq_coe, coe_lt_top]
    | (a : α), (b : α), ⊤ => by simp [WithTop.LocallyFiniteOrder._match2]
    | (a : α), (b : α), (x : α) => by
      simp [WithTop.LocallyFiniteOrder._match2, coe_eq_coe, coe_lt_coe]
  finset_mem_Ioc a b x :=
    match a, b, x with
    | ⊤, b, x => iff_of_false (not_mem_empty _) fun h => not_top_lt <| h.1.trans_le h.2
    | (a : α), ⊤, ⊤ => by simp [WithTop.LocallyFiniteOrder._match3, coe_lt_top]
    | (a : α), ⊤, (x : α) => by simp [WithTop.LocallyFiniteOrder._match3, coe_eq_coe, coe_lt_coe]
    | (a : α), (b : α), ⊤ => by simp [WithTop.LocallyFiniteOrder._match3]
    | (a : α), (b : α), (x : α) => by
      simp [WithTop.LocallyFiniteOrder._match3, coe_eq_coe, coe_lt_coe]
  finset_mem_Ioo a b x :=
    match a, b, x with
    | ⊤, b, x => iff_of_false (not_mem_empty _) fun h => not_top_lt <| h.1.trans h.2
    | (a : α), ⊤, ⊤ => by simp [WithTop.LocallyFiniteOrder._match4, coe_lt_top]
    | (a : α), ⊤, (x : α) => by
      simp [WithTop.LocallyFiniteOrder._match4, coe_eq_coe, coe_lt_coe, coe_lt_top]
    | (a : α), (b : α), ⊤ => by simp [WithTop.LocallyFiniteOrder._match4]
    | (a : α), (b : α), (x : α) => by
      simp [WithTop.LocallyFiniteOrder._match4, coe_eq_coe, coe_lt_coe]

variable (a b : α)

theorem icc_coe_top : icc (a : WithTop α) ⊤ = insertNone (ici a) :=
  rfl
#align with_top.Icc_coe_top WithTop.icc_coe_top

theorem icc_coe_coe : icc (a : WithTop α) b = (icc a b).map Embedding.some :=
  rfl
#align with_top.Icc_coe_coe WithTop.icc_coe_coe

theorem ico_coe_top : ico (a : WithTop α) ⊤ = (ici a).map Embedding.some :=
  rfl
#align with_top.Ico_coe_top WithTop.ico_coe_top

theorem ico_coe_coe : ico (a : WithTop α) b = (ico a b).map Embedding.some :=
  rfl
#align with_top.Ico_coe_coe WithTop.ico_coe_coe

theorem ioc_coe_top : ioc (a : WithTop α) ⊤ = insertNone (ioi a) :=
  rfl
#align with_top.Ioc_coe_top WithTop.ioc_coe_top

theorem ioc_coe_coe : ioc (a : WithTop α) b = (ioc a b).map Embedding.some :=
  rfl
#align with_top.Ioc_coe_coe WithTop.ioc_coe_coe

theorem ioo_coe_top : ioo (a : WithTop α) ⊤ = (ioi a).map Embedding.some :=
  rfl
#align with_top.Ioo_coe_top WithTop.ioo_coe_top

theorem ioo_coe_coe : ioo (a : WithTop α) b = (ioo a b).map Embedding.some :=
  rfl
#align with_top.Ioo_coe_coe WithTop.ioo_coe_coe

end WithTop

namespace WithBot

variable (α) [PartialOrder α] [OrderBot α] [LocallyFiniteOrder α]

instance : LocallyFiniteOrder (WithBot α) :=
  @OrderDual.locallyFiniteOrder (WithTop αᵒᵈ) _ _

variable (a b : α)

theorem icc_bot_coe : icc (⊥ : WithBot α) b = insertNone (iic b) :=
  rfl
#align with_bot.Icc_bot_coe WithBot.icc_bot_coe

theorem icc_coe_coe : icc (a : WithBot α) b = (icc a b).map Embedding.some :=
  rfl
#align with_bot.Icc_coe_coe WithBot.icc_coe_coe

theorem ico_bot_coe : ico (⊥ : WithBot α) b = insertNone (iio b) :=
  rfl
#align with_bot.Ico_bot_coe WithBot.ico_bot_coe

theorem ico_coe_coe : ico (a : WithBot α) b = (ico a b).map Embedding.some :=
  rfl
#align with_bot.Ico_coe_coe WithBot.ico_coe_coe

theorem ioc_bot_coe : ioc (⊥ : WithBot α) b = (iic b).map Embedding.some :=
  rfl
#align with_bot.Ioc_bot_coe WithBot.ioc_bot_coe

theorem ioc_coe_coe : ioc (a : WithBot α) b = (ioc a b).map Embedding.some :=
  rfl
#align with_bot.Ioc_coe_coe WithBot.ioc_coe_coe

theorem ioo_bot_coe : ioo (⊥ : WithBot α) b = (iio b).map Embedding.some :=
  rfl
#align with_bot.Ioo_bot_coe WithBot.ioo_bot_coe

theorem ioo_coe_coe : ioo (a : WithBot α) b = (ioo a b).map Embedding.some :=
  rfl
#align with_bot.Ioo_coe_coe WithBot.ioo_coe_coe

end WithBot

namespace OrderIso

variable [Preorder α] [Preorder β]

/-! #### Transfer locally finite orders across order isomorphisms -/


-- See note [reducible non-instances]
/-- Transfer `locally_finite_order` across an `order_iso`. -/
@[reducible]
def locallyFiniteOrder [LocallyFiniteOrder β] (f : α ≃o β) : LocallyFiniteOrder α
    where
  finsetIcc a b := (icc (f a) (f b)).map f.symm.toEquiv.toEmbedding
  finsetIco a b := (ico (f a) (f b)).map f.symm.toEquiv.toEmbedding
  finsetIoc a b := (ioc (f a) (f b)).map f.symm.toEquiv.toEmbedding
  finsetIoo a b := (ioo (f a) (f b)).map f.symm.toEquiv.toEmbedding
  finset_mem_Icc := by simp
  finset_mem_Ico := by simp
  finset_mem_Ioc := by simp
  finset_mem_Ioo := by simp
#align order_iso.locally_finite_order OrderIso.locallyFiniteOrder

-- See note [reducible non-instances]
/-- Transfer `locally_finite_order_top` across an `order_iso`. -/
@[reducible]
def locallyFiniteOrderTop [LocallyFiniteOrderTop β] (f : α ≃o β) : LocallyFiniteOrderTop α
    where
  finsetIci a := (ici (f a)).map f.symm.toEquiv.toEmbedding
  finsetIoi a := (ioi (f a)).map f.symm.toEquiv.toEmbedding
  finset_mem_Ici := by simp
  finset_mem_Ioi := by simp
#align order_iso.locally_finite_order_top OrderIso.locallyFiniteOrderTop

-- See note [reducible non-instances]
/-- Transfer `locally_finite_order_bot` across an `order_iso`. -/
@[reducible]
def locallyFiniteOrderBot [LocallyFiniteOrderBot β] (f : α ≃o β) : LocallyFiniteOrderBot α
    where
  finsetIic a := (iic (f a)).map f.symm.toEquiv.toEmbedding
  finsetIio a := (iio (f a)).map f.symm.toEquiv.toEmbedding
  finset_mem_Iic := by simp
  finset_mem_Iio := by simp
#align order_iso.locally_finite_order_bot OrderIso.locallyFiniteOrderBot

end OrderIso

/-! #### Subtype of a locally finite order -/


variable [Preorder α] (p : α → Prop) [DecidablePred p]

instance [LocallyFiniteOrder α] : LocallyFiniteOrder (Subtype p)
    where
  finsetIcc a b := (icc (a : α) b).Subtype p
  finsetIco a b := (ico (a : α) b).Subtype p
  finsetIoc a b := (ioc (a : α) b).Subtype p
  finsetIoo a b := (ioo (a : α) b).Subtype p
  finset_mem_Icc a b x := by simp_rw [Finset.mem_subtype, mem_Icc, Subtype.coe_le_coe]
  finset_mem_Ico a b x := by
    simp_rw [Finset.mem_subtype, mem_Ico, Subtype.coe_le_coe, Subtype.coe_lt_coe]
  finset_mem_Ioc a b x := by
    simp_rw [Finset.mem_subtype, mem_Ioc, Subtype.coe_le_coe, Subtype.coe_lt_coe]
  finset_mem_Ioo a b x := by simp_rw [Finset.mem_subtype, mem_Ioo, Subtype.coe_lt_coe]

instance [LocallyFiniteOrderTop α] : LocallyFiniteOrderTop (Subtype p)
    where
  finsetIci a := (ici (a : α)).Subtype p
  finsetIoi a := (ioi (a : α)).Subtype p
  finset_mem_Ici a x := by simp_rw [Finset.mem_subtype, mem_Ici, Subtype.coe_le_coe]
  finset_mem_Ioi a x := by simp_rw [Finset.mem_subtype, mem_Ioi, Subtype.coe_lt_coe]

instance [LocallyFiniteOrderBot α] : LocallyFiniteOrderBot (Subtype p)
    where
  finsetIic a := (iic (a : α)).Subtype p
  finsetIio a := (iio (a : α)).Subtype p
  finset_mem_Iic a x := by simp_rw [Finset.mem_subtype, mem_Iic, Subtype.coe_le_coe]
  finset_mem_Iio a x := by simp_rw [Finset.mem_subtype, mem_Iio, Subtype.coe_lt_coe]

namespace Finset

section LocallyFiniteOrder

variable [LocallyFiniteOrder α] (a b : Subtype p)

theorem subtype_icc_eq : icc a b = (icc (a : α) b).Subtype p :=
  rfl
#align finset.subtype_Icc_eq Finset.subtype_icc_eq

theorem subtype_ico_eq : ico a b = (ico (a : α) b).Subtype p :=
  rfl
#align finset.subtype_Ico_eq Finset.subtype_ico_eq

theorem subtype_ioc_eq : ioc a b = (ioc (a : α) b).Subtype p :=
  rfl
#align finset.subtype_Ioc_eq Finset.subtype_ioc_eq

theorem subtype_ioo_eq : ioo a b = (ioo (a : α) b).Subtype p :=
  rfl
#align finset.subtype_Ioo_eq Finset.subtype_ioo_eq

variable (hp : ∀ ⦃a b x⦄, a ≤ x → x ≤ b → p a → p b → p x)

include hp

theorem map_subtype_embedding_icc : (icc a b).map (Embedding.subtype p) = icc a b :=
  by
  rw [subtype_Icc_eq]
  refine' Finset.subtype_map_of_mem fun x hx => _
  rw [mem_Icc] at hx
  exact hp hx.1 hx.2 a.prop b.prop
#align finset.map_subtype_embedding_Icc Finset.map_subtype_embedding_icc

theorem map_subtype_embedding_ico : (ico a b).map (Embedding.subtype p) = ico a b :=
  by
  rw [subtype_Ico_eq]
  refine' Finset.subtype_map_of_mem fun x hx => _
  rw [mem_Ico] at hx
  exact hp hx.1 hx.2.le a.prop b.prop
#align finset.map_subtype_embedding_Ico Finset.map_subtype_embedding_ico

theorem map_subtype_embedding_ioc : (ioc a b).map (Embedding.subtype p) = ioc a b :=
  by
  rw [subtype_Ioc_eq]
  refine' Finset.subtype_map_of_mem fun x hx => _
  rw [mem_Ioc] at hx
  exact hp hx.1.le hx.2 a.prop b.prop
#align finset.map_subtype_embedding_Ioc Finset.map_subtype_embedding_ioc

theorem map_subtype_embedding_ioo : (ioo a b).map (Embedding.subtype p) = ioo a b :=
  by
  rw [subtype_Ioo_eq]
  refine' Finset.subtype_map_of_mem fun x hx => _
  rw [mem_Ioo] at hx
  exact hp hx.1.le hx.2.le a.prop b.prop
#align finset.map_subtype_embedding_Ioo Finset.map_subtype_embedding_ioo

end LocallyFiniteOrder

section LocallyFiniteOrderTop

variable [LocallyFiniteOrderTop α] (a : Subtype p)

theorem subtype_ici_eq : ici a = (ici (a : α)).Subtype p :=
  rfl
#align finset.subtype_Ici_eq Finset.subtype_ici_eq

theorem subtype_ioi_eq : ioi a = (ioi (a : α)).Subtype p :=
  rfl
#align finset.subtype_Ioi_eq Finset.subtype_ioi_eq

variable (hp : ∀ ⦃a x⦄, a ≤ x → p a → p x)

include hp

theorem map_subtype_embedding_ici : (ici a).map (Embedding.subtype p) = ici a :=
  by
  rw [subtype_Ici_eq]
  exact Finset.subtype_map_of_mem fun x hx => hp (mem_Ici.1 hx) a.prop
#align finset.map_subtype_embedding_Ici Finset.map_subtype_embedding_ici

theorem map_subtype_embedding_ioi : (ioi a).map (Embedding.subtype p) = ioi a :=
  by
  rw [subtype_Ioi_eq]
  exact Finset.subtype_map_of_mem fun x hx => hp (mem_Ioi.1 hx).le a.prop
#align finset.map_subtype_embedding_Ioi Finset.map_subtype_embedding_ioi

end LocallyFiniteOrderTop

section LocallyFiniteOrderBot

variable [LocallyFiniteOrderBot α] (a : Subtype p)

theorem subtype_iic_eq : iic a = (iic (a : α)).Subtype p :=
  rfl
#align finset.subtype_Iic_eq Finset.subtype_iic_eq

theorem subtype_iio_eq : iio a = (iio (a : α)).Subtype p :=
  rfl
#align finset.subtype_Iio_eq Finset.subtype_iio_eq

variable (hp : ∀ ⦃a x⦄, x ≤ a → p a → p x)

include hp

theorem map_subtype_embedding_iic : (iic a).map (Embedding.subtype p) = iic a :=
  by
  rw [subtype_Iic_eq]
  exact Finset.subtype_map_of_mem fun x hx => hp (mem_Iic.1 hx) a.prop
#align finset.map_subtype_embedding_Iic Finset.map_subtype_embedding_iic

theorem map_subtype_embedding_iio : (iio a).map (Embedding.subtype p) = iio a :=
  by
  rw [subtype_Iio_eq]
  exact Finset.subtype_map_of_mem fun x hx => hp (mem_Iio.1 hx).le a.prop
#align finset.map_subtype_embedding_Iio Finset.map_subtype_embedding_iio

end LocallyFiniteOrderBot

end Finset

