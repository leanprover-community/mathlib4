/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Finset.Preimage
public import Mathlib.Data.Finset.Prod
public import Mathlib.Order.Hom.WithTopBot
public import Mathlib.Order.Interval.Set.UnorderedInterval

/-!
# Locally finite orders

This file defines locally finite orders.

A locally finite order is an order for which all bounded intervals are finite. This allows to make
sense of `Icc`/`Ico`/`Ioc`/`Ioo` as lists, multisets, or finsets.
Further, if the order is bounded above (resp. below), then we can also make sense of the
"unbounded" intervals `Ici`/`Ioi` (resp. `Iic`/`Iio`).

Many theorems about these intervals can be found in `Mathlib/Order/Interval/Finset/Basic.lean`.

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
`NoMinOrder α` and `Nonempty α`. When `OrderBot α`, we can match `a : α` to `#(Iio a)`.

We can provide `SuccOrder α` from `LinearOrder α` and `LocallyFiniteOrder α` using

```lean
lemma exists_min_greater [LinearOrder α] [LocallyFiniteOrder α] {x ub : α} (hx : x < ub) :
    ∃ lub, x < lub ∧ ∀ y, x < y → lub ≤ y := by
  -- very non-golfed
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
set_option backward.defeqAttrib.useBackward true

@[expose] public section

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

/-- `LocallyFiniteOrder.mk'` is the dual of `LocallyFiniteOrder.mk`, which we need for `to_dual`.
Please avoid using this directly. -/
@[to_dual existing mk]
abbrev LocallyFiniteOrder.mk' {α : Type*} [Preorder α]
    (finsetIcc finsetIco finsetIoc finsetIoo : α → α → Finset α)
    (finset_mem_Icc : ∀ (a b x : α), x ∈ finsetIcc a b ↔ x ≤ a ∧ b ≤ x)
    (finset_mem_Ico : ∀ (a b x : α), x ∈ finsetIco a b ↔ x ≤ a ∧ b < x)
    (finset_mem_Ioc : ∀ (a b x : α), x ∈ finsetIoc a b ↔ x < a ∧ b ≤ x)
    (finset_mem_Ioo : ∀ (a b x : α), x ∈ finsetIoo a b ↔ x < a ∧ b < x) : LocallyFiniteOrder α where
  finsetIcc := swap finsetIcc
  finsetIco := swap finsetIoc
  finsetIoc := swap finsetIco
  finsetIoo := swap finsetIoo
  finset_mem_Icc := by grind
  finset_mem_Ico := by grind
  finset_mem_Ioc := by grind
  finset_mem_Ioo := by grind

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

/-- This mixin class describes an order where all intervals bounded above are finite. This is
slightly weaker than `LocallyFiniteOrder` + `OrderBot` as it allows empty types. -/
@[to_dual]
class LocallyFiniteOrderBot (α : Type*) [Preorder α] where
  /-- Left-infinite right-open interval -/
  finsetIio : α → Finset α
  /-- Left-infinite right-closed interval -/
  finsetIic : α → Finset α
  /-- `x ∈ finsetIic a ↔ x ≤ a` -/
  finset_mem_Iic : ∀ a x : α, x ∈ finsetIic a ↔ x ≤ a
  /-- `x ∈ finsetIio a ↔ x < a` -/
  finset_mem_Iio : ∀ a x : α, x ∈ finsetIio a ↔ x < a

/-- A constructor from a definition of `Finset.Icc` alone, the other ones being derived by removing
the ends. As opposed to `LocallyFiniteOrder.ofIcc`, this one requires `DecidableLE` but
only `Preorder`. -/
@[implicit_reducible]
def LocallyFiniteOrder.ofIcc' (α : Type*) [Preorder α] [DecidableLE α]
    (finsetIcc : α → α → Finset α) (mem_Icc : ∀ a b x, x ∈ finsetIcc a b ↔ a ≤ x ∧ x ≤ b) :
    LocallyFiniteOrder α where
  finsetIcc := finsetIcc
  finsetIco a b := {x ∈ finsetIcc a b | ¬b ≤ x}
  finsetIoc a b := {x ∈ finsetIcc a b | ¬x ≤ a}
  finsetIoo a b := {x ∈ finsetIcc a b | ¬x ≤ a ∧ ¬b ≤ x}
  finset_mem_Icc := mem_Icc
  finset_mem_Ico a b x := by rw [Finset.mem_filter, mem_Icc, and_assoc, lt_iff_le_not_ge]
  finset_mem_Ioc a b x := by rw [Finset.mem_filter, mem_Icc, and_right_comm, lt_iff_le_not_ge]
  finset_mem_Ioo a b x := by
    rw [Finset.mem_filter, mem_Icc, and_and_and_comm, lt_iff_le_not_ge, lt_iff_le_not_ge]

/-- A constructor from a definition of `Finset.Icc` alone, the other ones being derived by removing
the ends. As opposed to `LocallyFiniteOrder.ofIcc'`, this one requires `PartialOrder` but only
`DecidableEq`. -/
@[implicit_reducible]
def LocallyFiniteOrder.ofIcc (α : Type*) [PartialOrder α] [DecidableEq α]
    (finsetIcc : α → α → Finset α) (mem_Icc : ∀ a b x, x ∈ finsetIcc a b ↔ a ≤ x ∧ x ≤ b) :
    LocallyFiniteOrder α where
  finsetIcc := finsetIcc
  finsetIco a b := {x ∈ finsetIcc a b | x ≠ b}
  finsetIoc a b := {x ∈ finsetIcc a b | a ≠ x}
  finsetIoo a b := {x ∈ finsetIcc a b | a ≠ x ∧ x ≠ b}
  finset_mem_Icc := mem_Icc
  finset_mem_Ico a b x := by rw [Finset.mem_filter, mem_Icc, and_assoc, lt_iff_le_and_ne]
  finset_mem_Ioc a b x := by rw [Finset.mem_filter, mem_Icc, and_right_comm, lt_iff_le_and_ne]
  finset_mem_Ioo a b x := by
    rw [Finset.mem_filter, mem_Icc, and_and_and_comm, lt_iff_le_and_ne, lt_iff_le_and_ne]

/-- A constructor from a definition of `Finset.Ici` alone, the other ones being derived by removing
the ends. As opposed to `LocallyFiniteOrderTop.ofIci`, this one requires `DecidableLE` but
only `Preorder`. -/
@[to_dual (attr := implicit_reducible)
/-- A constructor from a definition of `Finset.Iic` alone, the other ones being derived by removing
the ends. As opposed to `LocallyFiniteOrderBot.ofIic`, this one requires `DecidableLE` but
only `Preorder`. -/]
def LocallyFiniteOrderTop.ofIci' (α : Type*) [Preorder α] [DecidableLE α]
    (finsetIci : α → Finset α) (mem_Ici : ∀ a x, x ∈ finsetIci a ↔ a ≤ x) :
    LocallyFiniteOrderTop α where
  finsetIci := finsetIci
  finsetIoi a := {x ∈ finsetIci a | ¬x ≤ a}
  finset_mem_Ici := mem_Ici
  finset_mem_Ioi a x := by rw [mem_filter, mem_Ici, lt_iff_le_not_ge]

/-- A constructor from a definition of `Finset.Ici` alone, the other ones being derived by removing
the ends. As opposed to `LocallyFiniteOrderTop.ofIci'`, this one requires `PartialOrder` but
only `DecidableEq`. -/
@[to_dual (attr := implicit_reducible)
/-- A constructor from a definition of `Finset.Iic` alone, the other ones being derived by removing
the ends. As opposed to `LocallyFiniteOrderBot.ofIic'`, this one requires `PartialOrder` but
only `DecidableEq`. -/]
def LocallyFiniteOrderTop.ofIci (α : Type*) [PartialOrder α] [DecidableEq α]
    (finsetIci : α → Finset α) (mem_Ici : ∀ a x, x ∈ finsetIci a ↔ a ≤ x) :
    LocallyFiniteOrderTop α where
  finsetIci := finsetIci
  finsetIoi a := {x ∈ finsetIci a | a ≠ x}
  finset_mem_Ici := mem_Ici
  finset_mem_Ioi a x := by rw [mem_filter, mem_Ici, lt_iff_le_and_ne]

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

-- See note [reducible non-instances]
/-- An empty type is locally finite.

This is not an instance as it would not be defeq to more specific instances. -/
@[to_dual
/-- An empty type is locally finite.

This is not an instance as it would not be defeq to more specific instances. -/]
protected abbrev IsEmpty.toLocallyFiniteOrderTop [Preorder α] [IsEmpty α] :
    LocallyFiniteOrderTop α where
  finsetIci := isEmptyElim
  finsetIoi := isEmptyElim
  finset_mem_Ici := isEmptyElim
  finset_mem_Ioi := isEmptyElim

/-! ### Intervals as finsets -/


namespace Finset

section Preorder

variable [Preorder α]

section LocallyFiniteOrder

variable [LocallyFiniteOrder α] {a b x : α}

/-- The finset $[a, b]$ of elements `x` such that `a ≤ x` and `x ≤ b`. Basically `Set.Icc a b` as a
finset. -/
@[to_dual self (reorder := a b)]
def Icc (a b : α) : Finset α :=
  LocallyFiniteOrder.finsetIcc a b

/-- The finset $[a, b)$ of elements `x` such that `a ≤ x` and `x < b`. Basically `Set.Ico a b` as a
finset. -/
def Ico (a b : α) : Finset α :=
  LocallyFiniteOrder.finsetIco a b

/-- The finset $(a, b]$ of elements `x` such that `a < x` and `x ≤ b`. Basically `Set.Ioc a b` as a
finset. -/
@[to_dual existing (reorder := a b)]
def Ioc (a b : α) : Finset α :=
  LocallyFiniteOrder.finsetIoc a b

/-- The finset $(a, b)$ of elements `x` such that `a < x` and `x < b`. Basically `Set.Ioo a b` as a
finset. -/
@[to_dual self (reorder := a b)]
def Ioo (a b : α) : Finset α :=
  LocallyFiniteOrder.finsetIoo a b

@[simp, grind =]
theorem mem_Icc : x ∈ Icc a b ↔ a ≤ x ∧ x ≤ b :=
  LocallyFiniteOrder.finset_mem_Icc a b x

@[simp, grind =]
theorem mem_Ico : x ∈ Ico a b ↔ a ≤ x ∧ x < b :=
  LocallyFiniteOrder.finset_mem_Ico a b x

@[simp, grind =]
theorem mem_Ioc : x ∈ Ioc a b ↔ a < x ∧ x ≤ b :=
  LocallyFiniteOrder.finset_mem_Ioc a b x

@[simp, grind =]
theorem mem_Ioo : x ∈ Ioo a b ↔ a < x ∧ x < b :=
  LocallyFiniteOrder.finset_mem_Ioo a b x

@[to_dual existing mem_Icc] theorem mem_Icc' : x ∈ Icc a b ↔ x ≤ b ∧ a ≤ x := by grind
@[to_dual existing mem_Ioc] theorem mem_Ico' : x ∈ Ico a b ↔ x < b ∧ a ≤ x := by grind
@[to_dual existing mem_Ico] theorem mem_Ioc' : x ∈ Ioc a b ↔ x ≤ b ∧ a < x := by grind
@[to_dual existing mem_Ioo] theorem mem_Ioo' : x ∈ Ioo a b ↔ x < b ∧ a < x := by grind

@[simp, norm_cast, to_dual self]
theorem coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b :=
  Set.ext fun _ => mem_Icc

@[to_dual (reorder := a b) (attr := simp, norm_cast)]
theorem coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b :=
  Set.ext fun _ => mem_Ico

@[simp, norm_cast, to_dual self]
theorem coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b :=
  Set.ext fun _ => mem_Ioo

@[simp, to_dual self]
theorem _root_.Fintype.card_Icc (a b : α) [Fintype (Set.Icc a b)] :
    Fintype.card (Set.Icc a b) = #(Icc a b) :=
  Fintype.card_of_finset' _ fun _ ↦ by simp

@[to_dual (reorder := a b) (attr := simp)]
theorem _root_.Fintype.card_Ico (a b : α) [Fintype (Set.Ico a b)] :
    Fintype.card (Set.Ico a b) = #(Ico a b) :=
  Fintype.card_of_finset' _ fun _ ↦ by simp

@[simp, to_dual self]
theorem _root_.Fintype.card_Ioo (a b : α) [Fintype (Set.Ioo a b)] :
    Fintype.card (Set.Ioo a b) = #(Ioo a b) :=
  Fintype.card_of_finset' _ fun _ ↦ by simp

end LocallyFiniteOrder

section LocallyFiniteOrderTop

variable [LocallyFiniteOrderTop α] {a x : α}

/-- The finset $[a, ∞)$ of elements `x` such that `a ≤ x`. Basically `Set.Ici a` as a finset. -/
@[to_dual
/-- The finset $(-∞, b]$ of elements `x` such that `x ≤ b`. Basically `Set.Iic b` as a finset. -/]
def Ici (a : α) : Finset α :=
  LocallyFiniteOrderTop.finsetIci a

/-- The finset $(a, ∞)$ of elements `x` such that `a < x`. Basically `Set.Ioi a` as a finset. -/
@[to_dual
/-- The finset $(-∞, b)$ of elements `x` such that `x < b`. Basically `Set.Iio b` as a finset. -/]
def Ioi (a : α) : Finset α :=
  LocallyFiniteOrderTop.finsetIoi a

@[to_dual (attr := simp, grind =)]
theorem mem_Ici : x ∈ Ici a ↔ a ≤ x :=
  LocallyFiniteOrderTop.finset_mem_Ici _ _

@[to_dual (attr := simp, grind =)]
theorem mem_Ioi : x ∈ Ioi a ↔ a < x :=
  LocallyFiniteOrderTop.finset_mem_Ioi _ _

@[to_dual (attr := simp, norm_cast)]
theorem coe_Ici (a : α) : (Ici a : Set α) = Set.Ici a :=
  Set.ext fun _ => mem_Ici

@[to_dual (attr := simp, norm_cast)]
theorem coe_Ioi (a : α) : (Ioi a : Set α) = Set.Ioi a :=
  Set.ext fun _ => mem_Ioi

@[to_dual (attr := simp)]
theorem _root_.Fintype.card_Ici (a : α) [Fintype (Set.Ici a)] :
    Fintype.card (Set.Ici a) = #(Ici a) :=
  Fintype.card_of_finset' _ fun _ ↦ by simp

@[to_dual (attr := simp)]
theorem _root_.Fintype.card_Ioi (a : α) [Fintype (Set.Ioi a)] :
    Fintype.card (Set.Ioi a) = #(Ioi a) :=
  Fintype.card_of_finset' _ fun _ ↦ by simp

end LocallyFiniteOrderTop

section OrderTop

variable [LocallyFiniteOrder α] [OrderTop α] {a x : α}

-- See note [lower priority instance]
@[to_dual]
instance (priority := 100) _root_.LocallyFiniteOrder.toLocallyFiniteOrderTop :
    LocallyFiniteOrderTop α where
  finsetIci b := Icc b ⊤
  finsetIoi b := Ioc b ⊤
  finset_mem_Ici a x := by rw [mem_Icc, and_iff_left le_top]
  finset_mem_Ioi a x := by rw [mem_Ioc, and_iff_left le_top]

@[to_dual]
theorem Ici_eq_Icc (a : α) : Ici a = Icc a ⊤ :=
  rfl

@[to_dual]
theorem Ioi_eq_Ioc (a : α) : Ioi a = Ioc a ⊤ :=
  rfl

end OrderTop

end Preorder

section Lattice

variable [Lattice α] [LocallyFiniteOrder α] {a b x : α}

/-- `Finset.uIcc a b` is the set of elements lying between `a` and `b`, with `a` and `b` included.
Note that we define it more generally in a lattice as `Finset.Icc (a ⊓ b) (a ⊔ b)`. In a
product type, `Finset.uIcc` corresponds to the bounding box of the two elements. -/
def uIcc (a b : α) : Finset α :=
  Icc (a ⊓ b) (a ⊔ b)

@[inherit_doc]
scoped[FinsetInterval] notation "[[" a ", " b "]]" => Finset.uIcc a b

@[simp]
theorem mem_uIcc : x ∈ uIcc a b ↔ a ⊓ b ≤ x ∧ x ≤ a ⊔ b :=
  mem_Icc

@[simp, norm_cast]
theorem coe_uIcc (a b : α) : (Finset.uIcc a b : Set α) = Set.uIcc a b :=
  coe_Icc _ _

@[simp]
theorem _root_.Fintype.card_uIcc (a b : α) [Fintype (Set.uIcc a b)] :
    Fintype.card (Set.uIcc a b) = #(uIcc a b) :=
  Fintype.card_of_finset' _ fun _ ↦ by simp [Set.uIcc]

end Lattice

end Finset

namespace Mathlib.Meta
open Lean Elab Term Meta Batteries.ExtendedBinder

/-- Elaborate set builder notation for `Finset`.

* `{x ≤ a | p x}` is elaborated as `Finset.filter (fun x ↦ p x) (Finset.Iic a)` if the expected type
  is `Finset ?α`.
* `{x ≥ a | p x}` is elaborated as `Finset.filter (fun x ↦ p x) (Finset.Ici a)` if the expected type
  is `Finset ?α`.
* `{x < a | p x}` is elaborated as `Finset.filter (fun x ↦ p x) (Finset.Iio a)` if the expected type
  is `Finset ?α`.
* `{x > a | p x}` is elaborated as `Finset.filter (fun x ↦ p x) (Finset.Ioi a)` if the expected type
  is `Finset ?α`.

See also
* `Data.Set.Defs` for the `Set` builder notation elaborator that this elaborator partly overrides.
* `Data.Finset.Basic` for the `Finset` builder notation elaborator partly overriding this one for
  syntax of the form `{x ∈ s | p x}`.
* `Data.Fintype.Basic` for the `Finset` builder notation elaborator handling syntax of the form
  `{x | p x}`, `{x : α | p x}`, `{x ∉ s | p x}`, `{x ≠ a | p x}`.

TODO: Write a delaborator
-/
@[term_elab setBuilder]
meta def elabFinsetBuilderIxx : TermElab
  | `({ $x:ident ≤ $a | $p }), expectedType? => do
    -- If the expected type is not known to be `Finset ?α`, give up.
    unless ← knownToBeFinsetNotSet expectedType? do throwUnsupportedSyntax
    elabTerm (← `(Finset.filter (fun $x:ident ↦ $p) (Finset.Iic $a))) expectedType?
  | `({ $x:ident ≥ $a | $p }), expectedType? => do
    -- If the expected type is not known to be `Finset ?α`, give up.
    unless ← knownToBeFinsetNotSet expectedType? do throwUnsupportedSyntax
    elabTerm (← `(Finset.filter (fun $x:ident ↦ $p) (Finset.Ici $a))) expectedType?
  | `({ $x:ident < $a | $p }), expectedType? => do
    -- If the expected type is not known to be `Finset ?α`, give up.
    unless ← knownToBeFinsetNotSet expectedType? do throwUnsupportedSyntax
    elabTerm (← `(Finset.filter (fun $x:ident ↦ $p) (Finset.Iio $a))) expectedType?
  | `({ $x:ident > $a | $p }), expectedType? => do
    -- If the expected type is not known to be `Finset ?α`, give up.
    unless ← knownToBeFinsetNotSet expectedType? do throwUnsupportedSyntax
    elabTerm (← `(Finset.filter (fun $x:ident ↦ $p) (Finset.Ioi $a))) expectedType?
  | _, _ => throwUnsupportedSyntax

end Mathlib.Meta

/-! ### Finiteness of `Set` intervals -/


namespace Set

section Preorder

variable [Preorder α] [LocallyFiniteOrder α] (a b : α)

@[to_dual self]
instance instFintypeIcc : Fintype (Icc a b) := .ofFinset (Finset.Icc a b) fun _ => by simp

@[to_dual (reorder := a b)]
instance instFintypeIco : Fintype (Ico a b) := .ofFinset (Finset.Ico a b) fun _ => by simp

@[to_dual self]
instance instFintypeIoo : Fintype (Ioo a b) := .ofFinset (Finset.Ioo a b) fun _ => by simp

@[simp, to_dual self]
lemma finite_Icc : (Icc a b).Finite := (Icc a b).toFinite

@[to_dual (reorder := a b) (attr := simp)]
lemma finite_Ico : (Ico a b).Finite := (Ico a b).toFinite

@[simp, to_dual self]
lemma finite_Ioo : (Ioo a b).Finite := (Ioo a b).toFinite

end Preorder

section OrderTop

variable [Preorder α] [LocallyFiniteOrderTop α] (a : α)

@[to_dual]
instance instFintypeIci : Fintype (Ici a) := .ofFinset (Finset.Ici a) fun _ => Finset.mem_Ici

@[to_dual]
instance instFintypeIoi : Fintype (Ioi a) := .ofFinset (Finset.Ioi a) fun _ => Finset.mem_Ioi

@[to_dual (attr := simp)] lemma finite_Ici : (Ici a).Finite := (Ici a).toFinite
@[to_dual (attr := simp)] lemma finite_Ioi : (Ioi a).Finite := (Ioi a).toFinite

end OrderTop

section Lattice
variable [Lattice α] [LocallyFiniteOrder α] (a b : α)

instance fintypeUIcc : Fintype (uIcc a b) :=
  Fintype.ofFinset (Finset.uIcc a b) fun _ => Finset.mem_uIcc

@[simp] lemma finite_uIcc : (uIcc a b).Finite := (uIcc _ _).toFinite

@[deprecated (since := "2026-02-03")] alias finite_interval := finite_uIcc

end Lattice

end Set

/-! ### Instances -/

section Preorder

variable [Preorder α] [Preorder β]

/-- A noncomputable constructor from the finiteness of all closed intervals. -/
@[implicit_reducible]
noncomputable def LocallyFiniteOrder.ofFiniteIcc (h : ∀ a b : α, (Set.Icc a b).Finite) :
    LocallyFiniteOrder α :=
  @LocallyFiniteOrder.ofIcc' α _ (Classical.decRel _) (fun a b => (h a b).toFinset) fun a b x => by
    rw [Set.Finite.mem_toFinset, Set.mem_Icc]

/-- A fintype is a locally finite order.

This is not an instance as it would not be defeq to better instances such as
`Fin.locallyFiniteOrder`.
-/
abbrev Fintype.toLocallyFiniteOrder [Fintype α] [DecidableLT α] [DecidableLE α] :
    LocallyFiniteOrder α where
  finsetIcc a b := (Set.Icc a b).toFinset
  finsetIco a b := (Set.Ico a b).toFinset
  finsetIoc a b := (Set.Ioc a b).toFinset
  finsetIoo a b := (Set.Ioo a b).toFinset
  finset_mem_Icc a b x := by simp only [Set.mem_toFinset, Set.mem_Icc]
  finset_mem_Ico a b x := by simp only [Set.mem_toFinset, Set.mem_Ico]
  finset_mem_Ioc a b x := by simp only [Set.mem_toFinset, Set.mem_Ioc]
  finset_mem_Ioo a b x := by simp only [Set.mem_toFinset, Set.mem_Ioo]

instance : Subsingleton (LocallyFiniteOrder α) :=
  Subsingleton.intro fun h₀ h₁ => by
    obtain ⟨h₀_finset_Icc, h₀_finset_Ico, h₀_finset_Ioc, h₀_finset_Ioo,
      h₀_finset_mem_Icc, h₀_finset_mem_Ico, h₀_finset_mem_Ioc, h₀_finset_mem_Ioo⟩ := h₀
    obtain ⟨h₁_finset_Icc, h₁_finset_Ico, h₁_finset_Ioc, h₁_finset_Ioo,
      h₁_finset_mem_Icc, h₁_finset_mem_Ico, h₁_finset_mem_Ioc, h₁_finset_mem_Ioo⟩ := h₁
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

@[to_dual]
instance : Subsingleton (LocallyFiniteOrderTop α) :=
  Subsingleton.intro fun h₀ h₁ => by
    obtain ⟨h₀_finset_Ioi, h₀_finset_Ici, h₀_finset_mem_Ici, h₀_finset_mem_Ioi⟩ := h₀
    obtain ⟨h₁_finset_Ioi, h₁_finset_Ici, h₁_finset_mem_Ici, h₁_finset_mem_Ioi⟩ := h₁
    have hIci : h₀_finset_Ici = h₁_finset_Ici := by
      ext a b
      rw [h₀_finset_mem_Ici, h₁_finset_mem_Ici]
    have hIoi : h₀_finset_Ioi = h₁_finset_Ioi := by
      ext a b
      rw [h₀_finset_mem_Ioi, h₁_finset_mem_Ioi]
    simp_rw [hIci, hIoi]

-- Should this be called `LocallyFiniteOrder.lift`?
/-- Given an order embedding `α ↪o β`, pulls back the `LocallyFiniteOrder` on `β` to `α`. -/
@[implicit_reducible]
protected noncomputable def OrderEmbedding.locallyFiniteOrder [LocallyFiniteOrder β] (f : α ↪o β) :
    LocallyFiniteOrder α where
  finsetIcc a b := (Icc (f a) (f b)).preimage f f.toEmbedding.injective.injOn
  finsetIco a b := (Ico (f a) (f b)).preimage f f.toEmbedding.injective.injOn
  finsetIoc a b := (Ioc (f a) (f b)).preimage f f.toEmbedding.injective.injOn
  finsetIoo a b := (Ioo (f a) (f b)).preimage f f.toEmbedding.injective.injOn
  finset_mem_Icc a b x := by rw [mem_preimage, mem_Icc, f.le_iff_le, f.le_iff_le]
  finset_mem_Ico a b x := by rw [mem_preimage, mem_Ico, f.le_iff_le, f.lt_iff_lt]
  finset_mem_Ioc a b x := by rw [mem_preimage, mem_Ioc, f.lt_iff_lt, f.le_iff_le]
  finset_mem_Ioo a b x := by rw [mem_preimage, mem_Ioo, f.lt_iff_lt, f.lt_iff_lt]

/-! ### `OrderDual` -/

open OrderDual

section LocallyFiniteOrder

variable [LocallyFiniteOrder α] (a b : α)

/-- Note we define `Icc (toDual a) (toDual b)` as `Icc α _ _ b a` (which has type `Finset α` not
`Finset αᵒᵈ`!) instead of `(Icc b a).map toDual.toEmbedding` as this means the
following is defeq:
```
lemma this : (Icc (toDual (toDual a)) (toDual (toDual b)) :) = (Icc a b :) := rfl
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

@[to_dual self]
lemma Finset.Icc_orderDual_def (a b : αᵒᵈ) :
    Icc a b = (Icc (ofDual b) (ofDual a)).map toDual.toEmbedding := map_refl.symm

@[to_dual (reorder := a b)]
lemma Finset.Ico_orderDual_def (a b : αᵒᵈ) :
    Ico a b = (Ioc (ofDual b) (ofDual a)).map toDual.toEmbedding := map_refl.symm

@[to_dual self]
lemma Finset.Ioo_orderDual_def (a b : αᵒᵈ) :
    Ioo a b = (Ioo (ofDual b) (ofDual a)).map toDual.toEmbedding := map_refl.symm

@[to_dual self]
lemma Finset.Icc_toDual : Icc (toDual a) (toDual b) = (Icc b a).map toDual.toEmbedding :=
  map_refl.symm

@[to_dual (reorder := a b)]
lemma Finset.Ico_toDual : Ico (toDual a) (toDual b) = (Ioc b a).map toDual.toEmbedding :=
  map_refl.symm

@[to_dual self]
lemma Finset.Ioo_toDual : Ioo (toDual a) (toDual b) = (Ioo b a).map toDual.toEmbedding :=
  map_refl.symm

@[to_dual self]
lemma Finset.Icc_ofDual (a b : αᵒᵈ) :
    Icc (ofDual a) (ofDual b) = (Icc b a).map ofDual.toEmbedding := map_refl.symm

@[to_dual (reorder := a b)]
lemma Finset.Ico_ofDual (a b : αᵒᵈ) :
    Ico (ofDual a) (ofDual b) = (Ioc b a).map ofDual.toEmbedding := map_refl.symm

@[to_dual self]
lemma Finset.Ioo_ofDual (a b : αᵒᵈ) :
    Ioo (ofDual a) (ofDual b) = (Ioo b a).map ofDual.toEmbedding := map_refl.symm

end LocallyFiniteOrder

section LocallyFiniteOrderTop

variable [LocallyFiniteOrderTop α]

/-- Note we define `Iic (toDual a)` as `Ici a` (which has type `Finset α` not `Finset αᵒᵈ`!)
instead of `(Ici a).map toDual.toEmbedding` as this means the following is defeq:
```
lemma this : (Iic (toDual (toDual a)) :) = (Iic a :) := rfl
```
-/
@[to_dual
/-- Note we define `Ici (toDual a)` as `Iic a` (which has type `Finset α` not `Finset αᵒᵈ`!)
instead of `(Iic a).map toDual.toEmbedding` as this means the following is defeq:
```
lemma this : (Ici (toDual (toDual a)) :) = (Ici a :) := rfl
```
-/]
instance OrderDual.instLocallyFiniteOrderBot : LocallyFiniteOrderBot αᵒᵈ where
  finsetIic a := @Ici α _ _ (ofDual a)
  finsetIio a := @Ioi α _ _ (ofDual a)
  finset_mem_Iic _ _ := mem_Ici (α := α)
  finset_mem_Iio _ _ := mem_Ioi (α := α)

@[to_dual]
lemma Iic_orderDual_def (a : αᵒᵈ) : Iic a = (Ici (ofDual a)).map toDual.toEmbedding := map_refl.symm

@[to_dual]
lemma Iio_orderDual_def (a : αᵒᵈ) : Iio a = (Ioi (ofDual a)).map toDual.toEmbedding := map_refl.symm

@[to_dual]
lemma Finset.Iic_toDual (a : α) : Iic (toDual a) = (Ici a).map toDual.toEmbedding :=
  map_refl.symm

@[to_dual]
lemma Finset.Iio_toDual (a : α) : Iio (toDual a) = (Ioi a).map toDual.toEmbedding :=
  map_refl.symm

@[to_dual]
lemma Finset.Ici_ofDual (a : αᵒᵈ) : Ici (ofDual a) = (Iic a).map ofDual.toEmbedding :=
  map_refl.symm

@[to_dual]
lemma Finset.Ioi_ofDual (a : αᵒᵈ) : Ioi (ofDual a) = (Iio a).map ofDual.toEmbedding :=
  map_refl.symm

end LocallyFiniteOrderTop

/-! ### `Prod` -/

section LocallyFiniteOrder
variable [LocallyFiniteOrder α] [LocallyFiniteOrder β] [DecidableLE (α × β)]

instance Prod.instLocallyFiniteOrder : LocallyFiniteOrder (α × β) :=
  LocallyFiniteOrder.ofIcc' (α × β) (fun x y ↦ Icc x.1 y.1 ×ˢ Icc x.2 y.2) fun a b x => by
    rw [mem_product, mem_Icc, mem_Icc, and_and_and_comm, le_def, le_def]

@[to_dual self]
lemma Finset.Icc_prod_def (x y : α × β) : Icc x y = Icc x.1 y.1 ×ˢ Icc x.2 y.2 := rfl

@[to_dual self]
lemma Finset.Icc_product_Icc (a₁ a₂ : α) (b₁ b₂ : β) :
    Icc a₁ a₂ ×ˢ Icc b₁ b₂ = Icc (a₁, b₁) (a₂, b₂) := rfl

@[to_dual self]
lemma Finset.card_Icc_prod (x y : α × β) : #(Icc x y) = #(Icc x.1 y.1) * #(Icc x.2 y.2) :=
  card_product ..

end LocallyFiniteOrder

section LocallyFiniteOrderTop
variable [LocallyFiniteOrderTop α] [LocallyFiniteOrderTop β] [DecidableLE (α × β)]

@[to_dual]
instance Prod.instLocallyFiniteOrderTop : LocallyFiniteOrderTop (α × β) :=
  LocallyFiniteOrderTop.ofIci' (α × β) (fun x => Ici x.1 ×ˢ Ici x.2) fun a x => by
    rw [mem_product, mem_Ici, mem_Ici, le_def]

@[to_dual]
lemma Finset.Ici_prod_def (x : α × β) : Ici x = Ici x.1 ×ˢ Ici x.2 := rfl

@[to_dual Iic_product_Iic]
lemma Finset.Ici_product_Ici (a : α) (b : β) : Ici a ×ˢ Ici b = Ici (a, b) := rfl

@[to_dual]
lemma Finset.card_Ici_prod (x : α × β) : #(Ici x) = #(Ici x.1) * #(Ici x.2) :=
  card_product _ _

end LocallyFiniteOrderTop
end Preorder

section Lattice
variable [Lattice α] [Lattice β] [LocallyFiniteOrder α] [LocallyFiniteOrder β] [DecidableLE (α × β)]

lemma Finset.uIcc_prod_def (x y : α × β) : uIcc x y = uIcc x.1 y.1 ×ˢ uIcc x.2 y.2 := rfl

lemma Finset.uIcc_product_uIcc (a₁ a₂ : α) (b₁ b₂ : β) :
    uIcc a₁ a₂ ×ˢ uIcc b₁ b₂ = uIcc (a₁, b₁) (a₂, b₂) := rfl

lemma Finset.card_uIcc_prod (x y : α × β) : #(uIcc x y) = #(uIcc x.1 y.1) * #(uIcc x.2 y.2) :=
  card_product ..

end Lattice

/-!
#### `WithTop`, `WithBot`

Adding a `⊤` to a locally finite `OrderTop` keeps it locally finite.
Adding a `⊥` to a locally finite `OrderBot` keeps it locally finite.
-/


namespace WithTop

/-- Given a finset on `α`, lift it to being a finset on `WithTop α`
using `WithTop.some` and then insert `⊤`. -/
@[to_dual /-- Given a finset on `α`, lift it to being a finset on `WithBot α`
using `WithBot.some` and then insert `⊥`. -/]
def insertTop : Finset α ↪o Finset (WithTop α) :=
  OrderEmbedding.ofMapLEIff
    (fun s => cons ⊤ (s.map Embedding.coeWithTop) <| by simp)
    (fun s t => by rw [le_iff_subset, cons_subset_cons, map_subset_map, le_iff_subset])

@[to_dual (attr := simp)]
theorem some_mem_insertTop {s : Finset α} {a : α} : ↑a ∈ insertTop s ↔ a ∈ s := by
  simp [insertTop]

@[to_dual (attr := simp)]
theorem top_mem_insertTop {s : Finset α} : ⊤ ∈ insertTop s := by
  simp [insertTop]

variable (α) [PartialOrder α] [OrderTop α] [LocallyFiniteOrder α]

@[to_dual]
instance : LocallyFiniteOrder (WithTop α) where
  finsetIcc a b :=
    match a, b with
    | ⊤, ⊤ => {⊤}
    | ⊤, (b : α) => ∅
    | (a : α), ⊤ => insertTop (Ici a)
    | (a : α), (b : α) => (Icc a b).map Embedding.coeWithTop
  finsetIco a b :=
    match a, b with
    | ⊤, _ => ∅
    | (a : α), ⊤ => (Ici a).map Embedding.coeWithTop
    | (a : α), (b : α) => (Ico a b).map Embedding.coeWithTop
  finsetIoc a b :=
    match a, b with
    | ⊤, _ => ∅
    | (a : α), ⊤ => insertTop (Ioi a)
    | (a : α), (b : α) => (Ioc a b).map Embedding.coeWithTop
  finsetIoo a b :=
    match a, b with
    | ⊤, _ => ∅
    | (a : α), ⊤ => (Ioi a).map Embedding.coeWithTop
    | (a : α), (b : α) => (Ioo a b).map Embedding.coeWithTop
  finset_mem_Icc a b x := by
    cases a <;> cases b <;> cases x <;> simp
  finset_mem_Ico a b x := by
    cases a <;> cases b <;> cases x <;> simp
  finset_mem_Ioc a b x := by
    cases a <;> cases b <;> cases x <;> simp
  finset_mem_Ioo a b x := by
    cases a <;> cases b <;> cases x <;> simp

variable (a b : α)

@[to_dual Icc_bot_coe]
theorem Icc_coe_top : Icc (a : WithTop α) ⊤ = insertNone (Ici a) :=
  rfl

@[to_dual]
theorem Icc_coe_coe : Icc (a : WithTop α) b = (Icc a b).map Embedding.some :=
  rfl

@[to_dual Ioc_bot_coe]
theorem Ico_coe_top : Ico (a : WithTop α) ⊤ = (Ici a).map Embedding.some :=
  rfl

@[to_dual]
theorem Ico_coe_coe : Ico (a : WithTop α) b = (Ico a b).map Embedding.some :=
  rfl

@[to_dual Ico_bot_coe]
theorem Ioc_coe_top : Ioc (a : WithTop α) ⊤ = insertNone (Ioi a) :=
  rfl

@[to_dual]
theorem Ioc_coe_coe : Ioc (a : WithTop α) b = (Ioc a b).map Embedding.some :=
  rfl

@[to_dual Ioo_bot_coe]
theorem Ioo_coe_top : Ioo (a : WithTop α) ⊤ = (Ioi a).map Embedding.some :=
  rfl

@[to_dual]
theorem Ioo_coe_coe : Ioo (a : WithTop α) b = (Ioo a b).map Embedding.some :=
  rfl

end WithTop

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

-- See note [reducible non-instances]
/-- Transfer `LocallyFiniteOrderTop` across an `OrderIso`. -/
@[to_dual /-- Transfer `LocallyFiniteOrderBot` across an `OrderIso`. -/]
abbrev locallyFiniteOrderTop [LocallyFiniteOrderTop β] (f : α ≃o β) : LocallyFiniteOrderTop α where
  finsetIci a := (Ici (f a)).map f.symm.toEquiv.toEmbedding
  finsetIoi a := (Ioi (f a)).map f.symm.toEquiv.toEmbedding
  finset_mem_Ici := by simp
  finset_mem_Ioi := by simp

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

@[to_dual]
instance Subtype.instLocallyFiniteOrderTop [LocallyFiniteOrderTop α] :
    LocallyFiniteOrderTop (Subtype p) where
  finsetIci a := (Ici (a : α)).subtype p
  finsetIoi a := (Ioi (a : α)).subtype p
  finset_mem_Ici a x := by simp_rw [Finset.mem_subtype, mem_Ici, Subtype.coe_le_coe]
  finset_mem_Ioi a x := by simp_rw [Finset.mem_subtype, mem_Ioi, Subtype.coe_lt_coe]

namespace Finset

section LocallyFiniteOrder

variable [LocallyFiniteOrder α] (a b : Subtype p)

@[to_dual self]
theorem subtype_Icc_eq : Icc a b = (Icc (a : α) b).subtype p :=
  rfl

@[to_dual (reorder := a b)]
theorem subtype_Ico_eq : Ico a b = (Ico (a : α) b).subtype p :=
  rfl

@[to_dual self]
theorem subtype_Ioo_eq : Ioo a b = (Ioo (a : α) b).subtype p :=
  rfl

theorem map_subtype_embedding_Icc (hp : ∀ ⦃a b x⦄, a ≤ x → x ≤ b → p a → p b → p x) :
    (Icc a b).map (Embedding.subtype p) = (Icc a b : Finset α) := by
  rw [subtype_Icc_eq]
  refine Finset.subtype_map_of_mem fun x hx => ?_
  rw [mem_Icc] at hx
  exact hp hx.1 hx.2 a.prop b.prop

theorem map_subtype_embedding_Ico (hp : ∀ ⦃a b x⦄, a ≤ x → x ≤ b → p a → p b → p x) :
    (Ico a b).map (Embedding.subtype p) = (Ico a b : Finset α) := by
  rw [subtype_Ico_eq]
  refine Finset.subtype_map_of_mem fun x hx => ?_
  rw [mem_Ico] at hx
  exact hp hx.1 hx.2.le a.prop b.prop

theorem map_subtype_embedding_Ioc (hp : ∀ ⦃a b x⦄, a ≤ x → x ≤ b → p a → p b → p x) :
    (Ioc a b).map (Embedding.subtype p) = (Ioc a b : Finset α) := by
  rw [subtype_Ioc_eq]
  refine Finset.subtype_map_of_mem fun x hx => ?_
  rw [mem_Ioc] at hx
  exact hp hx.1.le hx.2 a.prop b.prop

theorem map_subtype_embedding_Ioo (hp : ∀ ⦃a b x⦄, a ≤ x → x ≤ b → p a → p b → p x) :
    (Ioo a b).map (Embedding.subtype p) = (Ioo a b : Finset α) := by
  rw [subtype_Ioo_eq]
  refine Finset.subtype_map_of_mem fun x hx => ?_
  rw [mem_Ioo] at hx
  exact hp hx.1.le hx.2.le a.prop b.prop

end LocallyFiniteOrder

section LocallyFiniteOrderTop

variable [LocallyFiniteOrderTop α] (a : Subtype p)

@[to_dual]
theorem subtype_Ici_eq : Ici a = (Ici (a : α)).subtype p :=
  rfl

@[to_dual]
theorem subtype_Ioi_eq : Ioi a = (Ioi (a : α)).subtype p :=
  rfl

@[to_dual]
theorem map_subtype_embedding_Ici (hp : ∀ ⦃a x⦄, a ≤ x → p a → p x) :
    (Ici a).map (Embedding.subtype p) = (Ici a : Finset α) := by
  rw [subtype_Ici_eq]
  exact Finset.subtype_map_of_mem fun x hx => hp (mem_Ici.1 hx) a.prop

@[to_dual]
theorem map_subtype_embedding_Ioi (hp : ∀ ⦃a x⦄, a ≤ x → p a → p x) :
    (Ioi a).map (Embedding.subtype p) = (Ioi a : Finset α) := by
  rw [subtype_Ioi_eq]
  exact Finset.subtype_map_of_mem fun x hx => hp (mem_Ioi.1 hx).le a.prop

end LocallyFiniteOrderTop


end Finset

section Finite

variable {α : Type*} {s : Set α}

@[to_dual]
theorem BddBelow.finite_of_bddAbove [Preorder α] [LocallyFiniteOrder α]
    {s : Set α} (h₀ : BddBelow s) (h₁ : BddAbove s) :
    s.Finite :=
  let ⟨a, ha⟩ := h₀
  let ⟨b, hb⟩ := h₁
  (Set.finite_Icc a b).subset fun _x hx ↦ ⟨ha hx, hb hx⟩

@[to_dual]
theorem Set.finite_iff_bddAbove [SemilatticeSup α] [LocallyFiniteOrder α] [OrderBot α] :
    s.Finite ↔ BddAbove s :=
  ⟨fun h ↦ ⟨h.toFinset.sup id, fun _ hx ↦ Finset.le_sup (f := id) ((Finite.mem_toFinset h).mpr hx)⟩,
    fun ⟨m, hm⟩ ↦ (Set.finite_Icc ⊥ m).subset (fun _ hx ↦ ⟨bot_le, hm hx⟩)⟩

@[to_dual]
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

variable {y : α}

@[to_dual]
instance (priority := low) [DecidableLE α] [LocallyFiniteOrder α] :
    LocallyFiniteOrderTop { x : α // x ≤ y } where
  finsetIoi a := Finset.Ioc a ⟨y, by rfl⟩
  finsetIci a := Finset.Icc a ⟨y, by rfl⟩
  finset_mem_Ici a b := by
    simp only [Finset.mem_Icc, and_iff_left_iff_imp]
    exact fun _ => b.property
  finset_mem_Ioi a b := by
    simp only [Finset.mem_Ioc, and_iff_left_iff_imp]
    exact fun _ => b.property

@[to_dual]
instance (priority := low) [DecidableLT α] [LocallyFiniteOrder α] :
    LocallyFiniteOrderTop { x : α // x < y } where
  finsetIoi a := (Finset.Ioo ↑a y).subtype _
  finsetIci a := (Finset.Ico ↑a y).subtype _
  finset_mem_Ici a b := by
    simp only [Finset.mem_subtype, Finset.mem_Ico, Subtype.coe_le_coe, and_iff_left_iff_imp]
    exact fun _ => b.property
  finset_mem_Ioi a b := by
    simp only [Finset.mem_subtype, Finset.mem_Ioo, Subtype.coe_lt_coe, and_iff_left_iff_imp]
    exact fun _ => b.property

@[to_dual]
instance [LocallyFiniteOrderBot α] : Finite { x : α // x ≤ y } := by
  simpa only [coe_Iic] using (Finset.Iic y).finite_toSet

@[to_dual]
instance [LocallyFiniteOrderBot α] : Finite { x : α // x < y } := by
  simpa only [coe_Iio] using (Finset.Iio y).finite_toSet

namespace Set
variable {α : Type*} [Preorder α]

section LocallyFiniteOrder
variable [LocallyFiniteOrder α]

@[simp, to_dual self]
lemma toFinset_Icc (a b : α) [Fintype (Icc a b)] : (Icc a b).toFinset = Finset.Icc a b := by
  ext; simp

@[to_dual (reorder := a b) (attr := simp)]
lemma toFinset_Ico (a b : α) [Fintype (Ico a b)] : (Ico a b).toFinset = Finset.Ico a b := by
  ext; simp

@[simp, to_dual self]
lemma toFinset_Ioo (a b : α) [Fintype (Ioo a b)] : (Ioo a b).toFinset = Finset.Ioo a b := by
  ext; simp

end LocallyFiniteOrder

section LocallyFiniteOrderTop
variable [LocallyFiniteOrderTop α]

@[to_dual (attr := simp)]
lemma toFinset_Ici (a : α) [Fintype (Ici a)] : (Ici a).toFinset = Finset.Ici a := by ext; simp

@[to_dual (attr := simp)]
lemma toFinset_Ioi (a : α) [Fintype (Ioi a)] : (Ioi a).toFinset = Finset.Ioi a := by ext; simp

end LocallyFiniteOrderTop
end Set

/-- A `LocallyFiniteOrder` can be transferred across an order isomorphism. -/
-- See note [reducible non-instances]
abbrev LocallyFiniteOrder.ofOrderIsoClass {F M N : Type*} [Preorder M] [Preorder N]
    [EquivLike F M N] [OrderIsoClass F M N] (f : F) [LocallyFiniteOrder N] :
    LocallyFiniteOrder M where
  finsetIcc x y := (finsetIcc (f x) (f y)).map ⟨EquivLike.inv f, (EquivLike.right_inv f).injective⟩
  finsetIco x y := (finsetIco (f x) (f y)).map ⟨EquivLike.inv f, (EquivLike.right_inv f).injective⟩
  finsetIoc x y := (finsetIoc (f x) (f y)).map ⟨EquivLike.inv f, (EquivLike.right_inv f).injective⟩
  finsetIoo x y := (finsetIoo (f x) (f y)).map ⟨EquivLike.inv f, (EquivLike.right_inv f).injective⟩
  finset_mem_Icc := by simp [finset_mem_Icc, EquivLike.inv_apply_eq]
  finset_mem_Ico := by
    simp [finset_mem_Ico, EquivLike.inv_apply_eq, map_lt_map_iff]
  finset_mem_Ioc := by
    simp [finset_mem_Ioc, EquivLike.inv_apply_eq, map_lt_map_iff]
  finset_mem_Ioo := by
    simp [finset_mem_Ioo, EquivLike.inv_apply_eq, map_lt_map_iff]
