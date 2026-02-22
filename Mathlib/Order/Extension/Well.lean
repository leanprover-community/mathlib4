/-
Copyright (c) 2022 Yaël Dillies, Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Junyan Xu
-/
module

public import Mathlib.Data.Prod.Lex
public import Mathlib.SetTheory.Ordinal.Rank

/-!
# Extend a well-founded order to a well-order

This file constructs a well-order (linear well-founded order) which is an extension of a given
well-founded order.

## Proof idea

We can map our order into two well-orders:
* the first map respects the order but isn't necessarily injective. Namely, this is the *rank*
  function `WellFounded.rank : α → Ordinal`.
* the second map is injective but doesn't necessarily respect the order. This is an arbitrary
  embedding into `Cardinal` given by `embeddingToCardinal`.

Then their lexicographic product is a well-founded linear order which our original order injects in.

## Implementation note

The definition in `mathlib` 3 used an auxiliary well-founded order on `α` lifted from `Cardinal`,
instead of using `Cardinal` directly. The new definition is definitionally equal
to the `mathlib` 3 version but avoids non-standard instances.

## Tags

well-founded relation, well order, extension
-/

@[expose] public section


universe u

variable {α : Type u} {r : α → α → Prop}

namespace WellFounded

variable {α : Type u} (r : α → α → Prop) [WellFounded r]

/-- An arbitrary well order on `α` that extends `r`.

The construction maps `r` into two well-orders: the first map is `WellFounded.rank`, which is not
necessarily injective but respects the order `r`; the other map is the identity (with an arbitrarily
chosen well-order on `α`), which is injective but doesn't respect `r`.

By taking the lexicographic product of the two, we get both properties, so we can pull it back and
get a well-order that extend our original order `r`. Another way to view this is that we choose an
arbitrary well-order to serve as a tiebreak between two elements of same rank.
-/
noncomputable def wellOrderExtension : LinearOrder α :=
  @LinearOrder.lift' α (Ordinal ×ₗ Cardinal) _ (fun a : α => (rank r a, embeddingToCardinal a))
    fun _ _ h => embeddingToCardinal.injective <| congr_arg Prod.snd h

instance wellOrderExtension.wellFounded_lt : WellFounded (wellOrderExtension r).lt :=
  InvImage.wf (fun a : α => (rank r a, embeddingToCardinal a)) <|
    Ordinal.lt_wf.prod_lex Cardinal.lt_wf

instance wellOrderExtension.isWellOrder_lt : IsWellOrder α (wellOrderExtension r).lt where

/-- Any well-founded relation can be extended to a well-ordering on that type. -/
theorem exists_well_order_ge : ∃ s, r ≤ s ∧ IsWellOrder α s :=
  ⟨(wellOrderExtension r).lt, fun _ _ h => Prod.Lex.left _ _ (rank_lt_of_rel h), ⟨⟩⟩

end WellFounded

/-- A type alias for `α`, intended to extend a well-founded order on `α` to a well-order. -/
def WellOrderExtension (α : Type*) : Type _ := α

instance [Inhabited α] : Inhabited (WellOrderExtension α) := ‹_›

/-- "Identity" equivalence between a well-founded order and its well-order extension. -/
def toWellOrderExtension : α ≃ WellOrderExtension α :=
  Equiv.refl _

noncomputable instance [LT α] [h : WellFoundedLT α] : LinearOrder (WellOrderExtension α) :=
  h.wellOrderExtension

theorem toWellOrderExtension_strictMono [Preorder α] [WellFoundedLT α] :
    StrictMono (toWellOrderExtension : α → WellOrderExtension α) := fun _ _ h =>
  Prod.Lex.left _ _ <| WellFounded.rank_lt_of_rel h
