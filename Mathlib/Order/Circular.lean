/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Lattice
public import Mathlib.Tactic.Order

/-!
# Circular order hierarchy

This file defines circular preorders, circular partial orders and circular orders.

## Hierarchy

* A ternary "betweenness" relation `btw : α → α → α → Prop` forms a `CircularOrder` if it is
  - reflexive: `btw a a a`
  - cyclic: `btw a b c → btw b c a`
  - antisymmetric: `btw a b c → btw c b a → a = b ∨ b = c ∨ c = a`
  - total: `btw a b c ∨ btw c b a`

  along with a strict betweenness relation `sbtw : α → α → α → Prop` which respects
  `sbtw a b c ↔ btw a b c ∧ ¬ btw c b a`, analogously to how `<` and `≤` are related, and is
  - transitive: `sbtw a b c → sbtw b d c → sbtw a d c`.

* A `CircularPartialOrder` drops totality.

* A `CircularPreorder` further drops antisymmetry.

The intuition is that a circular order is a circle and `btw a b c` means that going around
clockwise from `a` you reach `b` before `c` (`b` is between `a` and `c` is meaningless on an
unoriented circle). A circular partial order is several, potentially intersecting, circles. A
circular preorder is like a circular partial order, but several points can coexist.

Note that the relations between `CircularPreorder`, `CircularPartialOrder` and `CircularOrder`
are subtler than between `Preorder`, `PartialOrder`, `LinearOrder`. In particular, one cannot
simply extend the `Btw` of a `CircularPartialOrder` to make it a `CircularOrder`.

One can translate from usual orders to circular ones by "closing the necklace at infinity". See
`LE.toBtw` and `LT.toSBtw`. Going the other way involves "cutting the necklace" or
"rolling the necklace open".

## Examples

Some concrete circular orders one encounters in the wild are `ZMod n` for `0 < n`, `Circle`,
`Real.Angle`...

## Main definitions

* `Set.cIcc`: Closed-closed circular interval.
* `Set.cIoo`: Open-open circular interval.

## Notes

There's an unsolved diamond on `OrderDual α` here. The instances `LE α → Btw αᵒᵈ` and
`LT α → SBtw αᵒᵈ` can each be inferred in two ways:
* `LE α` → `Btw α` → `Btw αᵒᵈ` vs
  `LE α` → `LE αᵒᵈ` → `Btw αᵒᵈ`
* `LT α` → `SBtw α` → `SBtw αᵒᵈ` vs
  `LT α` → `LT αᵒᵈ` → `SBtw αᵒᵈ`

The fields are propeq, but not defeq. It is temporarily fixed by turning the circularizing instances
into definitions.

## TODO

Antisymmetry is quite weak in the sense that there's no way to discriminate which two points are
equal. This prevents defining closed-open intervals `cIco` and `cIoc` in the neat `=`-less way. We
currently haven't defined them at all.

What is the correct generality of "rolling the necklace" open? At least, this works for `α × β` and
`β × α` where `α` is a circular order and `β` is a linear order.

What's next is to define circular groups and provide instances for `ZMod n`, the usual circle group
`Circle`, and `RootsOfUnity M`. What conditions do we need on `M` for this last one
to work?

We should have circular order homomorphisms. The typical example is
`daysToMonth : DaysOfTheYear →c MonthsOfTheYear` which relates the circular order of days
and the circular order of months. Is `α →c β` a good notation?

## References

* https://en.wikipedia.org/wiki/Cyclic_order
* https://en.wikipedia.org/wiki/Partial_cyclic_order

## Tags

circular order, cyclic order, circularly ordered set, cyclically ordered set
-/

public section

assert_not_exists RelIso

/-- Syntax typeclass for a betweenness relation. -/
class Btw (α : Type*) where
  /-- Betweenness for circular orders. `btw a b c` states that `b` is between `a` and `c` (in that
  order). -/
  btw : α → α → α → Prop

export Btw (btw)

/-- Syntax typeclass for a strict betweenness relation. -/
class SBtw (α : Type*) where
  /-- Strict betweenness for circular orders. `sbtw a b c` states that `b` is strictly between `a`
  and `c` (in that order). -/
  sbtw : α → α → α → Prop

export SBtw (sbtw)

/-- A circular preorder is the analogue of a preorder where you can loop around. `≤` and `<` are
replaced by ternary relations `btw` and `sbtw`. `btw` is reflexive and cyclic. `sbtw` is transitive.
-/
class CircularPreorder (α : Type*) extends Btw α, SBtw α where
  /-- `a` is between `a` and `a`. -/
  btw_refl (a : α) : btw a a a
  /-- If `b` is between `a` and `c`, then `c` is between `b` and `a`.
  This is motivated by imagining three points on a circle. -/
  btw_cyclic_left {a b c : α} : btw a b c → btw b c a
  sbtw := fun a b c => btw a b c ∧ ¬btw c b a
  /-- Strict betweenness is given by betweenness in one direction and non-betweenness in the other.

  I.e., if `b` is between `a` and `c` but not between `c` and `a`, then we say `b` is strictly
  between `a` and `c`. -/
  sbtw_iff_btw_not_btw {a b c : α} : sbtw a b c ↔ btw a b c ∧ ¬btw c b a := by intros; rfl
  /-- For any fixed `c`, `fun a b ↦ sbtw a b c` is a transitive relation.

  I.e., given `a` `b` `d` `c` in that "order", if we have `b` strictly between `a` and `c`, and `d`
  strictly between `b` and `c`, then `d` is strictly between `a` and `c`. -/
  sbtw_trans_left {a b c d : α} : sbtw a b c → sbtw b d c → sbtw a d c

export CircularPreorder (btw_refl btw_cyclic_left sbtw_trans_left)

/-- A circular partial order is the analogue of a partial order where you can loop around. `≤` and
`<` are replaced by ternary relations `btw` and `sbtw`. `btw` is reflexive, cyclic and
antisymmetric. `sbtw` is transitive. -/
class CircularPartialOrder (α : Type*) extends CircularPreorder α where
  /-- If `b` is between `a` and `c` and also between `c` and `a`, then at least one pair of points
  among `a`, `b`, `c` are identical. -/
  btw_antisymm {a b c : α} : btw a b c → btw c b a → a = b ∨ b = c ∨ c = a

export CircularPartialOrder (btw_antisymm)

/-- A circular order is the analogue of a linear order where you can loop around. `≤` and `<` are
replaced by ternary relations `btw` and `sbtw`. `btw` is reflexive, cyclic, antisymmetric and total.
`sbtw` is transitive. -/
class CircularOrder (α : Type*) extends CircularPartialOrder α where
  /-- For any triple of points, the second is between the other two one way or another. -/
  btw_total : ∀ a b c : α, btw a b c ∨ btw c b a

export CircularOrder (btw_total)

/-! ### Circular preorders -/


section CircularPreorder

variable {α : Type*} [CircularPreorder α]

theorem btw_rfl {a : α} : btw a a a :=
  btw_refl _

-- TODO: `alias` creates a def instead of a lemma (because `btw_cyclic_left` is a def).
-- alias btw_cyclic_left        ← Btw.btw.cyclic_left
theorem Btw.btw.cyclic_left {a b c : α} (h : btw a b c) : btw b c a :=
  btw_cyclic_left h

theorem btw_cyclic_right {a b c : α} (h : btw a b c) : btw c a b :=
  h.cyclic_left.cyclic_left

alias Btw.btw.cyclic_right := btw_cyclic_right

/-- The order of the `↔` has been chosen so that `rw [btw_cyclic]` cycles to the right while
`rw [← btw_cyclic]` cycles to the left (thus following the prepended arrow). -/
theorem btw_cyclic {a b c : α} : btw a b c ↔ btw c a b :=
  ⟨btw_cyclic_right, btw_cyclic_left⟩

theorem sbtw_iff_btw_not_btw {a b c : α} : sbtw a b c ↔ btw a b c ∧ ¬btw c b a :=
  CircularPreorder.sbtw_iff_btw_not_btw

theorem btw_of_sbtw {a b c : α} (h : sbtw a b c) : btw a b c :=
  (sbtw_iff_btw_not_btw.1 h).1

alias SBtw.sbtw.btw := btw_of_sbtw

theorem not_btw_of_sbtw {a b c : α} (h : sbtw a b c) : ¬btw c b a :=
  (sbtw_iff_btw_not_btw.1 h).2

alias SBtw.sbtw.not_btw := not_btw_of_sbtw

theorem not_sbtw_of_btw {a b c : α} (h : btw a b c) : ¬sbtw c b a := fun h' => h'.not_btw h

alias Btw.btw.not_sbtw := not_sbtw_of_btw

theorem sbtw_of_btw_not_btw {a b c : α} (habc : btw a b c) (hcba : ¬btw c b a) : sbtw a b c :=
  sbtw_iff_btw_not_btw.2 ⟨habc, hcba⟩

alias Btw.btw.sbtw_of_not_btw := sbtw_of_btw_not_btw

theorem sbtw_cyclic_left {a b c : α} (h : sbtw a b c) : sbtw b c a :=
  h.btw.cyclic_left.sbtw_of_not_btw fun h' => h.not_btw h'.cyclic_left

alias SBtw.sbtw.cyclic_left := sbtw_cyclic_left

theorem sbtw_cyclic_right {a b c : α} (h : sbtw a b c) : sbtw c a b :=
  h.cyclic_left.cyclic_left

alias SBtw.sbtw.cyclic_right := sbtw_cyclic_right

/-- The order of the `↔` has been chosen so that `rw [sbtw_cyclic]` cycles to the right while
`rw [← sbtw_cyclic]` cycles to the left (thus following the prepended arrow). -/
theorem sbtw_cyclic {a b c : α} : sbtw a b c ↔ sbtw c a b :=
  ⟨sbtw_cyclic_right, sbtw_cyclic_left⟩

-- TODO: `alias` creates a def instead of a lemma (because `sbtw_trans_left` is a def).
-- alias btw_trans_left        ← SBtw.sbtw.trans_left
theorem SBtw.sbtw.trans_left {a b c d : α} (h : sbtw a b c) : sbtw b d c → sbtw a d c :=
  sbtw_trans_left h

theorem sbtw_trans_right {a b c d : α} (hbc : sbtw a b c) (hcd : sbtw a c d) : sbtw a b d :=
  (hbc.cyclic_left.trans_left hcd.cyclic_left).cyclic_right

alias SBtw.sbtw.trans_right := sbtw_trans_right

theorem sbtw_asymm {a b c : α} (h : sbtw a b c) : ¬sbtw c b a :=
  h.btw.not_sbtw

alias SBtw.sbtw.not_sbtw := sbtw_asymm

theorem sbtw_irrefl_left_right {a b : α} : ¬sbtw a b a := fun h => h.not_btw h.btw

theorem sbtw_irrefl_left {a b : α} : ¬sbtw a a b := fun h => sbtw_irrefl_left_right h.cyclic_left

theorem sbtw_irrefl_right {a b : α} : ¬sbtw a b b := fun h => sbtw_irrefl_left_right h.cyclic_right

theorem sbtw_irrefl (a : α) : ¬sbtw a a a :=
  sbtw_irrefl_left_right

end CircularPreorder

/-! ### Circular partial orders -/


section CircularPartialOrder

variable {α : Type*} [CircularPartialOrder α]

-- TODO: `alias` creates a def instead of a lemma (because `btw_antisymm` is a def).
-- alias btw_antisymm        ← Btw.btw.antisymm
theorem Btw.btw.antisymm {a b c : α} (h : btw a b c) : btw c b a → a = b ∨ b = c ∨ c = a :=
  btw_antisymm h

end CircularPartialOrder

/-! ### Circular orders -/


section CircularOrder

variable {α : Type*} [CircularOrder α]

theorem btw_refl_left_right (a b : α) : btw a b a :=
  or_self_iff.1 (btw_total a b a)

theorem btw_rfl_left_right {a b : α} : btw a b a :=
  btw_refl_left_right _ _

theorem btw_refl_left (a b : α) : btw a a b :=
  btw_rfl_left_right.cyclic_right

theorem btw_rfl_left {a b : α} : btw a a b :=
  btw_refl_left _ _

theorem btw_refl_right (a b : α) : btw a b b :=
  btw_rfl_left_right.cyclic_left

theorem btw_rfl_right {a b : α} : btw a b b :=
  btw_refl_right _ _

theorem sbtw_iff_not_btw {a b c : α} : sbtw a b c ↔ ¬btw c b a := by
  rw [sbtw_iff_btw_not_btw]
  exact and_iff_right_of_imp (btw_total _ _ _).resolve_left

theorem btw_iff_not_sbtw {a b c : α} : btw a b c ↔ ¬sbtw c b a :=
  iff_not_comm.1 sbtw_iff_not_btw

end CircularOrder

/-! ### Circular intervals -/


namespace Set

section CircularPreorder

variable {α : Type*} [CircularPreorder α]

/-- Closed-closed circular interval -/
def cIcc (a b : α) : Set α :=
  { x | btw a x b }

/-- Open-open circular interval -/
def cIoo (a b : α) : Set α :=
  { x | sbtw a x b }

@[simp]
theorem mem_cIcc {a b x : α} : x ∈ cIcc a b ↔ btw a x b :=
  Iff.rfl

@[simp]
theorem mem_cIoo {a b x : α} : x ∈ cIoo a b ↔ sbtw a x b :=
  Iff.rfl

end CircularPreorder

section CircularOrder

variable {α : Type*} [CircularOrder α]

theorem left_mem_cIcc (a b : α) : a ∈ cIcc a b :=
  btw_rfl_left

theorem right_mem_cIcc (a b : α) : b ∈ cIcc a b :=
  btw_rfl_right

theorem compl_cIcc {a b : α} : (cIcc a b)ᶜ = cIoo b a := by
  ext
  rw [Set.mem_cIoo, sbtw_iff_not_btw, cIcc, mem_compl_iff, mem_setOf]

theorem compl_cIoo {a b : α} : (cIoo a b)ᶜ = cIcc b a := by
  ext
  rw [Set.mem_cIcc, btw_iff_not_sbtw, cIoo, mem_compl_iff, mem_setOf]

end CircularOrder

end Set

/-! ### Circularizing instances -/


/-- The betweenness relation obtained from "looping around" `≤`.
See note [reducible non-instances]. -/
abbrev LE.toBtw (α : Type*) [LE α] : Btw α where
  btw a b c := a ≤ b ∧ b ≤ c ∨ b ≤ c ∧ c ≤ a ∨ c ≤ a ∧ a ≤ b

/-- The strict betweenness relation obtained from "looping around" `<`.
See note [reducible non-instances]. -/
abbrev LT.toSBtw (α : Type*) [LT α] : SBtw α where
  sbtw a b c := a < b ∧ b < c ∨ b < c ∧ c < a ∨ c < a ∧ a < b

section

variable {α : Type*} {a b c : α}

attribute [local instance] LE.toBtw LT.toSBtw

/-- The following lemmas are about the non-instances `LE.toBtw`, `LT.toSBtw` and
`LinearOrder.toCircularOrder`. -/
lemma btw_iff [LE α] : btw a b c ↔ a ≤ b ∧ b ≤ c ∨ b ≤ c ∧ c ≤ a ∨ c ≤ a ∧ a ≤ b := .rfl
/-- The following lemmas are about the non-instances `LE.toBtw`, `LT.toSBtw` and
`LinearOrder.toCircularOrder`. -/
lemma sbtw_iff [LT α] : sbtw a b c ↔ a < b ∧ b < c ∨ b < c ∧ c < a ∨ c < a ∧ a < b := .rfl

end

/-- The circular preorder obtained from "looping around" a preorder.
See note [reducible non-instances]. -/
abbrev Preorder.toCircularPreorder (α : Type*) [Preorder α] : CircularPreorder α where
  btw a b c := a ≤ b ∧ b ≤ c ∨ b ≤ c ∧ c ≤ a ∨ c ≤ a ∧ a ≤ b
  sbtw a b c := a < b ∧ b < c ∨ b < c ∧ c < a ∨ c < a ∧ a < b
  btw_refl _ := .inl ⟨le_rfl, le_rfl⟩
  btw_cyclic_left {a b c} := .rotate
  sbtw_trans_left {a b c d} := by
    rintro (⟨hab, hbc⟩ | ⟨hbc, hca⟩ | ⟨hca, hab⟩) (⟨hbd, hdc⟩ | ⟨hdc, hcb⟩ | ⟨hcb, hbd⟩) <;>
      first
      | refine .inl ?_; constructor <;> order
      | refine .inr <| .inl ?_; constructor <;> order
      | refine .inr <| .inr ?_; constructor <;> order
  sbtw_iff_btw_not_btw {a b c} := by
    simp_rw [lt_iff_le_not_ge]
    grind

/-- The circular partial order obtained from "looping around" a partial order.
See note [reducible non-instances]. -/
abbrev PartialOrder.toCircularPartialOrder (α : Type*) [PartialOrder α] : CircularPartialOrder α :=
  { Preorder.toCircularPreorder α with
    btw_antisymm := fun {a b c} => by
      rintro (⟨hab, hbc⟩ | ⟨hbc, hca⟩ | ⟨hca, hab⟩) (⟨hcb, hba⟩ | ⟨hba, hac⟩ | ⟨hac, hcb⟩)
      · exact Or.inl (hab.antisymm hba)
      · exact Or.inl (hab.antisymm hba)
      · exact Or.inr (Or.inl <| hbc.antisymm hcb)
      · exact Or.inr (Or.inl <| hbc.antisymm hcb)
      · exact Or.inr (Or.inr <| hca.antisymm hac)
      · exact Or.inr (Or.inl <| hbc.antisymm hcb)
      · exact Or.inl (hab.antisymm hba)
      · exact Or.inl (hab.antisymm hba)
      · exact Or.inr (Or.inr <| hca.antisymm hac) }

/-- The circular order obtained from "looping around" a linear order.
See note [reducible non-instances]. -/
abbrev LinearOrder.toCircularOrder (α : Type*) [LinearOrder α] : CircularOrder α :=
  { PartialOrder.toCircularPartialOrder α with
    btw_total := fun a b c => by
      rcases le_total a b with hab | hba <;> rcases le_total b c with hbc | hcb <;>
        rcases le_total c a with hca | hac
      · exact Or.inl (Or.inl ⟨hab, hbc⟩)
      · exact Or.inl (Or.inl ⟨hab, hbc⟩)
      · exact Or.inl (Or.inr <| Or.inr ⟨hca, hab⟩)
      · exact Or.inr (Or.inr <| Or.inr ⟨hac, hcb⟩)
      · exact Or.inl (Or.inr <| Or.inl ⟨hbc, hca⟩)
      · exact Or.inr (Or.inr <| Or.inl ⟨hba, hac⟩)
      · exact Or.inr (Or.inl ⟨hcb, hba⟩)
      · exact Or.inr (Or.inr <| Or.inl ⟨hba, hac⟩) }

/-! ### Dual constructions -/


namespace OrderDual

instance btw (α : Type*) [h : Btw α] : Btw αᵒᵈ :=
  ⟨fun a b c => h.btw c b a⟩

instance sbtw (α : Type*) [h : SBtw α] : SBtw αᵒᵈ :=
  ⟨fun a b c => h.sbtw c b a⟩

instance circularPreorder (α : Type*) [CircularPreorder α] : CircularPreorder αᵒᵈ where
  btw_refl _ := btw_refl _
  btw_cyclic_left {_ _ _} := @btw_cyclic_right α _ _ _ _
  sbtw_trans_left {_ _ _ _} habc hbdc := hbdc.trans_right habc
  sbtw_iff_btw_not_btw {a b c} := @sbtw_iff_btw_not_btw α _ c b a

instance circularPartialOrder (α : Type*) [CircularPartialOrder α] : CircularPartialOrder αᵒᵈ where
  btw_antisymm := fun {_ _ _} habc hcba => @btw_antisymm α _ _ _ _ hcba habc

instance (α : Type*) [CircularOrder α] : CircularOrder αᵒᵈ where
  btw_total := fun {a b c} => @btw_total α _ c b a

end OrderDual
