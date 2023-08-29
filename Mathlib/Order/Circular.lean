/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Set.Basic

#align_import order.circular from "leanprover-community/mathlib"@"213b0cff7bc5ab6696ee07cceec80829ce42efec"

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
simply extend the `btw` of a `CircularPartialOrder` to make it a `CircularOrder`.

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
`days_to_month : days_of_the_year →c months_of_the_year` which relates the circular order of days
and the circular order of months. Is `α →c β` a good notation?

## References

* https://en.wikipedia.org/wiki/Cyclic_order
* https://en.wikipedia.org/wiki/Partial_cyclic_order

## Tags

circular order, cyclic order, circularly ordered set, cyclically ordered set
-/


/-- Syntax typeclass for a betweenness relation. -/
class Btw (α : Type*) where
  /-- Betweenness for circular orders. `btw a b c` states that `b` is between `a` and `c` (in that
  order). -/
  btw : α → α → α → Prop
#align has_btw Btw

export Btw (btw)

/-- Syntax typeclass for a strict betweenness relation. -/
class SBtw (α : Type*) where
  /-- Strict betweenness for circular orders. `sbtw a b c` states that `b` is strictly between `a`
  and `c` (in that order). -/
  sbtw : α → α → α → Prop
#align has_sbtw SBtw

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
#align circular_preorder CircularPreorder

export CircularPreorder (btw_refl btw_cyclic_left sbtw_trans_left)

/-- A circular partial order is the analogue of a partial order where you can loop around. `≤` and
`<` are replaced by ternary relations `btw` and `sbtw`. `btw` is reflexive, cyclic and
antisymmetric. `sbtw` is transitive. -/
class CircularPartialOrder (α : Type*) extends CircularPreorder α where
  /-- If `b` is between `a` and `c` and also between `c` and `a`, then at least one pair of points
  among `a`, `b`, `c` are identical. -/
  btw_antisymm {a b c : α} : btw a b c → btw c b a → a = b ∨ b = c ∨ c = a
#align circular_partial_order CircularPartialOrder

export CircularPartialOrder (btw_antisymm)

/-- A circular order is the analogue of a linear order where you can loop around. `≤` and `<` are
replaced by ternary relations `btw` and `sbtw`. `btw` is reflexive, cyclic, antisymmetric and total.
`sbtw` is transitive. -/
class CircularOrder (α : Type*) extends CircularPartialOrder α where
  /-- For any triple of points, the second is between the other two one way or another. -/
  btw_total : ∀ a b c : α, btw a b c ∨ btw c b a
#align circular_order CircularOrder

export CircularOrder (btw_total)

/-! ### Circular preorders -/


section CircularPreorder

variable {α : Type*} [CircularPreorder α]

theorem btw_rfl {a : α} : btw a a a :=
  btw_refl _
#align btw_rfl btw_rfl

-- TODO: `alias` creates a def instead of a lemma (because `btw_cyclic_left` is a def).
-- alias btw_cyclic_left        ← Btw.btw.cyclic_left
theorem Btw.btw.cyclic_left {a b c : α} (h : btw a b c) : btw b c a :=
  btw_cyclic_left h
#align has_btw.btw.cyclic_left Btw.btw.cyclic_left

theorem btw_cyclic_right {a b c : α} (h : btw a b c) : btw c a b :=
  h.cyclic_left.cyclic_left
#align btw_cyclic_right btw_cyclic_right

alias Btw.btw.cyclic_right := btw_cyclic_right
#align has_btw.btw.cyclic_right Btw.btw.cyclic_right

/-- The order of the `↔` has been chosen so that `rw [btw_cyclic]` cycles to the right while
`rw [← btw_cyclic]` cycles to the left (thus following the prepended arrow). -/
theorem btw_cyclic {a b c : α} : btw a b c ↔ btw c a b :=
  ⟨btw_cyclic_right, btw_cyclic_left⟩
#align btw_cyclic btw_cyclic

theorem sbtw_iff_btw_not_btw {a b c : α} : sbtw a b c ↔ btw a b c ∧ ¬btw c b a :=
  CircularPreorder.sbtw_iff_btw_not_btw
#align sbtw_iff_btw_not_btw sbtw_iff_btw_not_btw

theorem btw_of_sbtw {a b c : α} (h : sbtw a b c) : btw a b c :=
  (sbtw_iff_btw_not_btw.1 h).1
#align btw_of_sbtw btw_of_sbtw

alias SBtw.sbtw.btw := btw_of_sbtw
#align has_sbtw.sbtw.btw SBtw.sbtw.btw

theorem not_btw_of_sbtw {a b c : α} (h : sbtw a b c) : ¬btw c b a :=
  (sbtw_iff_btw_not_btw.1 h).2
#align not_btw_of_sbtw not_btw_of_sbtw

alias SBtw.sbtw.not_btw := not_btw_of_sbtw
#align has_sbtw.sbtw.not_btw SBtw.sbtw.not_btw

theorem not_sbtw_of_btw {a b c : α} (h : btw a b c) : ¬sbtw c b a := fun h' => h'.not_btw h
#align not_sbtw_of_btw not_sbtw_of_btw

alias Btw.btw.not_sbtw := not_sbtw_of_btw
#align has_btw.btw.not_sbtw Btw.btw.not_sbtw

theorem sbtw_of_btw_not_btw {a b c : α} (habc : btw a b c) (hcba : ¬btw c b a) : sbtw a b c :=
  sbtw_iff_btw_not_btw.2 ⟨habc, hcba⟩
#align sbtw_of_btw_not_btw sbtw_of_btw_not_btw

alias Btw.btw.sbtw_of_not_btw := sbtw_of_btw_not_btw
#align has_btw.btw.sbtw_of_not_btw Btw.btw.sbtw_of_not_btw

theorem sbtw_cyclic_left {a b c : α} (h : sbtw a b c) : sbtw b c a :=
  h.btw.cyclic_left.sbtw_of_not_btw fun h' => h.not_btw h'.cyclic_left
#align sbtw_cyclic_left sbtw_cyclic_left

alias SBtw.sbtw.cyclic_left := sbtw_cyclic_left
#align has_sbtw.sbtw.cyclic_left SBtw.sbtw.cyclic_left

theorem sbtw_cyclic_right {a b c : α} (h : sbtw a b c) : sbtw c a b :=
  h.cyclic_left.cyclic_left
#align sbtw_cyclic_right sbtw_cyclic_right

alias SBtw.sbtw.cyclic_right := sbtw_cyclic_right
#align has_sbtw.sbtw.cyclic_right SBtw.sbtw.cyclic_right

/-- The order of the `↔` has been chosen so that `rw [sbtw_cyclic]` cycles to the right while
`rw [← sbtw_cyclic]` cycles to the left (thus following the prepended arrow). -/
theorem sbtw_cyclic {a b c : α} : sbtw a b c ↔ sbtw c a b :=
  ⟨sbtw_cyclic_right, sbtw_cyclic_left⟩
#align sbtw_cyclic sbtw_cyclic

-- TODO: `alias` creates a def instead of a lemma (because `sbtw_trans_left` is a def).
-- alias btw_trans_left        ← SBtw.sbtw.trans_left
theorem SBtw.sbtw.trans_left {a b c d : α} (h : sbtw a b c) : sbtw b d c → sbtw a d c :=
  sbtw_trans_left h
#align has_sbtw.sbtw.trans_left SBtw.sbtw.trans_left

theorem sbtw_trans_right {a b c d : α} (hbc : sbtw a b c) (hcd : sbtw a c d) : sbtw a b d :=
  (hbc.cyclic_left.trans_left hcd.cyclic_left).cyclic_right
#align sbtw_trans_right sbtw_trans_right

alias SBtw.sbtw.trans_right := sbtw_trans_right
#align has_sbtw.sbtw.trans_right SBtw.sbtw.trans_right

theorem sbtw_asymm {a b c : α} (h : sbtw a b c) : ¬sbtw c b a :=
  h.btw.not_sbtw
#align sbtw_asymm sbtw_asymm

alias SBtw.sbtw.not_sbtw := sbtw_asymm
#align has_sbtw.sbtw.not_sbtw SBtw.sbtw.not_sbtw

theorem sbtw_irrefl_left_right {a b : α} : ¬sbtw a b a := fun h => h.not_btw h.btw
#align sbtw_irrefl_left_right sbtw_irrefl_left_right

theorem sbtw_irrefl_left {a b : α} : ¬sbtw a a b := fun h => sbtw_irrefl_left_right h.cyclic_left
#align sbtw_irrefl_left sbtw_irrefl_left

theorem sbtw_irrefl_right {a b : α} : ¬sbtw a b b := fun h => sbtw_irrefl_left_right h.cyclic_right
#align sbtw_irrefl_right sbtw_irrefl_right

theorem sbtw_irrefl (a : α) : ¬sbtw a a a :=
  sbtw_irrefl_left_right
#align sbtw_irrefl sbtw_irrefl

end CircularPreorder

/-! ### Circular partial orders -/


section CircularPartialOrder

variable {α : Type*} [CircularPartialOrder α]

-- TODO: `alias` creates a def instead of a lemma (because `btw_antisymm` is a def).
-- alias btw_antisymm        ← Btw.btw.antisymm
theorem Btw.btw.antisymm {a b c : α} (h : btw a b c) : btw c b a → a = b ∨ b = c ∨ c = a :=
  btw_antisymm h
#align has_btw.btw.antisymm Btw.btw.antisymm

end CircularPartialOrder

/-! ### Circular orders -/


section CircularOrder

variable {α : Type*} [CircularOrder α]

theorem btw_refl_left_right (a b : α) : btw a b a :=
  (or_self_iff _).1 (btw_total a b a)
#align btw_refl_left_right btw_refl_left_right

theorem btw_rfl_left_right {a b : α} : btw a b a :=
  btw_refl_left_right _ _
#align btw_rfl_left_right btw_rfl_left_right

theorem btw_refl_left (a b : α) : btw a a b :=
  btw_rfl_left_right.cyclic_right
#align btw_refl_left btw_refl_left

theorem btw_rfl_left {a b : α} : btw a a b :=
  btw_refl_left _ _
#align btw_rfl_left btw_rfl_left

theorem btw_refl_right (a b : α) : btw a b b :=
  btw_rfl_left_right.cyclic_left
#align btw_refl_right btw_refl_right

theorem btw_rfl_right {a b : α} : btw a b b :=
  btw_refl_right _ _
#align btw_rfl_right btw_rfl_right

theorem sbtw_iff_not_btw {a b c : α} : sbtw a b c ↔ ¬btw c b a := by
  rw [sbtw_iff_btw_not_btw]
  -- ⊢ btw a b c ∧ ¬btw c b a ↔ ¬btw c b a
  exact and_iff_right_of_imp (btw_total _ _ _).resolve_left
  -- 🎉 no goals
#align sbtw_iff_not_btw sbtw_iff_not_btw

theorem btw_iff_not_sbtw {a b c : α} : btw a b c ↔ ¬sbtw c b a :=
  iff_not_comm.1 sbtw_iff_not_btw
#align btw_iff_not_sbtw btw_iff_not_sbtw

end CircularOrder

/-! ### Circular intervals -/


namespace Set

section CircularPreorder

variable {α : Type*} [CircularPreorder α]

/-- Closed-closed circular interval -/
def cIcc (a b : α) : Set α :=
  { x | btw a x b }
#align set.cIcc Set.cIcc

/-- Open-open circular interval -/
def cIoo (a b : α) : Set α :=
  { x | sbtw a x b }
#align set.cIoo Set.cIoo

@[simp]
theorem mem_cIcc {a b x : α} : x ∈ cIcc a b ↔ btw a x b :=
  Iff.rfl
#align set.mem_cIcc Set.mem_cIcc

@[simp]
theorem mem_cIoo {a b x : α} : x ∈ cIoo a b ↔ sbtw a x b :=
  Iff.rfl
#align set.mem_cIoo Set.mem_cIoo

end CircularPreorder

section CircularOrder

variable {α : Type*} [CircularOrder α]

theorem left_mem_cIcc (a b : α) : a ∈ cIcc a b :=
  btw_rfl_left
#align set.left_mem_cIcc Set.left_mem_cIcc

theorem right_mem_cIcc (a b : α) : b ∈ cIcc a b :=
  btw_rfl_right
#align set.right_mem_cIcc Set.right_mem_cIcc

theorem compl_cIcc {a b : α} : (cIcc a b)ᶜ = cIoo b a := by
  ext
  -- ⊢ x✝ ∈ (cIcc a b)ᶜ ↔ x✝ ∈ cIoo b a
  rw [Set.mem_cIoo, sbtw_iff_not_btw, cIcc, mem_compl_iff, mem_setOf]
  -- 🎉 no goals
#align set.compl_cIcc Set.compl_cIcc

theorem compl_cIoo {a b : α} : (cIoo a b)ᶜ = cIcc b a := by
  ext
  -- ⊢ x✝ ∈ (cIoo a b)ᶜ ↔ x✝ ∈ cIcc b a
  rw [Set.mem_cIcc, btw_iff_not_sbtw, cIoo, mem_compl_iff, mem_setOf]
  -- 🎉 no goals
#align set.compl_cIoo Set.compl_cIoo

end CircularOrder

end Set

/-! ### Circularizing instances -/


/-- The betweenness relation obtained from "looping around" `≤`.
See note [reducible non-instances]. -/
@[reducible]
def LE.toBtw (α : Type*) [LE α] : Btw α where
  btw a b c := a ≤ b ∧ b ≤ c ∨ b ≤ c ∧ c ≤ a ∨ c ≤ a ∧ a ≤ b
#align has_le.to_has_btw LE.toBtw

/-- The strict betweenness relation obtained from "looping around" `<`.
See note [reducible non-instances]. -/
@[reducible]
def LT.toSBtw (α : Type*) [LT α] : SBtw α where
  sbtw a b c := a < b ∧ b < c ∨ b < c ∧ c < a ∨ c < a ∧ a < b
#align has_lt.to_has_sbtw LT.toSBtw

/-- The circular preorder obtained from "looping around" a preorder.
See note [reducible non-instances]. -/
@[reducible]
def Preorder.toCircularPreorder (α : Type*) [Preorder α] : CircularPreorder α where
  btw a b c := a ≤ b ∧ b ≤ c ∨ b ≤ c ∧ c ≤ a ∨ c ≤ a ∧ a ≤ b
  sbtw a b c := a < b ∧ b < c ∨ b < c ∧ c < a ∨ c < a ∧ a < b
  btw_refl a := Or.inl ⟨le_rfl, le_rfl⟩
  btw_cyclic_left {a b c} h := by
    dsimp
    -- ⊢ b ≤ c ∧ c ≤ a ∨ c ≤ a ∧ a ≤ b ∨ a ≤ b ∧ b ≤ c
    rwa [← or_assoc, or_comm]
    -- 🎉 no goals
  sbtw_trans_left {a b c d} := by
    rintro (⟨hab, hbc⟩ | ⟨hbc, hca⟩ | ⟨hca, hab⟩) (⟨hbd, hdc⟩ | ⟨hdc, hcb⟩ | ⟨hcb, hbd⟩)
    · exact Or.inl ⟨hab.trans hbd, hdc⟩
      -- 🎉 no goals
    · exact (hbc.not_lt hcb).elim
      -- 🎉 no goals
    · exact (hbc.not_lt hcb).elim
      -- 🎉 no goals
    · exact Or.inr (Or.inl ⟨hdc, hca⟩)
      -- 🎉 no goals
    · exact Or.inr (Or.inl ⟨hdc, hca⟩)
      -- 🎉 no goals
    · exact (hbc.not_lt hcb).elim
    -- ⊢ (a ≤ b ∧ ¬b ≤ a) ∧ b ≤ c ∧ ¬c ≤ b ∨ (b ≤ c ∧ ¬c ≤ b) ∧ c ≤ a ∧ ¬a ≤ c ∨ (c ≤ …
      -- 🎉 no goals
    -- ⊢ (a ≤ b ∧ ¬b ≤ a) ∧ b ≤ c ∧ ¬c ≤ b ∨ (b ≤ c ∧ ¬c ≤ b) ∧ c ≤ a ∧ ¬a ≤ c ∨ (c ≤ …
    · exact Or.inr (Or.inl ⟨hdc, hca⟩)
    -- ⊢ (a ≤ b ∧ ¬b ≤ a) ∧ b ≤ c ∧ ¬c ≤ b ∨ (b ≤ c ∧ ¬c ≤ b) ∧ c ≤ a ∧ ¬a ≤ c ∨ (c ≤ …
      -- 🎉 no goals
    -- ⊢ (a ≤ b ∧ ¬b ≤ a) ∧ b ≤ c ∧ ¬c ≤ b ∨ (b ≤ c ∧ ¬c ≤ b) ∧ c ≤ a ∧ ¬a ≤ c ∨ (c ≤ …
    · exact Or.inr (Or.inl ⟨hdc, hca⟩)
      -- 🎉 no goals
    -- ⊢ (a ≤ b → b ≤ c → a ≤ c) → (b ≤ c → c ≤ a → b ≤ a) → (c ≤ a → a ≤ b → c ≤ b)  …
    · exact Or.inr (Or.inr ⟨hca, hab.trans hbd⟩)
    -- ⊢ (p1 → b ≤ c → a ≤ c) → (b ≤ c → c ≤ a → b ≤ a) → (c ≤ a → p1 → c ≤ b) → ((p1 …
      -- 🎉 no goals
    -- ⊢ (p1 → b ≤ c → a ≤ c) → (b ≤ c → c ≤ a → p2) → (c ≤ a → p1 → c ≤ b) → ((p1 ∧  …
  sbtw_iff_btw_not_btw {a b c} := by
    -- ⊢ (p1 → b ≤ c → p3) → (b ≤ c → c ≤ a → p2) → (c ≤ a → p1 → c ≤ b) → ((p1 ∧ ¬p2 …
    simp_rw [lt_iff_le_not_le]
    -- ⊢ (p1 → b ≤ c → p3) → (b ≤ c → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ b  …
    have h1 := le_trans a b c
    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
    have h2 := le_trans b c a
    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                                    -- ⊢ (p1 → p5 → p3) → (p5 → p4 → p2) → (p4 → p1 → c ≤ b) → ((p1 ∧ ¬p2) ∧ p5 ∧ ¬c  …
                                                                                    -- 🎉 no goals
                                                                                    -- 🎉 no goals
                                                                                    -- 🎉 no goals
                                                                                    -- 🎉 no goals
                                                                                    -- 🎉 no goals
                                                                                    -- 🎉 no goals
                                                                                    -- 🎉 no goals
                                                                                    -- 🎉 no goals
                                                                                    -- 🎉 no goals
                                                                                    -- 🎉 no goals
                                                                                    -- 🎉 no goals
                                                                                    -- 🎉 no goals
                                                                                    -- 🎉 no goals
                                                                                    -- 🎉 no goals
                                                                                    -- 🎉 no goals
                                                                                    -- 🎉 no goals
                                                                                    -- 🎉 no goals
                                                                                    -- 🎉 no goals
                                                                                    -- 🎉 no goals
                                                                                    -- 🎉 no goals
                                                                                    -- 🎉 no goals
                                                                                    -- 🎉 no goals
                                                                                    -- 🎉 no goals
                                                                                    -- 🎉 no goals
                                                                                    -- 🎉 no goals
                                                                                    -- 🎉 no goals
                                                                                    -- 🎉 no goals
                                                                                    -- 🎉 no goals
                                                                                    -- 🎉 no goals
                                                                                    -- 🎉 no goals
                                                                                    -- 🎉 no goals
                                                                                    -- 🎉 no goals
    have h3 := le_trans c a b
    -- Porting note: was `tauto`, but this is a much faster tactic proof
    revert h1 h2 h3
    generalize (a ≤ b) = p1
    generalize (b ≤ a) = p2
    generalize (a ≤ c) = p3
    generalize (c ≤ a) = p4
    generalize (b ≤ c) = p5
    by_cases p1 <;> by_cases p2 <;> by_cases p3 <;> by_cases p4 <;> by_cases p5 <;> simp [*]
#align preorder.to_circular_preorder Preorder.toCircularPreorder

/-- The circular partial order obtained from "looping around" a partial order.
See note [reducible non-instances]. -/
@[reducible]
def PartialOrder.toCircularPartialOrder (α : Type*) [PartialOrder α] : CircularPartialOrder α :=
  { Preorder.toCircularPreorder α with
    btw_antisymm := fun {a b c} => by
      rintro (⟨hab, hbc⟩ | ⟨hbc, hca⟩ | ⟨hca, hab⟩) (⟨hcb, hba⟩ | ⟨hba, hac⟩ | ⟨hac, hcb⟩)
      · exact Or.inl (hab.antisymm hba)
        -- 🎉 no goals
      · exact Or.inl (hab.antisymm hba)
        -- 🎉 no goals
      · exact Or.inr (Or.inl <| hbc.antisymm hcb)
        -- 🎉 no goals
      · exact Or.inr (Or.inl <| hbc.antisymm hcb)
        -- 🎉 no goals
      · exact Or.inr (Or.inr <| hca.antisymm hac)
        -- 🎉 no goals
      · exact Or.inr (Or.inl <| hbc.antisymm hcb)
        -- 🎉 no goals
      · exact Or.inl (hab.antisymm hba)
        -- 🎉 no goals
      · exact Or.inl (hab.antisymm hba)
        -- 🎉 no goals
      · exact Or.inr (Or.inr <| hca.antisymm hac) }
        -- 🎉 no goals
#align partial_order.to_circular_partial_order PartialOrder.toCircularPartialOrder

/-- The circular order obtained from "looping around" a linear order.
See note [reducible non-instances]. -/
@[reducible]
def LinearOrder.toCircularOrder (α : Type*) [LinearOrder α] : CircularOrder α :=
  { PartialOrder.toCircularPartialOrder α with
    btw_total := fun a b c => by
      cases' le_total a b with hab hba <;> cases' le_total b c with hbc hcb <;>
      -- ⊢ btw a b c ∨ btw c b a
                                           -- ⊢ btw a b c ∨ btw c b a
                                           -- ⊢ btw a b c ∨ btw c b a
        cases' le_total c a with hca hac
        -- ⊢ btw a b c ∨ btw c b a
        -- ⊢ btw a b c ∨ btw c b a
        -- ⊢ btw a b c ∨ btw c b a
        -- ⊢ btw a b c ∨ btw c b a
      · exact Or.inl (Or.inl ⟨hab, hbc⟩)
        -- 🎉 no goals
      · exact Or.inl (Or.inl ⟨hab, hbc⟩)
        -- 🎉 no goals
      · exact Or.inl (Or.inr <| Or.inr ⟨hca, hab⟩)
        -- 🎉 no goals
      · exact Or.inr (Or.inr <| Or.inr ⟨hac, hcb⟩)
        -- 🎉 no goals
      · exact Or.inl (Or.inr <| Or.inl ⟨hbc, hca⟩)
        -- 🎉 no goals
      · exact Or.inr (Or.inr <| Or.inl ⟨hba, hac⟩)
        -- 🎉 no goals
      · exact Or.inr (Or.inl ⟨hcb, hba⟩)
        -- 🎉 no goals
      · exact Or.inr (Or.inr <| Or.inl ⟨hba, hac⟩) }
        -- 🎉 no goals
#align linear_order.to_circular_order LinearOrder.toCircularOrder

/-! ### Dual constructions -/


namespace OrderDual

instance btw (α : Type*) [Btw α] : Btw αᵒᵈ :=
  ⟨fun a b c : α => Btw.btw c b a⟩

instance sbtw (α : Type*) [SBtw α] : SBtw αᵒᵈ :=
  ⟨fun a b c : α => SBtw.sbtw c b a⟩

instance circularPreorder (α : Type*) [CircularPreorder α] : CircularPreorder αᵒᵈ :=
  { OrderDual.btw α,
    OrderDual.sbtw α with
    btw_refl := fun _ => @btw_refl α _ _
    btw_cyclic_left := fun {_ _ _} => @btw_cyclic_right α _ _ _ _
    sbtw_trans_left := fun {_ _ _ _} habc hbdc => hbdc.trans_right habc
    sbtw_iff_btw_not_btw := fun {a b c} => @sbtw_iff_btw_not_btw α _ c b a }

instance circularPartialOrder (α : Type*) [CircularPartialOrder α] : CircularPartialOrder αᵒᵈ :=
  { OrderDual.circularPreorder α with
    btw_antisymm := fun {_ _ _} habc hcba => @btw_antisymm α _ _ _ _ hcba habc }

instance (α : Type*) [CircularOrder α] : CircularOrder αᵒᵈ :=
  { OrderDual.circularPartialOrder α with
    btw_total := fun {a b c} => @btw_total α _ c b a }

end OrderDual
