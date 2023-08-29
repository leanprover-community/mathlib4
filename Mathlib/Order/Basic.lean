/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Data.Prod.Basic
import Mathlib.Data.Subtype

#align_import order.basic from "leanprover-community/mathlib"@"90df25ded755a2cf9651ea850d1abe429b1e4eb1"

/-!
# Basic definitions about `≤` and `<`

This file proves basic results about orders, provides extensive dot notation, defines useful order
classes and allows to transfer order instances.

## Type synonyms

* `OrderDual α` : A type synonym reversing the meaning of all inequalities, with notation `αᵒᵈ`.
* `AsLinearOrder α`: A type synonym to promote `PartialOrder α` to `LinearOrder α` using
  `IsTotal α (≤)`.

### Transferring orders

- `Order.Preimage`, `Preorder.lift`: Transfers a (pre)order on `β` to an order on `α`
  using a function `f : α → β`.
- `PartialOrder.lift`, `LinearOrder.lift`: Transfers a partial (resp., linear) order on `β` to a
  partial (resp., linear) order on `α` using an injective function `f`.

### Extra class

* `Sup`: type class for the `⊔` notation
* `Inf`: type class for the `⊓` notation
* `HasCompl`: type class for the `ᶜ` notation
* `DenselyOrdered`: An order with no gap, i.e. for any two elements `a < b` there exists `c` such
  that `a < c < b`.

## Notes

`≤` and `<` are highly favored over `≥` and `>` in mathlib. The reason is that we can formulate all
lemmas using `≤`/`<`, and `rw` has trouble unifying `≤` and `≥`. Hence choosing one direction spares
us useless duplication. This is enforced by a linter. See Note [nolint_ge] for more infos.

Dot notation is particularly useful on `≤` (`LE.le`) and `<` (`LT.lt`). To that end, we
provide many aliases to dot notation-less lemmas. For example, `le_trans` is aliased with
`LE.le.trans` and can be used to construct `hab.trans hbc : a ≤ c` when `hab : a ≤ b`,
`hbc : b ≤ c`, `lt_of_le_of_lt` is aliased as `LE.le.trans_lt` and can be used to construct
`hab.trans hbc : a < c` when `hab : a ≤ b`, `hbc : b < c`.

## TODO

- expand module docs
- automatic construction of dual definitions / theorems

## Tags

preorder, order, partial order, poset, linear order, chain
-/


open Function

universe u v w

variable {ι : Type*} {α : Type u} {β : Type v} {γ : Type w} {π : ι → Type*} {r : α → α → Prop}

section Preorder

variable [Preorder α] {a b c : α}

theorem le_trans' : b ≤ c → a ≤ b → a ≤ c :=
  flip le_trans
#align le_trans' le_trans'

theorem lt_trans' : b < c → a < b → a < c :=
  flip lt_trans
#align lt_trans' lt_trans'

theorem lt_of_le_of_lt' : b ≤ c → a < b → a < c :=
  flip lt_of_lt_of_le
#align lt_of_le_of_lt' lt_of_le_of_lt'

theorem lt_of_lt_of_le' : b < c → a ≤ b → a < c :=
  flip lt_of_le_of_lt
#align lt_of_lt_of_le' lt_of_lt_of_le'

end Preorder

section PartialOrder

variable [PartialOrder α] {a b : α}

theorem ge_antisymm : a ≤ b → b ≤ a → b = a :=
  flip le_antisymm
#align ge_antisymm ge_antisymm

theorem lt_of_le_of_ne' : a ≤ b → b ≠ a → a < b := fun h₁ h₂ ↦ lt_of_le_of_ne h₁ h₂.symm
#align lt_of_le_of_ne' lt_of_le_of_ne'

theorem Ne.lt_of_le : a ≠ b → a ≤ b → a < b :=
  flip lt_of_le_of_ne
#align ne.lt_of_le Ne.lt_of_le

theorem Ne.lt_of_le' : b ≠ a → a ≤ b → a < b :=
  flip lt_of_le_of_ne'
#align ne.lt_of_le' Ne.lt_of_le'

end PartialOrder

attribute [simp] le_refl

attribute [ext] LE

alias LE.le.trans := le_trans

alias LE.le.trans' := le_trans'

alias LE.le.trans_lt := lt_of_le_of_lt

alias LE.le.trans_lt' := lt_of_le_of_lt'

alias LE.le.antisymm := le_antisymm

alias LE.le.antisymm' := ge_antisymm

alias LE.le.lt_of_ne := lt_of_le_of_ne

alias LE.le.lt_of_ne' := lt_of_le_of_ne'

alias LE.le.lt_of_not_le := lt_of_le_not_le

alias LE.le.lt_or_eq := lt_or_eq_of_le

alias LE.le.lt_or_eq_dec := Decidable.lt_or_eq_of_le

alias LT.lt.le := le_of_lt

alias LT.lt.trans := lt_trans

alias LT.lt.trans' := lt_trans'

alias LT.lt.trans_le := lt_of_lt_of_le

alias LT.lt.trans_le' := lt_of_lt_of_le'

alias LT.lt.ne := ne_of_lt
#align has_lt.lt.ne LT.lt.ne

alias LT.lt.asymm := lt_asymm

alias LT.lt.not_lt := lt_asymm

alias Eq.le := le_of_eq
#align eq.le Eq.le

-- Porting note: no `decidable_classical` linter
-- attribute [nolint decidable_classical] LE.le.lt_or_eq_dec

section

variable [Preorder α] {a b c : α}

/-- A version of `le_refl` where the argument is implicit -/
theorem le_rfl : a ≤ a :=
  le_refl a
#align le_rfl le_rfl

@[simp]
theorem lt_self_iff_false (x : α) : x < x ↔ False :=
  ⟨lt_irrefl x, False.elim⟩
#align lt_self_iff_false lt_self_iff_false

theorem le_of_le_of_eq (hab : a ≤ b) (hbc : b = c) : a ≤ c :=
  hab.trans hbc.le
#align le_of_le_of_eq le_of_le_of_eq

theorem le_of_eq_of_le (hab : a = b) (hbc : b ≤ c) : a ≤ c :=
  hab.le.trans hbc
#align le_of_eq_of_le le_of_eq_of_le

theorem lt_of_lt_of_eq (hab : a < b) (hbc : b = c) : a < c :=
  hab.trans_le hbc.le
#align lt_of_lt_of_eq lt_of_lt_of_eq

theorem lt_of_eq_of_lt (hab : a = b) (hbc : b < c) : a < c :=
  hab.le.trans_lt hbc
#align lt_of_eq_of_lt lt_of_eq_of_lt

theorem le_of_le_of_eq' : b ≤ c → a = b → a ≤ c :=
  flip le_of_eq_of_le
#align le_of_le_of_eq' le_of_le_of_eq'

theorem le_of_eq_of_le' : b = c → a ≤ b → a ≤ c :=
  flip le_of_le_of_eq
#align le_of_eq_of_le' le_of_eq_of_le'

theorem lt_of_lt_of_eq' : b < c → a = b → a < c :=
  flip lt_of_eq_of_lt
#align lt_of_lt_of_eq' lt_of_lt_of_eq'

theorem lt_of_eq_of_lt' : b = c → a < b → a < c :=
  flip lt_of_lt_of_eq
#align lt_of_eq_of_lt' lt_of_eq_of_lt'

alias LE.le.trans_eq := le_of_le_of_eq

alias LE.le.trans_eq' := le_of_le_of_eq'

alias LT.lt.trans_eq := lt_of_lt_of_eq

alias LT.lt.trans_eq' := lt_of_lt_of_eq'

alias Eq.trans_le := le_of_eq_of_le
#align eq.trans_le Eq.trans_le

alias Eq.trans_ge := le_of_eq_of_le'
#align eq.trans_ge Eq.trans_ge

alias Eq.trans_lt := lt_of_eq_of_lt
#align eq.trans_lt Eq.trans_lt

alias Eq.trans_gt := lt_of_eq_of_lt'
#align eq.trans_gt Eq.trans_gt

end

namespace Eq

variable [Preorder α] {x y z : α}

/-- If `x = y` then `y ≤ x`. Note: this lemma uses `y ≤ x` instead of `x ≥ y`, because `le` is used
almost exclusively in mathlib. -/
protected theorem ge (h : x = y) : y ≤ x :=
  h.symm.le
#align eq.ge Eq.ge

theorem not_lt (h : x = y) : ¬x < y := fun h' ↦ h'.ne h
#align eq.not_lt Eq.not_lt

theorem not_gt (h : x = y) : ¬y < x :=
  h.symm.not_lt
#align eq.not_gt Eq.not_gt

end Eq


section

variable [Preorder α] {a b : α}

@[simp] lemma le_of_subsingleton [Subsingleton α] : a ≤ b := (Subsingleton.elim a b).le

-- Making this a @[simp] lemma causes confluences problems downstream.
lemma not_lt_of_subsingleton [Subsingleton α] : ¬a < b := (Subsingleton.elim a b).not_lt

end

namespace LE.le

-- see Note [nolint_ge]
-- Porting note: linter not found @[nolint ge_or_gt]
protected theorem ge [LE α] {x y : α} (h : x ≤ y) : y ≥ x :=
  h
#align has_le.le.ge LE.le.ge

section PartialOrder

variable [PartialOrder α] {a b : α}

theorem lt_iff_ne (h : a ≤ b) : a < b ↔ a ≠ b :=
  ⟨fun h ↦ h.ne, h.lt_of_ne⟩
#align has_le.le.lt_iff_ne LE.le.lt_iff_ne

theorem gt_iff_ne (h : a ≤ b) : a < b ↔ b ≠ a :=
  ⟨fun h ↦ h.ne.symm, h.lt_of_ne'⟩
#align has_le.le.gt_iff_ne LE.le.gt_iff_ne

theorem not_lt_iff_eq (h : a ≤ b) : ¬a < b ↔ a = b :=
  h.lt_iff_ne.not_left
#align has_le.le.not_lt_iff_eq LE.le.not_lt_iff_eq

theorem not_gt_iff_eq (h : a ≤ b) : ¬a < b ↔ b = a :=
  h.gt_iff_ne.not_left
#align has_le.le.not_gt_iff_eq LE.le.not_gt_iff_eq

theorem le_iff_eq (h : a ≤ b) : b ≤ a ↔ b = a :=
  ⟨fun h' ↦ h'.antisymm h, Eq.le⟩
#align has_le.le.le_iff_eq LE.le.le_iff_eq

theorem ge_iff_eq (h : a ≤ b) : b ≤ a ↔ a = b :=
  ⟨h.antisymm, Eq.ge⟩
#align has_le.le.ge_iff_eq LE.le.ge_iff_eq

end PartialOrder

theorem lt_or_le [LinearOrder α] {a b : α} (h : a ≤ b) (c : α) : a < c ∨ c ≤ b :=
  ((lt_or_ge a c).imp id) fun hc ↦ le_trans hc h
#align has_le.le.lt_or_le LE.le.lt_or_le

theorem le_or_lt [LinearOrder α] {a b : α} (h : a ≤ b) (c : α) : a ≤ c ∨ c < b :=
  ((le_or_gt a c).imp id) fun hc ↦ lt_of_lt_of_le hc h
#align has_le.le.le_or_lt LE.le.le_or_lt

theorem le_or_le [LinearOrder α] {a b : α} (h : a ≤ b) (c : α) : a ≤ c ∨ c ≤ b :=
  (h.le_or_lt c).elim Or.inl fun h ↦ Or.inr <| le_of_lt h
#align has_le.le.le_or_le LE.le.le_or_le

end LE.le

namespace LT.lt

-- see Note [nolint_ge]
-- Porting note: linter not found @[nolint ge_or_gt]
protected theorem gt [LT α] {x y : α} (h : x < y) : y > x :=
  h
#align has_lt.lt.gt LT.lt.gt

protected theorem false [Preorder α] {x : α} : x < x → False :=
  lt_irrefl x
#align has_lt.lt.false LT.lt.false

theorem ne' [Preorder α] {x y : α} (h : x < y) : y ≠ x :=
  h.ne.symm
#align has_lt.lt.ne' LT.lt.ne'

theorem lt_or_lt [LinearOrder α] {x y : α} (h : x < y) (z : α) : x < z ∨ z < y :=
  (lt_or_ge z y).elim Or.inr fun hz ↦ Or.inl <| h.trans_le hz
#align has_lt.lt.lt_or_lt LT.lt.lt_or_lt

end LT.lt

-- see Note [nolint_ge]
-- Porting note: linter not found @[nolint ge_or_gt]
protected theorem GE.ge.le [LE α] {x y : α} (h : x ≥ y) : y ≤ x :=
  h
#align ge.le GE.ge.le

-- see Note [nolint_ge]
-- Porting note: linter not found @[nolint ge_or_gt]
protected theorem GT.gt.lt [LT α] {x y : α} (h : x > y) : y < x :=
  h
#align gt.lt GT.gt.lt

-- see Note [nolint_ge]
-- Porting note: linter not found @[nolint ge_or_gt]
theorem ge_of_eq [Preorder α] {a b : α} (h : a = b) : a ≥ b :=
  h.ge
#align ge_of_eq ge_of_eq

-- see Note [nolint_ge]
-- Porting note: linter not found @[nolint ge_or_gt]
@[simp]
theorem ge_iff_le [LE α] {a b : α} : a ≥ b ↔ b ≤ a :=
  Iff.rfl
#align ge_iff_le ge_iff_le

-- see Note [nolint_ge]
-- Porting note: linter not found @[nolint ge_or_gt]
@[simp]
theorem gt_iff_lt [LT α] {a b : α} : a > b ↔ b < a :=
  Iff.rfl
#align gt_iff_lt gt_iff_lt

theorem not_le_of_lt [Preorder α] {a b : α} (h : a < b) : ¬b ≤ a :=
  (le_not_le_of_lt h).right
#align not_le_of_lt not_le_of_lt

alias LT.lt.not_le := not_le_of_lt

theorem not_lt_of_le [Preorder α] {a b : α} (h : a ≤ b) : ¬b < a := fun hba ↦ hba.not_le h
#align not_lt_of_le not_lt_of_le

alias LE.le.not_lt := not_lt_of_le

theorem ne_of_not_le [Preorder α] {a b : α} (h : ¬a ≤ b) : a ≠ b := fun hab ↦ h (le_of_eq hab)
#align ne_of_not_le ne_of_not_le

-- See Note [decidable namespace]
protected theorem Decidable.le_iff_eq_or_lt [PartialOrder α] [@DecidableRel α (· ≤ ·)] {a b : α} :
    a ≤ b ↔ a = b ∨ a < b :=
  Decidable.le_iff_lt_or_eq.trans or_comm
#align decidable.le_iff_eq_or_lt Decidable.le_iff_eq_or_lt

theorem le_iff_eq_or_lt [PartialOrder α] {a b : α} : a ≤ b ↔ a = b ∨ a < b :=
  le_iff_lt_or_eq.trans or_comm
#align le_iff_eq_or_lt le_iff_eq_or_lt

theorem lt_iff_le_and_ne [PartialOrder α] {a b : α} : a < b ↔ a ≤ b ∧ a ≠ b :=
  ⟨fun h ↦ ⟨le_of_lt h, ne_of_lt h⟩, fun ⟨h1, h2⟩ ↦ h1.lt_of_ne h2⟩
#align lt_iff_le_and_ne lt_iff_le_and_ne

theorem eq_iff_not_lt_of_le {α} [PartialOrder α] {x y : α} : x ≤ y → y = x ↔ ¬x < y := by
  rw [lt_iff_le_and_ne, not_and, Classical.not_not, eq_comm]
  -- 🎉 no goals
#align eq_iff_not_lt_of_le eq_iff_not_lt_of_le

-- See Note [decidable namespace]
protected theorem Decidable.eq_iff_le_not_lt [PartialOrder α] [@DecidableRel α (· ≤ ·)] {a b : α} :
    a = b ↔ a ≤ b ∧ ¬a < b :=
  ⟨fun h ↦ ⟨h.le, h ▸ lt_irrefl _⟩, fun ⟨h₁, h₂⟩ ↦
    h₁.antisymm <| Decidable.by_contradiction fun h₃ ↦ h₂ (h₁.lt_of_not_le h₃)⟩
#align decidable.eq_iff_le_not_lt Decidable.eq_iff_le_not_lt

theorem eq_iff_le_not_lt [PartialOrder α] {a b : α} : a = b ↔ a ≤ b ∧ ¬a < b :=
  haveI := Classical.dec
  Decidable.eq_iff_le_not_lt
#align eq_iff_le_not_lt eq_iff_le_not_lt

theorem eq_or_lt_of_le [PartialOrder α] {a b : α} (h : a ≤ b) : a = b ∨ a < b :=
  h.lt_or_eq.symm
#align eq_or_lt_of_le eq_or_lt_of_le

theorem eq_or_gt_of_le [PartialOrder α] {a b : α} (h : a ≤ b) : b = a ∨ a < b :=
  h.lt_or_eq.symm.imp Eq.symm id
#align eq_or_gt_of_le eq_or_gt_of_le

theorem gt_or_eq_of_le [PartialOrder α] {a b : α} (h : a ≤ b) : a < b ∨ b = a :=
  (eq_or_gt_of_le h).symm
#align gt_or_eq_of_le gt_or_eq_of_le

alias LE.le.eq_or_lt_dec := Decidable.eq_or_lt_of_le

alias LE.le.eq_or_lt := eq_or_lt_of_le

alias LE.le.eq_or_gt := eq_or_gt_of_le

alias LE.le.gt_or_eq := gt_or_eq_of_le

-- Porting note: no `decidable_classical` linter
-- attribute [nolint decidable_classical] LE.le.eq_or_lt_dec

theorem eq_of_le_of_not_lt [PartialOrder α] {a b : α} (hab : a ≤ b) (hba : ¬a < b) : a = b :=
  hab.eq_or_lt.resolve_right hba
#align eq_of_le_of_not_lt eq_of_le_of_not_lt

theorem eq_of_ge_of_not_gt [PartialOrder α] {a b : α} (hab : a ≤ b) (hba : ¬a < b) : b = a :=
  (hab.eq_or_lt.resolve_right hba).symm
#align eq_of_ge_of_not_gt eq_of_ge_of_not_gt

alias LE.le.eq_of_not_lt := eq_of_le_of_not_lt

alias LE.le.eq_of_not_gt := eq_of_ge_of_not_gt

theorem Ne.le_iff_lt [PartialOrder α] {a b : α} (h : a ≠ b) : a ≤ b ↔ a < b :=
  ⟨fun h' ↦ lt_of_le_of_ne h' h, fun h ↦ h.le⟩
#align ne.le_iff_lt Ne.le_iff_lt

theorem Ne.not_le_or_not_le [PartialOrder α] {a b : α} (h : a ≠ b) : ¬a ≤ b ∨ ¬b ≤ a :=
  not_and_or.1 <| le_antisymm_iff.not.1 h
#align ne.not_le_or_not_le Ne.not_le_or_not_le

-- See Note [decidable namespace]
protected theorem Decidable.ne_iff_lt_iff_le [PartialOrder α] [DecidableEq α] {a b : α} :
    (a ≠ b ↔ a < b) ↔ a ≤ b :=
  ⟨fun h ↦ Decidable.byCases le_of_eq (le_of_lt ∘ h.mp), fun h ↦ ⟨lt_of_le_of_ne h, ne_of_lt⟩⟩
#align decidable.ne_iff_lt_iff_le Decidable.ne_iff_lt_iff_le

@[simp]
theorem ne_iff_lt_iff_le [PartialOrder α] {a b : α} : (a ≠ b ↔ a < b) ↔ a ≤ b :=
  haveI := Classical.dec
  Decidable.ne_iff_lt_iff_le
#align ne_iff_lt_iff_le ne_iff_lt_iff_le

-- Variant of `min_def` with the branches reversed.
theorem min_def' [LinearOrder α] (a b : α) : min a b = if b ≤ a then b else a := by
  rw [min_def]
  -- ⊢ (if a ≤ b then a else b) = if b ≤ a then b else a
  rcases lt_trichotomy a b with (lt | eq | gt)
  · rw [if_pos lt.le, if_neg (not_le.mpr lt)]
    -- 🎉 no goals
  · rw [if_pos eq.le, if_pos eq.ge, eq]
    -- 🎉 no goals
  · rw [if_neg (not_le.mpr gt.gt), if_pos gt.le]
    -- 🎉 no goals
#align min_def' min_def'

-- Variant of `min_def` with the branches reversed.
-- This is sometimes useful as it used to be the default.
theorem max_def' [LinearOrder α] (a b : α) : max a b = if b ≤ a then a else b := by
  rw [max_def]
  -- ⊢ (if a ≤ b then b else a) = if b ≤ a then a else b
  rcases lt_trichotomy a b with (lt | eq | gt)
  · rw [if_pos lt.le, if_neg (not_le.mpr lt)]
    -- 🎉 no goals
  · rw [if_pos eq.le, if_pos eq.ge, eq]
    -- 🎉 no goals
  · rw [if_neg (not_le.mpr gt.gt), if_pos gt.le]
    -- 🎉 no goals
#align max_def' max_def'

theorem lt_of_not_le [LinearOrder α] {a b : α} (h : ¬b ≤ a) : a < b :=
  ((le_total _ _).resolve_right h).lt_of_not_le h
#align lt_of_not_le lt_of_not_le

theorem lt_iff_not_le [LinearOrder α] {x y : α} : x < y ↔ ¬y ≤ x :=
  ⟨not_le_of_lt, lt_of_not_le⟩
#align lt_iff_not_le lt_iff_not_le

theorem Ne.lt_or_lt [LinearOrder α] {x y : α} (h : x ≠ y) : x < y ∨ y < x :=
  lt_or_gt_of_ne h
#align ne.lt_or_lt Ne.lt_or_lt

/-- A version of `ne_iff_lt_or_gt` with LHS and RHS reversed. -/
@[simp]
theorem lt_or_lt_iff_ne [LinearOrder α] {x y : α} : x < y ∨ y < x ↔ x ≠ y :=
  ne_iff_lt_or_gt.symm
#align lt_or_lt_iff_ne lt_or_lt_iff_ne

theorem not_lt_iff_eq_or_lt [LinearOrder α] {a b : α} : ¬a < b ↔ a = b ∨ b < a :=
  not_lt.trans <| Decidable.le_iff_eq_or_lt.trans <| or_congr eq_comm Iff.rfl
#align not_lt_iff_eq_or_lt not_lt_iff_eq_or_lt

theorem exists_ge_of_linear [LinearOrder α] (a b : α) : ∃ c, a ≤ c ∧ b ≤ c :=
  match le_total a b with
  | Or.inl h => ⟨_, h, le_rfl⟩
  | Or.inr h => ⟨_, le_rfl, h⟩
#align exists_ge_of_linear exists_ge_of_linear

theorem lt_imp_lt_of_le_imp_le {β} [LinearOrder α] [Preorder β] {a b : α} {c d : β}
    (H : a ≤ b → c ≤ d) (h : d < c) : b < a :=
  lt_of_not_le fun h' ↦ (H h').not_lt h
#align lt_imp_lt_of_le_imp_le lt_imp_lt_of_le_imp_le

theorem le_imp_le_iff_lt_imp_lt {β} [LinearOrder α] [LinearOrder β] {a b : α} {c d : β} :
    a ≤ b → c ≤ d ↔ d < c → b < a :=
  ⟨lt_imp_lt_of_le_imp_le, le_imp_le_of_lt_imp_lt⟩
#align le_imp_le_iff_lt_imp_lt le_imp_le_iff_lt_imp_lt

theorem lt_iff_lt_of_le_iff_le' {β} [Preorder α] [Preorder β] {a b : α} {c d : β}
    (H : a ≤ b ↔ c ≤ d) (H' : b ≤ a ↔ d ≤ c) : b < a ↔ d < c :=
  lt_iff_le_not_le.trans <| (and_congr H' (not_congr H)).trans lt_iff_le_not_le.symm
#align lt_iff_lt_of_le_iff_le' lt_iff_lt_of_le_iff_le'

theorem lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [LinearOrder β] {a b : α} {c d : β}
    (H : a ≤ b ↔ c ≤ d) : b < a ↔ d < c :=
  not_le.symm.trans <| (not_congr H).trans <| not_le
#align lt_iff_lt_of_le_iff_le lt_iff_lt_of_le_iff_le

theorem le_iff_le_iff_lt_iff_lt {β} [LinearOrder α] [LinearOrder β] {a b : α} {c d : β} :
    (a ≤ b ↔ c ≤ d) ↔ (b < a ↔ d < c) :=
  ⟨lt_iff_lt_of_le_iff_le, fun H ↦ not_lt.symm.trans <| (not_congr H).trans <| not_lt⟩
#align le_iff_le_iff_lt_iff_lt le_iff_le_iff_lt_iff_lt

theorem eq_of_forall_le_iff [PartialOrder α] {a b : α} (H : ∀ c, c ≤ a ↔ c ≤ b) : a = b :=
  ((H _).1 le_rfl).antisymm ((H _).2 le_rfl)
#align eq_of_forall_le_iff eq_of_forall_le_iff

theorem le_of_forall_le [Preorder α] {a b : α} (H : ∀ c, c ≤ a → c ≤ b) : a ≤ b :=
  H _ le_rfl
#align le_of_forall_le le_of_forall_le

theorem le_of_forall_le' [Preorder α] {a b : α} (H : ∀ c, a ≤ c → b ≤ c) : b ≤ a :=
  H _ le_rfl
#align le_of_forall_le' le_of_forall_le'

theorem le_of_forall_lt [LinearOrder α] {a b : α} (H : ∀ c, c < a → c < b) : a ≤ b :=
  le_of_not_lt fun h ↦ lt_irrefl _ (H _ h)
#align le_of_forall_lt le_of_forall_lt

theorem forall_lt_iff_le [LinearOrder α] {a b : α} : (∀ ⦃c⦄, c < a → c < b) ↔ a ≤ b :=
  ⟨le_of_forall_lt, fun h _ hca ↦ lt_of_lt_of_le hca h⟩
#align forall_lt_iff_le forall_lt_iff_le

theorem le_of_forall_lt' [LinearOrder α] {a b : α} (H : ∀ c, a < c → b < c) : b ≤ a :=
  le_of_not_lt fun h ↦ lt_irrefl _ (H _ h)
#align le_of_forall_lt' le_of_forall_lt'

theorem forall_lt_iff_le' [LinearOrder α] {a b : α} : (∀ ⦃c⦄, a < c → b < c) ↔ b ≤ a :=
  ⟨le_of_forall_lt', fun h _ hac ↦ lt_of_le_of_lt h hac⟩
#align forall_lt_iff_le' forall_lt_iff_le'

theorem eq_of_forall_ge_iff [PartialOrder α] {a b : α} (H : ∀ c, a ≤ c ↔ b ≤ c) : a = b :=
  ((H _).2 le_rfl).antisymm ((H _).1 le_rfl)
#align eq_of_forall_ge_iff eq_of_forall_ge_iff

theorem eq_of_forall_lt_iff [LinearOrder α] {a b : α} (h : ∀ c, c < a ↔ c < b) : a = b :=
  (le_of_forall_lt fun _ ↦ (h _).1).antisymm <| le_of_forall_lt fun _ ↦ (h _).2
#align eq_of_forall_lt_iff eq_of_forall_lt_iff

theorem eq_of_forall_gt_iff [LinearOrder α] {a b : α} (h : ∀ c, a < c ↔ b < c) : a = b :=
  (le_of_forall_lt' fun _ ↦ (h _).2).antisymm <| le_of_forall_lt' fun _ ↦ (h _).1
#align eq_of_forall_gt_iff eq_of_forall_gt_iff

/-- A symmetric relation implies two values are equal, when it implies they're less-equal.  -/
theorem rel_imp_eq_of_rel_imp_le [PartialOrder β] (r : α → α → Prop) [IsSymm α r] {f : α → β}
    (h : ∀ a b, r a b → f a ≤ f b) {a b : α} : r a b → f a = f b := fun hab ↦
  le_antisymm (h a b hab) (h b a <| symm hab)
#align rel_imp_eq_of_rel_imp_le rel_imp_eq_of_rel_imp_le

/-- monotonicity of `≤` with respect to `→` -/
theorem le_implies_le_of_le_of_le {a b c d : α} [Preorder α] (hca : c ≤ a) (hbd : b ≤ d) :
    a ≤ b → c ≤ d :=
  fun hab ↦ (hca.trans hab).trans hbd
#align le_implies_le_of_le_of_le le_implies_le_of_le_of_le

section PartialOrder

variable [PartialOrder α]

/-- To prove commutativity of a binary operation `○`, we only to check `a ○ b ≤ b ○ a` for all `a`,
`b`. -/
theorem commutative_of_le {f : β → β → α} (comm : ∀ a b, f a b ≤ f b a) : ∀ a b, f a b = f b a :=
  fun _ _ ↦ (comm _ _).antisymm <| comm _ _
#align commutative_of_le commutative_of_le

/-- To prove associativity of a commutative binary operation `○`, we only to check
`(a ○ b) ○ c ≤ a ○ (b ○ c)` for all `a`, `b`, `c`. -/
theorem associative_of_commutative_of_le {f : α → α → α} (comm : Commutative f)
    (assoc : ∀ a b c, f (f a b) c ≤ f a (f b c)) : Associative f := fun a b c ↦
  le_antisymm (assoc _ _ _) <| by
    rw [comm, comm b, comm _ c, comm a]
    -- ⊢ f (f c b) a ≤ f c (f b a)
    exact assoc _ _ _
    -- 🎉 no goals
#align associative_of_commutative_of_le associative_of_commutative_of_le

end PartialOrder

@[ext]
theorem Preorder.toLE_injective {α : Type*} : Function.Injective (@Preorder.toLE α) :=
  fun A B h ↦ match A, B with
  | { lt := A_lt, lt_iff_le_not_le := A_iff, .. },
    { lt := B_lt, lt_iff_le_not_le := B_iff, .. } => by
    cases h
    -- ⊢ mk le_refl✝¹ le_trans✝¹ = mk le_refl✝ le_trans✝
    have : A_lt = B_lt := by
      funext a b
      show (LT.mk A_lt).lt a b = (LT.mk B_lt).lt a b
      rw [A_iff, B_iff]
    cases this
    -- ⊢ mk le_refl✝¹ le_trans✝¹ = mk le_refl✝ le_trans✝
    congr
    -- 🎉 no goals
#align preorder.to_has_le_injective Preorder.toLE_injective

@[ext]
theorem PartialOrder.toPreorder_injective {α : Type*} :
    Function.Injective (@PartialOrder.toPreorder α) := fun A B h ↦ by
  cases A
  -- ⊢ mk le_antisymm✝ = B
  cases B
  -- ⊢ mk le_antisymm✝¹ = mk le_antisymm✝
  cases h
  -- ⊢ mk le_antisymm✝¹ = mk le_antisymm✝
  congr
  -- 🎉 no goals
#align partial_order.to_preorder_injective PartialOrder.toPreorder_injective

@[ext]
theorem LinearOrder.toPartialOrder_injective {α : Type*} :
    Function.Injective (@LinearOrder.toPartialOrder α) :=
  fun A B h ↦ match A, B with
  | { le := A_le, lt := A_lt,
      decidableLE := A_decidableLE, decidableEq := A_decidableEq, decidableLT := A_decidableLT
      min := A_min, max := A_max, min_def := A_min_def, max_def := A_max_def,
      compare := A_compare, compare_eq_compareOfLessAndEq := A_compare_canonical, .. },
    { le := B_le, lt := B_lt,
      decidableLE := B_decidableLE, decidableEq := B_decidableEq, decidableLT := B_decidableLT
      min := B_min, max := B_max, min_def := B_min_def, max_def := B_max_def,
      compare := B_compare, compare_eq_compareOfLessAndEq := B_compare_canonical, .. } => by
    cases h
    -- ⊢ mk le_total✝¹ A_decidableLE A_decidableEq A_decidableLT = mk le_total✝ B_dec …
    obtain rfl : A_decidableLE = B_decidableLE := Subsingleton.elim _ _
    -- ⊢ mk le_total✝¹ A_decidableLE A_decidableEq A_decidableLT = mk le_total✝ A_dec …
    obtain rfl : A_decidableEq = B_decidableEq := Subsingleton.elim _ _
    -- ⊢ mk le_total✝¹ A_decidableLE A_decidableEq A_decidableLT = mk le_total✝ A_dec …
    obtain rfl : A_decidableLT = B_decidableLT := Subsingleton.elim _ _
    -- ⊢ mk le_total✝¹ A_decidableLE A_decidableEq A_decidableLT = mk le_total✝ A_dec …
    have : A_min = B_min := by
      funext a b
      exact (A_min_def _ _).trans (B_min_def _ _).symm
    cases this
    -- ⊢ mk le_total✝¹ A_decidableLE A_decidableEq A_decidableLT = mk le_total✝ A_dec …
    have : A_max = B_max := by
      funext a b
      exact (A_max_def _ _).trans (B_max_def _ _).symm
    cases this
    -- ⊢ mk le_total✝¹ A_decidableLE A_decidableEq A_decidableLT = mk le_total✝ A_dec …
    have : A_compare = B_compare := by
      funext a b
      exact (A_compare_canonical _ _).trans (B_compare_canonical _ _).symm
    congr
    -- 🎉 no goals
#align linear_order.to_partial_order_injective LinearOrder.toPartialOrder_injective

theorem Preorder.ext {α} {A B : Preorder α}
    (H : ∀ x y : α, (haveI := A; x ≤ y) ↔ x ≤ y) : A = B := by
  ext x y
  -- ⊢ x ≤ y ↔ x ≤ y
  exact H x y
  -- 🎉 no goals
#align preorder.ext Preorder.ext

theorem PartialOrder.ext {α} {A B : PartialOrder α}
    (H : ∀ x y : α, (haveI := A; x ≤ y) ↔ x ≤ y) : A = B := by
  ext x y
  -- ⊢ x ≤ y ↔ x ≤ y
  exact H x y
  -- 🎉 no goals
#align partial_order.ext PartialOrder.ext

theorem LinearOrder.ext {α} {A B : LinearOrder α}
    (H : ∀ x y : α, (haveI := A; x ≤ y) ↔ x ≤ y) : A = B := by
  ext x y
  -- ⊢ x ≤ y ↔ x ≤ y
  exact H x y
  -- 🎉 no goals
#align linear_order.ext LinearOrder.ext

/-- Given a relation `R` on `β` and a function `f : α → β`, the preimage relation on `α` is defined
by `x ≤ y ↔ f x ≤ f y`. It is the unique relation on `α` making `f` a `RelEmbedding` (assuming `f`
is injective). -/
@[simp]
def Order.Preimage {α β} (f : α → β) (s : β → β → Prop) (x y : α) : Prop :=
  s (f x) (f y)
#align order.preimage Order.Preimage

@[inherit_doc]
infixl:80 " ⁻¹'o " => Order.Preimage

/-- The preimage of a decidable order is decidable. -/
instance Order.Preimage.decidable {α β} (f : α → β) (s : β → β → Prop) [H : DecidableRel s] :
    DecidableRel (f ⁻¹'o s) := fun _ _ ↦ H _ _
#align order.preimage.decidable Order.Preimage.decidable

/-! ### Order dual -/


/-- Type synonym to equip a type with the dual order: `≤` means `≥` and `<` means `>`. `αᵒᵈ` is
notation for `OrderDual α`. -/
def OrderDual (α : Type*) : Type _ :=
  α
#align order_dual OrderDual

@[inherit_doc]
notation:max α "ᵒᵈ" => OrderDual α

namespace OrderDual

instance (α : Type*) [h : Nonempty α] : Nonempty αᵒᵈ :=
  h

instance (α : Type*) [h : Subsingleton α] : Subsingleton αᵒᵈ :=
  h

instance (α : Type*) [LE α] : LE αᵒᵈ :=
  ⟨fun x y : α ↦ y ≤ x⟩

instance (α : Type*) [LT α] : LT αᵒᵈ :=
  ⟨fun x y : α ↦ y < x⟩

instance instPreorder (α : Type*) [Preorder α] : Preorder αᵒᵈ where
  le_refl := fun _ ↦ le_refl _
  le_trans := fun _ _ _ hab hbc ↦ hbc.trans hab
  lt_iff_le_not_le := fun _ _ ↦ lt_iff_le_not_le

instance instPartialOrder (α : Type*) [PartialOrder α] : PartialOrder αᵒᵈ where
  __ := inferInstanceAs (Preorder αᵒᵈ)
  le_antisymm := fun a b hab hba ↦ @le_antisymm α _ a b hba hab

instance instLinearOrder (α : Type*) [LinearOrder α] : LinearOrder αᵒᵈ where
  __ := inferInstanceAs (PartialOrder αᵒᵈ)
  le_total     := λ a b : α => le_total b a
  max := fun a b ↦ (min a b : α)
  min := fun a b ↦ (max a b : α)
  min_def := fun a b ↦ show (max .. : α) = _ by rw [max_comm, max_def]; rfl
                                                -- ⊢ (if b ≤ a then a else b) = if a ≤ b then a else b
                                                                        -- 🎉 no goals
  max_def := fun a b ↦ show (min .. : α) = _ by rw [min_comm, min_def]; rfl
                                                -- ⊢ (if b ≤ a then b else a) = if a ≤ b then b else a
                                                                        -- 🎉 no goals
  decidableLE := (inferInstance : DecidableRel (λ a b : α => b ≤ a))
  decidableLT := (inferInstance : DecidableRel (λ a b : α => b < a))
#align order_dual.linear_order OrderDual.instLinearOrder

instance : ∀ [Inhabited α], Inhabited αᵒᵈ := fun [x : Inhabited α] => x

theorem Preorder.dual_dual (α : Type*) [H : Preorder α] : OrderDual.instPreorder αᵒᵈ = H :=
  Preorder.ext fun _ _ ↦ Iff.rfl
#align order_dual.preorder.dual_dual OrderDual.Preorder.dual_dual

theorem instPartialOrder.dual_dual (α : Type*) [H : PartialOrder α] :
    OrderDual.instPartialOrder αᵒᵈ = H :=
  PartialOrder.ext fun _ _ ↦ Iff.rfl
#align order_dual.partial_order.dual_dual OrderDual.instPartialOrder.dual_dual

theorem instLinearOrder.dual_dual (α : Type*) [H : LinearOrder α] :
    OrderDual.instLinearOrder αᵒᵈ = H :=
  LinearOrder.ext fun _ _ ↦ Iff.rfl
#align order_dual.linear_order.dual_dual OrderDual.instLinearOrder.dual_dual

end OrderDual

/-! ### `HasCompl` -/


/-- Set / lattice complement -/
@[notation_class]
class HasCompl (α : Type*) where
  /-- Set / lattice complement -/
  compl : α → α
#align has_compl HasCompl

export HasCompl (compl)

@[inherit_doc]
postfix:1024 "ᶜ" => compl

instance Prop.hasCompl : HasCompl Prop :=
  ⟨Not⟩
#align Prop.has_compl Prop.hasCompl

instance Pi.hasCompl {ι : Type u} {α : ι → Type v} [∀ i, HasCompl (α i)] : HasCompl (∀ i, α i) :=
  ⟨fun x i ↦ (x i)ᶜ⟩
#align pi.has_compl Pi.hasCompl

theorem Pi.compl_def {ι : Type u} {α : ι → Type v} [∀ i, HasCompl (α i)] (x : ∀ i, α i) :
    xᶜ = fun i ↦ (x i)ᶜ :=
  rfl
#align pi.compl_def Pi.compl_def

@[simp]
theorem Pi.compl_apply {ι : Type u} {α : ι → Type v} [∀ i, HasCompl (α i)] (x : ∀ i, α i) (i : ι) :
    xᶜ i = (x i)ᶜ :=
  rfl
#align pi.compl_apply Pi.compl_apply

instance IsIrrefl.compl (r) [IsIrrefl α r] : IsRefl α rᶜ :=
  ⟨@irrefl α r _⟩
#align is_irrefl.compl IsIrrefl.compl

instance IsRefl.compl (r) [IsRefl α r] : IsIrrefl α rᶜ :=
  ⟨fun a ↦ not_not_intro (refl a)⟩
#align is_refl.compl IsRefl.compl

/-! ### Order instances on the function space -/


instance Pi.hasLe {ι : Type u} {α : ι → Type v} [∀ i, LE (α i)] :
    LE (∀ i, α i) where le x y := ∀ i, x i ≤ y i
#align pi.has_le Pi.hasLe

theorem Pi.le_def {ι : Type u} {α : ι → Type v} [∀ i, LE (α i)] {x y : ∀ i, α i} :
    x ≤ y ↔ ∀ i, x i ≤ y i :=
  Iff.rfl
#align pi.le_def Pi.le_def

instance Pi.preorder {ι : Type u} {α : ι → Type v} [∀ i, Preorder (α i)] : Preorder (∀ i, α i) where
  __ := inferInstanceAs (LE (∀ i, α i))
  le_refl := fun a i ↦ le_refl (a i)
  le_trans := fun a b c h₁ h₂ i ↦ le_trans (h₁ i) (h₂ i)
#align pi.preorder Pi.preorder

theorem Pi.lt_def {ι : Type u} {α : ι → Type v} [∀ i, Preorder (α i)] {x y : ∀ i, α i} :
    x < y ↔ x ≤ y ∧ ∃ i, x i < y i := by
  simp (config := { contextual := true }) [lt_iff_le_not_le, Pi.le_def]
  -- 🎉 no goals
#align pi.lt_def Pi.lt_def

instance Pi.partialOrder [∀ i, PartialOrder (π i)] : PartialOrder (∀ i, π i) where
  __ := Pi.preorder
  le_antisymm := fun _ _ h1 h2 ↦ funext fun b ↦ (h1 b).antisymm (h2 b)
#align pi.partial_order Pi.partialOrder

section Pi

/-- A function `a` is strongly less than a function `b` if `a i < b i` for all `i`. -/
def StrongLT [∀ i, LT (π i)] (a b : ∀ i, π i) : Prop :=
  ∀ i, a i < b i
#align strong_lt StrongLT

@[inherit_doc]
local infixl:50 " ≺ " => StrongLT

variable [∀ i, Preorder (π i)] {a b c : ∀ i, π i}

theorem le_of_strongLT (h : a ≺ b) : a ≤ b := fun _ ↦ (h _).le
#align le_of_strong_lt le_of_strongLT

theorem lt_of_strongLT [Nonempty ι] (h : a ≺ b) : a < b := by
  inhabit ι
  -- ⊢ a < b
  exact Pi.lt_def.2 ⟨le_of_strongLT h, default, h _⟩
  -- 🎉 no goals
#align lt_of_strong_lt lt_of_strongLT

theorem strongLT_of_strongLT_of_le (hab : a ≺ b) (hbc : b ≤ c) : a ≺ c := fun _ ↦
  (hab _).trans_le <| hbc _
#align strong_lt_of_strong_lt_of_le strongLT_of_strongLT_of_le

theorem strongLT_of_le_of_strongLT (hab : a ≤ b) (hbc : b ≺ c) : a ≺ c := fun _ ↦
  (hab _).trans_lt <| hbc _
#align strong_lt_of_le_of_strong_lt strongLT_of_le_of_strongLT

alias StrongLT.le := le_of_strongLT
#align strong_lt.le StrongLT.le

alias StrongLT.lt := lt_of_strongLT
#align strong_lt.lt StrongLT.lt

alias StrongLT.trans_le := strongLT_of_strongLT_of_le
#align strong_lt.trans_le StrongLT.trans_le

alias LE.le.trans_strongLT := strongLT_of_le_of_strongLT

end Pi

section Function

variable [DecidableEq ι] [∀ i, Preorder (π i)] {x y : ∀ i, π i} {i : ι} {a b : π i}

theorem le_update_iff : x ≤ Function.update y i a ↔ x i ≤ a ∧ ∀ (j) (_ : j ≠ i), x j ≤ y j :=
  Function.forall_update_iff _ fun j z ↦ x j ≤ z
#align le_update_iff le_update_iff

theorem update_le_iff : Function.update x i a ≤ y ↔ a ≤ y i ∧ ∀ (j) (_ : j ≠ i), x j ≤ y j :=
  Function.forall_update_iff _ fun j z ↦ z ≤ y j
#align update_le_iff update_le_iff

theorem update_le_update_iff :
    Function.update x i a ≤ Function.update y i b ↔ a ≤ b ∧ ∀ (j) (_ : j ≠ i), x j ≤ y j := by
  simp (config := { contextual := true }) [update_le_iff]
  -- 🎉 no goals
#align update_le_update_iff update_le_update_iff

@[simp]
theorem update_le_update_iff' : update x i a ≤ update x i b ↔ a ≤ b := by
  simp [update_le_update_iff]
  -- 🎉 no goals
#align update_le_update_iff' update_le_update_iff'

@[simp]
theorem update_lt_update_iff : update x i a < update x i b ↔ a < b :=
  lt_iff_lt_of_le_iff_le' update_le_update_iff' update_le_update_iff'
#align update_lt_update_iff update_lt_update_iff

@[simp]
theorem le_update_self_iff : x ≤ update x i a ↔ x i ≤ a := by simp [le_update_iff]
                                                              -- 🎉 no goals
#align le_update_self_iff le_update_self_iff

@[simp]
theorem update_le_self_iff : update x i a ≤ x ↔ a ≤ x i := by simp [update_le_iff]
                                                              -- 🎉 no goals
#align update_le_self_iff update_le_self_iff

@[simp]
theorem lt_update_self_iff : x < update x i a ↔ x i < a := by simp [lt_iff_le_not_le]
                                                              -- 🎉 no goals
#align lt_update_self_iff lt_update_self_iff

@[simp]
theorem update_lt_self_iff : update x i a < x ↔ a < x i := by simp [lt_iff_le_not_le]
                                                              -- 🎉 no goals
#align update_lt_self_iff update_lt_self_iff

end Function

instance Pi.sdiff {ι : Type u} {α : ι → Type v} [∀ i, SDiff (α i)] : SDiff (∀ i, α i) :=
  ⟨fun x y i ↦ x i \ y i⟩
#align pi.has_sdiff Pi.sdiff

theorem Pi.sdiff_def {ι : Type u} {α : ι → Type v} [∀ i, SDiff (α i)] (x y : ∀ i, α i) :
    x \ y = fun i ↦ x i \ y i :=
  rfl
#align pi.sdiff_def Pi.sdiff_def

@[simp]
theorem Pi.sdiff_apply {ι : Type u} {α : ι → Type v} [∀ i, SDiff (α i)] (x y : ∀ i, α i) (i : ι) :
    (x \ y) i = x i \ y i :=
  rfl
#align pi.sdiff_apply Pi.sdiff_apply

namespace Function

variable [Preorder α] [Nonempty β] {a b : α}

@[simp]
theorem const_le_const : const β a ≤ const β b ↔ a ≤ b := by simp [Pi.le_def]
                                                             -- 🎉 no goals
#align function.const_le_const Function.const_le_const

@[simp]
theorem const_lt_const : const β a < const β b ↔ a < b := by simpa [Pi.lt_def] using le_of_lt
                                                             -- 🎉 no goals
#align function.const_lt_const Function.const_lt_const

end Function

/-! ### `min`/`max` recursors -/


section MinMaxRec

variable [LinearOrder α] {p : α → Prop} {x y : α}

theorem min_rec (hx : x ≤ y → p x) (hy : y ≤ x → p y) : p (min x y) :=
  (le_total x y).rec (fun h ↦ (min_eq_left h).symm.subst (hx h)) fun h ↦
    (min_eq_right h).symm.subst (hy h)
#align min_rec min_rec

theorem max_rec (hx : y ≤ x → p x) (hy : x ≤ y → p y) : p (max x y) :=
  @min_rec αᵒᵈ _ _ _ _ hx hy
#align max_rec max_rec

theorem min_rec' (p : α → Prop) (hx : p x) (hy : p y) : p (min x y) :=
  min_rec (fun _ ↦ hx) fun _ ↦ hy
#align min_rec' min_rec'

theorem max_rec' (p : α → Prop) (hx : p x) (hy : p y) : p (max x y) :=
  max_rec (fun _ ↦ hx) fun _ ↦ hy
#align max_rec' max_rec'

theorem min_def_lt (x y : α) : min x y = if x < y then x else y := by
  rw [min_comm, min_def, ← ite_not]
  -- ⊢ (if ¬y ≤ x then x else y) = if x < y then x else y
  simp only [not_le]
  -- 🎉 no goals
#align min_def_lt min_def_lt

theorem max_def_lt (x y : α) : max x y = if x < y then y else x := by
  rw [max_comm, max_def, ← ite_not]
  -- ⊢ (if ¬y ≤ x then y else x) = if x < y then y else x
  simp only [not_le]
  -- 🎉 no goals
#align max_def_lt max_def_lt

end MinMaxRec

/-! ### `Sup` and `Inf` -/


/-- Typeclass for the `⊔` (`\lub`) notation -/
@[notation_class, ext]
class Sup (α : Type u) where
  /-- Least upper bound (`\lub` notation) -/
  sup : α → α → α
#align has_sup Sup

/-- Typeclass for the `⊓` (`\glb`) notation -/
@[notation_class, ext]
class Inf (α : Type u) where
  /-- Greatest lower bound (`\glb` notation) -/
  inf : α → α → α
#align has_inf Inf

@[inherit_doc]
infixl:68 " ⊔ " => Sup.sup

@[inherit_doc]
infixl:69 " ⊓ " => Inf.inf

/-! ### Lifts of order instances -/


/-- Transfer a `Preorder` on `β` to a `Preorder` on `α` using a function `f : α → β`.
See note [reducible non-instances]. -/
@[reducible]
def Preorder.lift {α β} [Preorder β] (f : α → β) : Preorder α where
  le x y := f x ≤ f y
  le_refl _ := le_rfl
  le_trans _ _ _ := _root_.le_trans
  lt x y := f x < f y
  lt_iff_le_not_le _ _ := _root_.lt_iff_le_not_le
#align preorder.lift Preorder.lift

/-- Transfer a `PartialOrder` on `β` to a `PartialOrder` on `α` using an injective
function `f : α → β`. See note [reducible non-instances]. -/
@[reducible]
def PartialOrder.lift {α β} [PartialOrder β] (f : α → β) (inj : Injective f) : PartialOrder α :=
  { Preorder.lift f with le_antisymm := fun _ _ h₁ h₂ ↦ inj (h₁.antisymm h₂) }
#align partial_order.lift PartialOrder.lift

theorem compare_of_injective_eq_compareOfLessAndEq (a b : α) [LinearOrder β]
    [DecidableEq α] (f : α → β) (inj : Injective f)
    [Decidable (LT.lt (self := PartialOrder.lift f inj |>.toLT) a b)] :
    compare (f a) (f b) =
      @compareOfLessAndEq _ a b (PartialOrder.lift f inj |>.toLT) _ _ := by
  have h := LinearOrder.compare_eq_compareOfLessAndEq (f a) (f b)
  -- ⊢ compare (f a) (f b) = compareOfLessAndEq a b
  simp only [h, compareOfLessAndEq]
  -- ⊢ (if f a < f b then Ordering.lt else if f a = f b then Ordering.eq else Order …
  split_ifs <;> try (first | rfl | contradiction)
                -- 🎉 no goals
                -- 🎉 no goals
                -- 🎉 no goals
                -- 🎉 no goals
                -- 🎉 no goals
                -- ⊢ False
                -- 🎉 no goals
                -- ⊢ False
                -- 🎉 no goals
  · have : ¬ f a = f b := by rename_i h; exact inj.ne h
    -- ⊢ False
    contradiction
    -- 🎉 no goals
  · have : f a = f b := by rename_i h; exact congrArg f h
    -- ⊢ False
    contradiction
    -- 🎉 no goals

/-- Transfer a `LinearOrder` on `β` to a `LinearOrder` on `α` using an injective
function `f : α → β`. This version takes `[Sup α]` and `[Inf α]` as arguments, then uses
them for `max` and `min` fields. See `LinearOrder.lift'` for a version that autogenerates `min` and
`max` fields, and `LinearOrder.liftWithOrd` for one that does not auto-generate `compare`
fields. See note [reducible non-instances]. -/
@[reducible]
def LinearOrder.lift {α β} [LinearOrder β] [Sup α] [Inf α] (f : α → β) (inj : Injective f)
    (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y)) (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
    LinearOrder α :=
  letI instOrdα : Ord α := ⟨fun a b ↦ compare (f a) (f b)⟩
  letI decidableLE := fun x y ↦ (inferInstance : Decidable (f x ≤ f y))
  letI decidableLT := fun x y ↦ (inferInstance : Decidable (f x < f y))
  letI decidableEq := fun x y ↦ decidable_of_iff (f x = f y) inj.eq_iff
  { PartialOrder.lift f inj, instOrdα with
    le_total := fun x y ↦ le_total (f x) (f y)
    decidableLE := decidableLE
    decidableLT := decidableLT
    decidableEq := decidableEq
    min := (· ⊓ ·)
    max := (· ⊔ ·)
    min_def := by
      intros x y
      -- ⊢ min x y = if x ≤ y then x else y
      apply inj
      -- ⊢ f (min x y) = f (if x ≤ y then x else y)
      rw [apply_ite f]
      -- ⊢ f (min x y) = if x ≤ y then f x else f y
      exact (hinf _ _).trans (min_def _ _)
      -- 🎉 no goals
    max_def := by
      intros x y
      -- ⊢ max x y = if x ≤ y then y else x
      apply inj
      -- ⊢ f (max x y) = f (if x ≤ y then y else x)
      rw [apply_ite f]
      -- ⊢ f (max x y) = if x ≤ y then f y else f x
      exact (hsup _ _).trans (max_def _ _)
      -- 🎉 no goals
    compare_eq_compareOfLessAndEq := fun a b ↦
      compare_of_injective_eq_compareOfLessAndEq a b f inj }

/-- Transfer a `LinearOrder` on `β` to a `LinearOrder` on `α` using an injective
function `f : α → β`. This version autogenerates `min` and `max` fields. See `LinearOrder.lift`
for a version that takes `[Sup α]` and `[Inf α]`, then uses them as `max` and `min`. See
`LinearOrder.liftWithOrd'` for a version which does not auto-generate `compare` fields.
See note [reducible non-instances]. -/
@[reducible]
def LinearOrder.lift' {α β} [LinearOrder β] (f : α → β) (inj : Injective f) : LinearOrder α :=
  @LinearOrder.lift α β _ ⟨fun x y ↦ if f x ≤ f y then y else x⟩
    ⟨fun x y ↦ if f x ≤ f y then x else y⟩ f inj
    (fun _ _ ↦ (apply_ite f _ _ _).trans (max_def _ _).symm) fun _ _ ↦
    (apply_ite f _ _ _).trans (min_def _ _).symm
#align linear_order.lift' LinearOrder.lift'

/-- Transfer a `LinearOrder` on `β` to a `LinearOrder` on `α` using an injective
function `f : α → β`. This version takes `[Sup α]` and `[Inf α]` as arguments, then uses
them for `max` and `min` fields. It also takes `[Ord α]` as an argument and uses them for `compare`
fields. See `LinearOrder.lift` for a version that autogenerates `compare` fields, and
`LinearOrder.liftWithOrd'` for one that auto-generates `min` and `max` fields.
fields. See note [reducible non-instances]. -/
@[reducible]
def LinearOrder.liftWithOrd {α β} [LinearOrder β] [Sup α] [Inf α] [Ord α] (f : α → β)
    (inj : Injective f) (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y))
    (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y))
    (compare_f : ∀ a b : α, compare a b = compare (f a) (f b)) : LinearOrder α :=
  letI decidableLE := fun x y ↦ (inferInstance : Decidable (f x ≤ f y))
  letI decidableLT := fun x y ↦ (inferInstance : Decidable (f x < f y))
  letI decidableEq := fun x y ↦ decidable_of_iff (f x = f y) inj.eq_iff
  { PartialOrder.lift f inj with
    le_total := fun x y ↦ le_total (f x) (f y)
    decidableLE := decidableLE
    decidableLT := decidableLT
    decidableEq := decidableEq
    min := (· ⊓ ·)
    max := (· ⊔ ·)
    min_def := by
      intros x y
      -- ⊢ min x y = if x ≤ y then x else y
      apply inj
      -- ⊢ f (min x y) = f (if x ≤ y then x else y)
      rw [apply_ite f]
      -- ⊢ f (min x y) = if x ≤ y then f x else f y
      exact (hinf _ _).trans (min_def _ _)
      -- 🎉 no goals
    max_def := by
      intros x y
      -- ⊢ max x y = if x ≤ y then y else x
      apply inj
      -- ⊢ f (max x y) = f (if x ≤ y then y else x)
      rw [apply_ite f]
      -- ⊢ f (max x y) = if x ≤ y then f y else f x
      exact (hsup _ _).trans (max_def _ _)
      -- 🎉 no goals
    compare_eq_compareOfLessAndEq := fun a b ↦
      (compare_f a b).trans <| compare_of_injective_eq_compareOfLessAndEq a b f inj }

/-- Transfer a `LinearOrder` on `β` to a `LinearOrder` on `α` using an injective
function `f : α → β`. This version auto-generates `min` and `max` fields. It also takes `[Ord α]`
as an argument and uses them for `compare` fields. See `LinearOrder.lift` for a version that
autogenerates `compare` fields, and `LinearOrder.liftWithOrd` for one that doesn't auto-generate
`min` and `max` fields. fields. See note [reducible non-instances]. -/
@[reducible]
def LinearOrder.liftWithOrd' {α β} [LinearOrder β] [Ord α] (f : α → β)
    (inj : Injective f)
    (compare_f : ∀ a b : α, compare a b = compare (f a) (f b)) : LinearOrder α :=
  @LinearOrder.liftWithOrd α β _ ⟨fun x y ↦ if f x ≤ f y then y else x⟩
    ⟨fun x y ↦ if f x ≤ f y then x else y⟩ _ f inj
    (fun _ _ ↦ (apply_ite f _ _ _).trans (max_def _ _).symm)
    (fun _ _ ↦ (apply_ite f _ _ _).trans (min_def _ _).symm)
    compare_f

/-! ### Subtype of an order -/


namespace Subtype

instance le [LE α] {p : α → Prop} : LE (Subtype p) :=
  ⟨fun x y ↦ (x : α) ≤ y⟩

instance lt [LT α] {p : α → Prop} : LT (Subtype p) :=
  ⟨fun x y ↦ (x : α) < y⟩

@[simp]
theorem mk_le_mk [LE α] {p : α → Prop} {x y : α} {hx : p x} {hy : p y} :
    (⟨x, hx⟩ : Subtype p) ≤ ⟨y, hy⟩ ↔ x ≤ y :=
  Iff.rfl
#align subtype.mk_le_mk Subtype.mk_le_mk

@[simp]
theorem mk_lt_mk [LT α] {p : α → Prop} {x y : α} {hx : p x} {hy : p y} :
    (⟨x, hx⟩ : Subtype p) < ⟨y, hy⟩ ↔ x < y :=
  Iff.rfl
#align subtype.mk_lt_mk Subtype.mk_lt_mk

@[simp, norm_cast]
theorem coe_le_coe [LE α] {p : α → Prop} {x y : Subtype p} : (x : α) ≤ y ↔ x ≤ y :=
  Iff.rfl
#align subtype.coe_le_coe Subtype.coe_le_coe

@[simp, norm_cast]
theorem coe_lt_coe [LT α] {p : α → Prop} {x y : Subtype p} : (x : α) < y ↔ x < y :=
  Iff.rfl
#align subtype.coe_lt_coe Subtype.coe_lt_coe

instance preorder [Preorder α] (p : α → Prop) : Preorder (Subtype p) :=
  Preorder.lift (fun (a : Subtype p) ↦ (a : α))

instance partialOrder [PartialOrder α] (p : α → Prop) : PartialOrder (Subtype p) :=
  PartialOrder.lift (fun (a : Subtype p) ↦ (a : α)) Subtype.coe_injective
#align subtype.partial_order Subtype.partialOrder

instance decidableLE [Preorder α] [h : @DecidableRel α (· ≤ ·)] {p : α → Prop} :
    @DecidableRel (Subtype p) (· ≤ ·) := fun a b ↦ h a b
#align subtype.decidable_le Subtype.decidableLE

instance decidableLT [Preorder α] [h : @DecidableRel α (· < ·)] {p : α → Prop} :
    @DecidableRel (Subtype p) (· < ·) := fun a b ↦ h a b
#align subtype.decidable_lt Subtype.decidableLT

/-- A subtype of a linear order is a linear order. We explicitly give the proofs of decidable
equality and decidable order in order to ensure the decidability instances are all definitionally
equal. -/
instance linearOrder [LinearOrder α] (p : α → Prop) : LinearOrder (Subtype p) :=
  @LinearOrder.lift (Subtype p) _ _ ⟨fun x y ↦ ⟨max x y, max_rec' _ x.2 y.2⟩⟩
    ⟨fun x y ↦ ⟨min x y, min_rec' _ x.2 y.2⟩⟩ (fun (a : Subtype p) ↦ (a : α))
    Subtype.coe_injective (fun _ _ ↦ rfl) fun _ _ ↦
    rfl

end Subtype

/-!
### Pointwise order on `α × β`

The lexicographic order is defined in `Data.Prod.Lex`, and the instances are available via the
type synonym `α ×ₗ β = α × β`.
-/


namespace Prod

instance (α : Type u) (β : Type v) [LE α] [LE β] : LE (α × β) :=
  ⟨fun p q ↦ p.1 ≤ q.1 ∧ p.2 ≤ q.2⟩

-- Porting note: new instance
instance instDecidableLE (α : Type u) (β : Type v) [LE α] [LE β] (x y : α × β)
    [Decidable (x.1 ≤ y.1)] [Decidable (x.2 ≤ y.2)] : Decidable (x ≤ y) := And.decidable

theorem le_def [LE α] [LE β] {x y : α × β} : x ≤ y ↔ x.1 ≤ y.1 ∧ x.2 ≤ y.2 :=
  Iff.rfl
#align prod.le_def Prod.le_def

@[simp]
theorem mk_le_mk [LE α] [LE β] {x₁ x₂ : α} {y₁ y₂ : β} : (x₁, y₁) ≤ (x₂, y₂) ↔ x₁ ≤ x₂ ∧ y₁ ≤ y₂ :=
  Iff.rfl
#align prod.mk_le_mk Prod.mk_le_mk

@[simp]
theorem swap_le_swap [LE α] [LE β] {x y : α × β} : x.swap ≤ y.swap ↔ x ≤ y :=
  and_comm
#align prod.swap_le_swap Prod.swap_le_swap

section Preorder

variable [Preorder α] [Preorder β] {a a₁ a₂ : α} {b b₁ b₂ : β} {x y : α × β}

instance (α : Type u) (β : Type v) [Preorder α] [Preorder β] : Preorder (α × β) where
  __ := inferInstanceAs (LE (α × β))
  le_refl := fun ⟨a, b⟩ ↦ ⟨le_refl a, le_refl b⟩
  le_trans := fun ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩ ⟨hac, hbd⟩ ⟨hce, hdf⟩ ↦ ⟨le_trans hac hce, le_trans hbd hdf⟩

@[simp]
theorem swap_lt_swap : x.swap < y.swap ↔ x < y :=
  and_congr swap_le_swap (not_congr swap_le_swap)
#align prod.swap_lt_swap Prod.swap_lt_swap

theorem mk_le_mk_iff_left : (a₁, b) ≤ (a₂, b) ↔ a₁ ≤ a₂ :=
  and_iff_left le_rfl
#align prod.mk_le_mk_iff_left Prod.mk_le_mk_iff_left

theorem mk_le_mk_iff_right : (a, b₁) ≤ (a, b₂) ↔ b₁ ≤ b₂ :=
  and_iff_right le_rfl
#align prod.mk_le_mk_iff_right Prod.mk_le_mk_iff_right

theorem mk_lt_mk_iff_left : (a₁, b) < (a₂, b) ↔ a₁ < a₂ :=
  lt_iff_lt_of_le_iff_le' mk_le_mk_iff_left mk_le_mk_iff_left
#align prod.mk_lt_mk_iff_left Prod.mk_lt_mk_iff_left

theorem mk_lt_mk_iff_right : (a, b₁) < (a, b₂) ↔ b₁ < b₂ :=
  lt_iff_lt_of_le_iff_le' mk_le_mk_iff_right mk_le_mk_iff_right
#align prod.mk_lt_mk_iff_right Prod.mk_lt_mk_iff_right

theorem lt_iff : x < y ↔ x.1 < y.1 ∧ x.2 ≤ y.2 ∨ x.1 ≤ y.1 ∧ x.2 < y.2 := by
  refine' ⟨fun h ↦ _, _⟩
  -- ⊢ x.fst < y.fst ∧ x.snd ≤ y.snd ∨ x.fst ≤ y.fst ∧ x.snd < y.snd
  · by_cases h₁ : y.1 ≤ x.1
    -- ⊢ x.fst < y.fst ∧ x.snd ≤ y.snd ∨ x.fst ≤ y.fst ∧ x.snd < y.snd
    · exact Or.inr ⟨h.1.1, LE.le.lt_of_not_le h.1.2 fun h₂ ↦ h.2 ⟨h₁, h₂⟩⟩
      -- 🎉 no goals
    · exact Or.inl ⟨LE.le.lt_of_not_le h.1.1 h₁, h.1.2⟩
      -- 🎉 no goals
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    -- ⊢ x < y
    · exact ⟨⟨h₁.le, h₂⟩, fun h ↦ h₁.not_le h.1⟩
      -- 🎉 no goals
    · exact ⟨⟨h₁, h₂.le⟩, fun h ↦ h₂.not_le h.2⟩
      -- 🎉 no goals
#align prod.lt_iff Prod.lt_iff

@[simp]
theorem mk_lt_mk : (a₁, b₁) < (a₂, b₂) ↔ a₁ < a₂ ∧ b₁ ≤ b₂ ∨ a₁ ≤ a₂ ∧ b₁ < b₂ :=
  lt_iff
#align prod.mk_lt_mk Prod.mk_lt_mk

end Preorder

/-- The pointwise partial order on a product.
    (The lexicographic ordering is defined in `Order.Lexicographic`, and the instances are
    available via the type synonym `α ×ₗ β = α × β`.) -/
instance instPartialOrder (α : Type u) (β : Type v) [PartialOrder α] [PartialOrder β] :
    PartialOrder (α × β) where
  __ := inferInstanceAs (Preorder (α × β))
  le_antisymm := fun _ _ ⟨hac, hbd⟩ ⟨hca, hdb⟩ ↦ Prod.ext (hac.antisymm hca) (hbd.antisymm hdb)

end Prod

/-! ### Additional order classes -/


/-- An order is dense if there is an element between any pair of distinct comparable elements. -/
class DenselyOrdered (α : Type u) [LT α] : Prop where
  /-- An order is dense if there is an element between any pair of distinct elements. -/
  dense : ∀ a₁ a₂ : α, a₁ < a₂ → ∃ a, a₁ < a ∧ a < a₂
#align densely_ordered DenselyOrdered

theorem exists_between [LT α] [DenselyOrdered α] : ∀ {a₁ a₂ : α}, a₁ < a₂ → ∃ a, a₁ < a ∧ a < a₂ :=
  DenselyOrdered.dense _ _
#align exists_between exists_between

instance OrderDual.denselyOrdered (α : Type u) [LT α] [h : DenselyOrdered α] :
    DenselyOrdered αᵒᵈ :=
  ⟨fun _ _ ha ↦ (@exists_between α _ h _ _ ha).imp fun _ ↦ And.symm⟩
#align order_dual.densely_ordered OrderDual.denselyOrdered

@[simp]
theorem denselyOrdered_orderDual [LT α] : DenselyOrdered αᵒᵈ ↔ DenselyOrdered α :=
  ⟨by convert @OrderDual.denselyOrdered αᵒᵈ _, @OrderDual.denselyOrdered α _⟩
      -- 🎉 no goals
#align densely_ordered_order_dual denselyOrdered_orderDual

instance [Preorder α] [Preorder β] [DenselyOrdered α] [DenselyOrdered β] : DenselyOrdered (α × β) :=
  ⟨fun a b ↦ by
    simp_rw [Prod.lt_iff]
    -- ⊢ a.fst < b.fst ∧ a.snd ≤ b.snd ∨ a.fst ≤ b.fst ∧ a.snd < b.snd → ∃ a_2, (a.fs …
    rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    -- ⊢ ∃ a_1, (a.fst < a_1.fst ∧ a.snd ≤ a_1.snd ∨ a.fst ≤ a_1.fst ∧ a.snd < a_1.sn …
    · obtain ⟨c, ha, hb⟩ := exists_between h₁
      -- ⊢ ∃ a_1, (a.fst < a_1.fst ∧ a.snd ≤ a_1.snd ∨ a.fst ≤ a_1.fst ∧ a.snd < a_1.sn …
      exact ⟨(c, _), Or.inl ⟨ha, h₂⟩, Or.inl ⟨hb, le_rfl⟩⟩
      -- 🎉 no goals
    · obtain ⟨c, ha, hb⟩ := exists_between h₂
      -- ⊢ ∃ a_1, (a.fst < a_1.fst ∧ a.snd ≤ a_1.snd ∨ a.fst ≤ a_1.fst ∧ a.snd < a_1.sn …
      exact ⟨(_, c), Or.inr ⟨h₁, ha⟩, Or.inr ⟨le_rfl, hb⟩⟩⟩
      -- 🎉 no goals

instance {α : ι → Type*} [∀ i, Preorder (α i)] [∀ i, DenselyOrdered (α i)] :
    DenselyOrdered (∀ i, α i) :=
  ⟨fun a b ↦ by
    classical
      simp_rw [Pi.lt_def]
      rintro ⟨hab, i, hi⟩
      obtain ⟨c, ha, hb⟩ := exists_between hi
      exact
        ⟨Function.update a i c,
          ⟨le_update_iff.2 ⟨ha.le, fun _ _ ↦ le_rfl⟩, i, by rwa [update_same]⟩,
          update_le_iff.2 ⟨hb.le, fun _ _ ↦ hab _⟩, i, by rwa [update_same]⟩⟩

theorem le_of_forall_le_of_dense [LinearOrder α] [DenselyOrdered α] {a₁ a₂ : α}
    (h : ∀ a, a₂ < a → a₁ ≤ a) : a₁ ≤ a₂ :=
  le_of_not_gt fun ha ↦
    let ⟨a, ha₁, ha₂⟩ := exists_between ha
    lt_irrefl a <| lt_of_lt_of_le ‹a < a₁› (h _ ‹a₂ < a›)
#align le_of_forall_le_of_dense le_of_forall_le_of_dense

theorem eq_of_le_of_forall_le_of_dense [LinearOrder α] [DenselyOrdered α] {a₁ a₂ : α} (h₁ : a₂ ≤ a₁)
    (h₂ : ∀ a, a₂ < a → a₁ ≤ a) : a₁ = a₂ :=
  le_antisymm (le_of_forall_le_of_dense h₂) h₁
#align eq_of_le_of_forall_le_of_dense eq_of_le_of_forall_le_of_dense

theorem le_of_forall_ge_of_dense [LinearOrder α] [DenselyOrdered α] {a₁ a₂ : α}
    (h : ∀ a₃ < a₁, a₃ ≤ a₂) : a₁ ≤ a₂ :=
  le_of_not_gt fun ha ↦
    let ⟨a, ha₁, ha₂⟩ := exists_between ha
    lt_irrefl a <| lt_of_le_of_lt (h _ ‹a < a₁›) ‹a₂ < a›
#align le_of_forall_ge_of_dense le_of_forall_ge_of_dense

theorem eq_of_le_of_forall_ge_of_dense [LinearOrder α] [DenselyOrdered α] {a₁ a₂ : α} (h₁ : a₂ ≤ a₁)
    (h₂ : ∀ a₃ < a₁, a₃ ≤ a₂) : a₁ = a₂ :=
  (le_of_forall_ge_of_dense h₂).antisymm h₁
#align eq_of_le_of_forall_ge_of_dense eq_of_le_of_forall_ge_of_dense

theorem dense_or_discrete [LinearOrder α] (a₁ a₂ : α) :
    (∃ a, a₁ < a ∧ a < a₂) ∨ (∀ a, a₁ < a → a₂ ≤ a) ∧ ∀ a < a₂, a ≤ a₁ :=
  or_iff_not_imp_left.2 fun h ↦
    ⟨fun a ha₁ ↦ le_of_not_gt fun ha₂ ↦ h ⟨a, ha₁, ha₂⟩,
     fun a ha₂ ↦ le_of_not_gt fun ha₁ ↦ h ⟨a, ha₁, ha₂⟩⟩
#align dense_or_discrete dense_or_discrete

/-- If a linear order has no elements `x < y < z`, then it has at most two elements. -/
lemma eq_or_eq_or_eq_of_forall_not_lt_lt [LinearOrder α]
    (h : ∀ ⦃x y z : α⦄, x < y → y < z → False) (x y z : α) : x = y ∨ y = z ∨ x = z := by
  by_contra hne
  -- ⊢ False
  simp only [not_or, ← Ne.def] at hne
  -- ⊢ False
  cases' hne.1.lt_or_lt with h₁ h₁ <;> cases' hne.2.1.lt_or_lt with h₂ h₂ <;>
  -- ⊢ False
                                       -- ⊢ False
                                       -- ⊢ False
    cases' hne.2.2.lt_or_lt with h₃ h₃
    -- ⊢ False
    -- ⊢ False
    -- ⊢ False
    -- ⊢ False
  exacts [h h₁ h₂, h h₂ h₃, h h₃ h₂, h h₃ h₁, h h₁ h₃, h h₂ h₃, h h₁ h₃, h h₂ h₁]
  -- 🎉 no goals
#align eq_or_eq_or_eq_of_forall_not_lt_lt eq_or_eq_or_eq_of_forall_not_lt_lt

namespace PUnit

variable (a b : PUnit.{u + 1})

instance linearOrder: LinearOrder PUnit where
  le  := fun _ _ ↦ True
  lt  := fun _ _ ↦ False
  max := fun _ _ ↦ unit
  min := fun _ _ ↦ unit
  decidableEq := inferInstance
  decidableLE := fun _ _ ↦ Decidable.isTrue trivial
  decidableLT := fun _ _ ↦ Decidable.isFalse id
  le_refl     := by intros; trivial
                    -- ⊢ a✝ ≤ a✝
                            -- 🎉 no goals
  le_trans    := by intros; trivial
                    -- ⊢ a✝² ≤ c✝
                            -- 🎉 no goals
  le_total    := by intros; exact Or.inl trivial
                    -- ⊢ a✝ ≤ b✝ ∨ b✝ ≤ a✝
                    -- ⊢ a✝² = b✝
                         -- 🎉 no goals
                            -- 🎉 no goals
                            -- 🎉 no goals
  le_antisymm := by intros; rfl
  lt_iff_le_not_le := by simp only [not_true, and_false, forall_const]

theorem max_eq : max a b = unit :=
  rfl
#align punit.max_eq PUnit.max_eq

theorem min_eq : min a b = unit :=
  rfl
#align punit.min_eq PUnit.min_eq

-- Porting note: simp can prove this @[simp]
protected theorem le : a ≤ b :=
  trivial
#align punit.le PUnit.le

-- Porting note: simp can prove this @[simp]
theorem not_lt : ¬a < b :=
  not_false
#align punit.not_lt PUnit.not_lt

instance : DenselyOrdered PUnit :=
  ⟨fun _ _ ↦ False.elim⟩

end PUnit

section «Prop»

/-- Propositions form a complete boolean algebra, where the `≤` relation is given by implication. -/
instance Prop.le : LE Prop :=
  ⟨(· → ·)⟩
#align Prop.has_le Prop.le

@[simp]
theorem le_Prop_eq : ((· ≤ ·) : Prop → Prop → Prop) = (· → ·) :=
  rfl
#align le_Prop_eq le_Prop_eq

theorem subrelation_iff_le {r s : α → α → Prop} : Subrelation r s ↔ r ≤ s :=
  Iff.rfl
#align subrelation_iff_le subrelation_iff_le

instance Prop.partialOrder : PartialOrder Prop where
  __ := Prop.le
  le_refl _ := id
  le_trans _ _ _ f g := g ∘ f
  le_antisymm _ _ Hab Hba := propext ⟨Hab, Hba⟩
#align Prop.partial_order Prop.partialOrder

end «Prop»

variable {s : β → β → Prop} {t : γ → γ → Prop}

/-! ### Linear order from a total partial order -/


/-- Type synonym to create an instance of `LinearOrder` from a `PartialOrder` and `IsTotal α (≤)` -/
def AsLinearOrder (α : Type u) :=
  α
#align as_linear_order AsLinearOrder

instance {α} [Inhabited α] : Inhabited (AsLinearOrder α) :=
  ⟨(default : α)⟩

noncomputable instance AsLinearOrder.linearOrder {α} [PartialOrder α] [IsTotal α (· ≤ ·)] :
    LinearOrder (AsLinearOrder α) where
  __ := inferInstanceAs (PartialOrder α)
  le_total := @total_of α (· ≤ ·) _
  decidableLE := Classical.decRel _
#align as_linear_order.linear_order AsLinearOrder.linearOrder
