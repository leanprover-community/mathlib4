/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Yury Kudryashov, Yaël Dillies
-/
import Mathlib.Order.Synonym

/-!
# Minimal/maximal and bottom/top elements

This file defines predicates for elements to be minimal/maximal or bottom/top and typeclasses
saying that there are no such elements.

## Predicates

* `IsBot`: An element is *bottom* if all elements are greater than it.
* `IsTop`: An element is *top* if all elements are less than it.
* `IsMin`: An element is *minimal* if no element is strictly less than it.
* `IsMax`: An element is *maximal* if no element is strictly greater than it.

See also `isBot_iff_isMin` and `isTop_iff_isMax` for the equivalences in a (co)directed order.

## Typeclasses

* `NoBotOrder`: An order without bottom elements.
* `NoTopOrder`: An order without top elements.
* `NoMinOrder`: An order without minimal elements.
* `NoMaxOrder`: An order without maximal elements.
-/


open OrderDual

variable {α β : Type _}

/-- Order without bottom elements. -/
class NoBotOrder (α : Type _) [LE α] : Prop where
  exists_not_ge (a : α) : ∃ b, ¬a ≤ b

/-- Order without top elements. -/
class NoTopOrder (α : Type _) [LE α] : Prop where
  exists_not_le (a : α) : ∃ b, ¬b ≤ a

/-- Order without minimal elements. Sometimes called coinitial or dense. -/
class NoMinOrder (α : Type _) [LT α] : Prop where
  exists_lt (a : α) : ∃ b, b < a

/-- Order without maximal elements. Sometimes called cofinal. -/
class NoMaxOrder (α : Type _) [LT α] : Prop where
  exists_gt (a : α) : ∃ b, a < b

export NoBotOrder (exists_not_ge)

export NoTopOrder (exists_not_le)

export NoMinOrder (exists_lt)

export NoMaxOrder (exists_gt)

instance [LT α] [NoMinOrder α] (a : α) : Nonempty { x // x < a } :=
  nonempty_subtype.2 (exists_lt a)

instance [LT α] [NoMaxOrder α] (a : α) : Nonempty { x // a < x } :=
  nonempty_subtype.2 (exists_gt a)

instance [LE α] [NoTopOrder α] : NoBotOrder αᵒᵈ :=
  ⟨fun a => @exists_not_le α _ _ a⟩

instance [LE α] [NoBotOrder α] : NoTopOrder αᵒᵈ :=
  ⟨fun a => @exists_not_ge α _ _ a⟩

instance [LT α] [NoMaxOrder α] : NoMinOrder αᵒᵈ :=
  ⟨fun a => @exists_gt α _ _ a⟩

instance [LT α] [NoMinOrder α] : NoMaxOrder αᵒᵈ :=
  ⟨fun a => @exists_lt α _ _ a⟩

-- See note [lower instance priority]
instance (priority := 100) [Preorder α] [NoMinOrder α] : NoBotOrder α :=
  ⟨fun a => (exists_lt a).imp fun _ => not_le_of_lt⟩

-- See note [lower instance priority]
instance (priority := 100) [Preorder α] [NoMaxOrder α] : NoTopOrder α :=
  ⟨fun a => (exists_gt a).imp fun _ => not_le_of_lt⟩

-- Porting note: mathlib3 proof uses `convert`
theorem NoBotOrder.to_noMinOrder (α : Type _) [LinearOrder α] [NoBotOrder α] : NoMinOrder α :=
  { exists_lt := fun a => by simpa [not_le] using exists_not_ge a }
#align no_bot_order.to_no_min_order NoBotOrder.to_noMinOrder

-- Porting note: mathlib3 proof uses `convert`
theorem NoTopOrder.to_noMaxOrder (α : Type _) [LinearOrder α] [NoTopOrder α] : NoMaxOrder α :=
  { exists_gt := fun a => by simpa [not_le] using exists_not_le a }
#align no_top_order.to_no_max_order NoTopOrder.to_noMaxOrder

theorem no_bot_order_iff_no_min_order (α : Type _) [LinearOrder α] : NoBotOrder α ↔ NoMinOrder α :=
  ⟨fun h =>
    haveI := h
    NoBotOrder.to_noMinOrder α,
    fun h =>
    haveI := h
    inferInstance⟩

theorem no_top_order_iff_no_max_order (α : Type _) [LinearOrder α] : NoTopOrder α ↔ NoMaxOrder α :=
  ⟨fun h =>
    haveI := h
    NoTopOrder.to_noMaxOrder α,
    fun h =>
    haveI := h
    inferInstance⟩

theorem NoMinOrder.not_acc [LT α] [NoMinOrder α] (a : α) : ¬Acc (· < ·) a := fun h =>
  Acc.recOn h fun x _ => (exists_lt x).recOn

theorem NoMaxOrder.not_acc [LT α] [NoMaxOrder α] (a : α) : ¬Acc (· > ·) a := fun h =>
  Acc.recOn h fun x _ => (exists_gt x).recOn

section LE

variable [LE α] {a b : α}

/-- `a : α` is a bottom element of `α` if it is less than or equal to any other element of `α`.
This predicate is roughly an unbundled version of `OrderBot`, except that a preorder may have
several bottom elements. When `α` is linear, this is useful to make a case disjunction on
`NoMinOrder α` within a proof. -/
def IsBot (a : α) : Prop :=
  ∀ b, a ≤ b

/-- `a : α` is a top element of `α` if it is greater than or equal to any other element of `α`.
This predicate is roughly an unbundled version of `OrderBot`, except that a preorder may have
several top elements. When `α` is linear, this is useful to make a case disjunction on
`NoMaxOrder α` within a proof. -/
def IsTop (a : α) : Prop :=
  ∀ b, b ≤ a

/-- `a` is a minimal element of `α` if no element is strictly less than it. We spell it without `<`
to avoid having to convert between `≤` and `<`. Instead, `is_min_iff_forall_not_lt` does the
conversion. -/
def IsMin (a : α) : Prop :=
  ∀ ⦃b⦄, b ≤ a → a ≤ b

/-- `a` is a maximal element of `α` if no element is strictly greater than it. We spell it without
`<` to avoid having to convert between `≤` and `<`. Instead, `is_max_iff_forall_not_lt` does the
conversion. -/
def IsMax (a : α) : Prop :=
  ∀ ⦃b⦄, a ≤ b → b ≤ a

@[simp]
theorem not_is_bot [NoBotOrder α] (a : α) : ¬IsBot a := fun h =>
  let ⟨_, hb⟩ := exists_not_ge a
  hb <| h _

@[simp]
theorem not_is_top [NoTopOrder α] (a : α) : ¬IsTop a := fun h =>
  let ⟨_, hb⟩ := exists_not_le a
  hb <| h _

protected theorem IsBot.is_min (h : IsBot a) : IsMin a := fun b _ => h b

protected theorem IsTop.is_max (h : IsTop a) : IsMax a := fun b _ => h b

@[simp]
theorem is_bot_to_dual_iff : IsBot (toDual a) ↔ IsTop a :=
  Iff.rfl

@[simp]
theorem is_top_to_dual_iff : IsTop (toDual a) ↔ IsBot a :=
  Iff.rfl

@[simp]
theorem is_min_to_dual_iff : IsMin (toDual a) ↔ IsMax a :=
  Iff.rfl

@[simp]
theorem is_max_to_dual_iff : IsMax (toDual a) ↔ IsMin a :=
  Iff.rfl

@[simp]
theorem is_bot_of_dual_iff {a : αᵒᵈ} : IsBot (ofDual a) ↔ IsTop a :=
  Iff.rfl

@[simp]
theorem is_top_of_dual_iff {a : αᵒᵈ} : IsTop (ofDual a) ↔ IsBot a :=
  Iff.rfl

@[simp]
theorem is_min_of_dual_iff {a : αᵒᵈ} : IsMin (ofDual a) ↔ IsMax a :=
  Iff.rfl

@[simp]
theorem is_max_of_dual_iff {a : αᵒᵈ} : IsMax (ofDual a) ↔ IsMin a :=
  Iff.rfl

alias is_bot_to_dual_iff ↔ _ IsTop.to_dual

alias is_top_to_dual_iff ↔ _ IsBot.to_dual

alias is_min_to_dual_iff ↔ _ IsMax.to_dual

alias is_max_to_dual_iff ↔ _ IsMin.to_dual

alias is_bot_of_dual_iff ↔ _ IsTop.of_dual

alias is_top_of_dual_iff ↔ _ IsBot.of_dual

alias is_min_of_dual_iff ↔ _ IsMax.of_dual

alias is_max_of_dual_iff ↔ _ IsMin.of_dual

end LE

section Preorder

variable [Preorder α] {a b : α}

theorem IsBot.mono (ha : IsBot a) (h : b ≤ a) : IsBot b := fun _ => h.trans <| ha _

theorem IsTop.mono (ha : IsTop a) (h : a ≤ b) : IsTop b := fun _ => (ha _).trans h

theorem IsMin.mono (ha : IsMin a) (h : b ≤ a) : IsMin b := fun _ hc => h.trans <| ha <| hc.trans h

theorem IsMax.mono (ha : IsMax a) (h : a ≤ b) : IsMax b := fun _ hc => (ha <| h.trans hc).trans h

theorem IsMin.not_lt (h : IsMin a) : ¬b < a := fun hb => hb.not_le <| h hb.le

theorem IsMax.not_lt (h : IsMax a) : ¬a < b := fun hb => hb.not_le <| h hb.le

@[simp]
theorem not_is_min_of_lt (h : b < a) : ¬IsMin a := fun ha => ha.not_lt h

@[simp]
theorem not_is_max_of_lt (h : a < b) : ¬IsMax a := fun ha => ha.not_lt h

alias not_is_min_of_lt ← LT.lt.not_is_min

alias not_is_max_of_lt ← LT.lt.not_is_max

theorem is_min_iff_forall_not_lt : IsMin a ↔ ∀ b, ¬b < a :=
  ⟨fun h _ => h.not_lt, fun h _ hba => of_not_not fun hab => h _ <| hba.lt_of_not_le hab⟩

theorem is_max_iff_forall_not_lt : IsMax a ↔ ∀ b, ¬a < b :=
  ⟨fun h _ => h.not_lt, fun h _ hba => of_not_not fun hab => h _ <| hba.lt_of_not_le hab⟩

@[simp]
theorem not_is_min_iff : ¬IsMin a ↔ ∃ b, b < a := by
  simp [lt_iff_le_not_le, IsMin, not_forall, exists_prop]

@[simp]
theorem not_is_max_iff : ¬IsMax a ↔ ∃ b, a < b := by
  simp [lt_iff_le_not_le, IsMax, not_forall, exists_prop]

@[simp]
theorem not_is_min [NoMinOrder α] (a : α) : ¬IsMin a :=
  not_is_min_iff.2 <| exists_lt a

@[simp]
theorem not_is_max [NoMaxOrder α] (a : α) : ¬IsMax a :=
  not_is_max_iff.2 <| exists_gt a

namespace Subsingleton

variable [Subsingleton α]

protected theorem is_bot (a : α) : IsBot a := fun _ => (Subsingleton.elim _ _).le

protected theorem is_top (a : α) : IsTop a := fun _ => (Subsingleton.elim _ _).le

protected theorem is_min (a : α) : IsMin a :=
  (Subsingleton.is_bot _).is_min

protected theorem is_max (a : α) : IsMax a :=
  (Subsingleton.is_top _).is_max

end Subsingleton

end Preorder

section PartialOrder

variable [PartialOrder α] {a b : α}

protected theorem IsMin.eq_of_le (ha : IsMin a) (h : b ≤ a) : b = a :=
  h.antisymm <| ha h

protected theorem IsMin.eq_of_ge (ha : IsMin a) (h : b ≤ a) : a = b :=
  h.antisymm' <| ha h

protected theorem IsMax.eq_of_le (ha : IsMax a) (h : a ≤ b) : a = b :=
  h.antisymm <| ha h

protected theorem IsMax.eq_of_ge (ha : IsMax a) (h : a ≤ b) : b = a :=
  h.antisymm' <| ha h

end PartialOrder

section Prod

variable [Preorder α] [Preorder β] {a a₁ a₂ : α} {b b₁ b₂ : β} {x y : α × β}

theorem IsBot.prod_mk (ha : IsBot a) (hb : IsBot b) : IsBot (a, b) := fun _ => ⟨ha _, hb _⟩

theorem IsTop.prod_mk (ha : IsTop a) (hb : IsTop b) : IsTop (a, b) := fun _ => ⟨ha _, hb _⟩

theorem IsMin.prod_mk (ha : IsMin a) (hb : IsMin b) : IsMin (a, b) := fun _ hc => ⟨ha hc.1, hb hc.2⟩

theorem IsMax.prod_mk (ha : IsMax a) (hb : IsMax b) : IsMax (a, b) := fun _ hc => ⟨ha hc.1, hb hc.2⟩

theorem IsBot.fst (hx : IsBot x) : IsBot x.1 := fun c => (hx (c, x.2)).1

theorem IsBot.snd (hx : IsBot x) : IsBot x.2 := fun c => (hx (x.1, c)).2

theorem IsTop.fst (hx : IsTop x) : IsTop x.1 := fun c => (hx (c, x.2)).1

theorem IsTop.snd (hx : IsTop x) : IsTop x.2 := fun c => (hx (x.1, c)).2

theorem IsMin.fst (hx : IsMin x) : IsMin x.1 :=
  fun c hc => (hx <| show (c, x.2) ≤ x from (and_iff_left le_rfl).2 hc).1

theorem IsMin.snd (hx : IsMin x) : IsMin x.2 :=
  fun c hc => (hx <| show (x.1, c) ≤ x from (and_iff_right le_rfl).2 hc).2

theorem IsMax.fst (hx : IsMax x) : IsMax x.1 :=
  fun c hc => (hx <| show x ≤ (c, x.2) from (and_iff_left le_rfl).2 hc).1

theorem IsMax.snd (hx : IsMax x) : IsMax x.2 :=
  fun c hc => (hx <| show x ≤ (x.1, c) from (and_iff_right le_rfl).2 hc).2

theorem Prod.is_bot_iff : IsBot x ↔ IsBot x.1 ∧ IsBot x.2 :=
  ⟨fun hx => ⟨hx.fst, hx.snd⟩, fun h => h.1.prod_mk h.2⟩

theorem Prod.is_top_iff : IsTop x ↔ IsTop x.1 ∧ IsTop x.2 :=
  ⟨fun hx => ⟨hx.fst, hx.snd⟩, fun h => h.1.prod_mk h.2⟩

theorem Prod.is_min_iff : IsMin x ↔ IsMin x.1 ∧ IsMin x.2 :=
  ⟨fun hx => ⟨hx.fst, hx.snd⟩, fun h => h.1.prod_mk h.2⟩

theorem Prod.is_max_iff : IsMax x ↔ IsMax x.1 ∧ IsMax x.2 :=
  ⟨fun hx => ⟨hx.fst, hx.snd⟩, fun h => h.1.prod_mk h.2⟩

end Prod
