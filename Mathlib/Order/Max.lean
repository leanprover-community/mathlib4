/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Yury Kudryashov, Yaël Dillies
-/
import Mathlib.Order.Synonym

#align_import order.max from "leanprover-community/mathlib"@"6623e6af705e97002a9054c1c05a980180276fc1"

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

universe u v

variable {α β : Type*}

/-- Order without bottom elements. -/
class NoBotOrder (α : Type*) [LE α] : Prop where
  /-- For each term `a`, there is some `b` which is either incomparable or strictly smaller. -/
  exists_not_ge (a : α) : ∃ b, ¬a ≤ b
#align no_bot_order NoBotOrder

/-- Order without top elements. -/
class NoTopOrder (α : Type*) [LE α] : Prop where
  /-- For each term `a`, there is some `b` which is either incomparable or strictly larger. -/
  exists_not_le (a : α) : ∃ b, ¬b ≤ a
#align no_top_order NoTopOrder

/-- Order without minimal elements. Sometimes called coinitial or dense. -/
class NoMinOrder (α : Type*) [LT α] : Prop where
  /-- For each term `a`, there is some strictly smaller `b`. -/
  exists_lt (a : α) : ∃ b, b < a
#align no_min_order NoMinOrder

/-- Order without maximal elements. Sometimes called cofinal. -/
class NoMaxOrder (α : Type*) [LT α] : Prop where
  /-- For each term `a`, there is some strictly greater `b`. -/
  exists_gt (a : α) : ∃ b, a < b
#align no_max_order NoMaxOrder

export NoBotOrder (exists_not_ge)

export NoTopOrder (exists_not_le)

export NoMinOrder (exists_lt)

export NoMaxOrder (exists_gt)

instance nonempty_lt [LT α] [NoMinOrder α] (a : α) : Nonempty { x // x < a } :=
  nonempty_subtype.2 (exists_lt a)

instance nonempty_gt [LT α] [NoMaxOrder α] (a : α) : Nonempty { x // a < x } :=
  nonempty_subtype.2 (exists_gt a)

instance IsEmpty.toNoMaxOrder [LT α] [IsEmpty α] : NoMaxOrder α := ⟨isEmptyElim⟩
instance IsEmpty.toNoMinOrder [LT α] [IsEmpty α] : NoMinOrder α := ⟨isEmptyElim⟩

instance OrderDual.noBotOrder [LE α] [NoTopOrder α] : NoBotOrder αᵒᵈ :=
  ⟨fun a => @exists_not_le α _ _ a⟩
#align order_dual.no_bot_order OrderDual.noBotOrder

instance OrderDual.noTopOrder [LE α] [NoBotOrder α] : NoTopOrder αᵒᵈ :=
  ⟨fun a => @exists_not_ge α _ _ a⟩
#align order_dual.no_top_order OrderDual.noTopOrder

instance OrderDual.noMinOrder [LT α] [NoMaxOrder α] : NoMinOrder αᵒᵈ :=
  ⟨fun a => @exists_gt α _ _ a⟩
#align order_dual.no_min_order OrderDual.noMinOrder

instance OrderDual.noMaxOrder [LT α] [NoMinOrder α] : NoMaxOrder αᵒᵈ :=
  ⟨fun a => @exists_lt α _ _ a⟩
#align order_dual.no_max_order OrderDual.noMaxOrder

-- See note [lower instance priority]
instance (priority := 100) [Preorder α] [NoMinOrder α] : NoBotOrder α :=
  ⟨fun a => (exists_lt a).imp fun _ => not_le_of_lt⟩

-- See note [lower instance priority]
instance (priority := 100) [Preorder α] [NoMaxOrder α] : NoTopOrder α :=
  ⟨fun a => (exists_gt a).imp fun _ => not_le_of_lt⟩

instance noMaxOrder_of_left [Preorder α] [Preorder β] [NoMaxOrder α] : NoMaxOrder (α × β) :=
  ⟨fun ⟨a, b⟩ => by
    obtain ⟨c, h⟩ := exists_gt a
    exact ⟨(c, b), Prod.mk_lt_mk_iff_left.2 h⟩⟩
#align no_max_order_of_left noMaxOrder_of_left

instance noMaxOrder_of_right [Preorder α] [Preorder β] [NoMaxOrder β] : NoMaxOrder (α × β) :=
  ⟨fun ⟨a, b⟩ => by
    obtain ⟨c, h⟩ := exists_gt b
    exact ⟨(a, c), Prod.mk_lt_mk_iff_right.2 h⟩⟩
#align no_max_order_of_right noMaxOrder_of_right

instance noMinOrder_of_left [Preorder α] [Preorder β] [NoMinOrder α] : NoMinOrder (α × β) :=
  ⟨fun ⟨a, b⟩ => by
    obtain ⟨c, h⟩ := exists_lt a
    exact ⟨(c, b), Prod.mk_lt_mk_iff_left.2 h⟩⟩
#align no_min_order_of_left noMinOrder_of_left

instance noMinOrder_of_right [Preorder α] [Preorder β] [NoMinOrder β] : NoMinOrder (α × β) :=
  ⟨fun ⟨a, b⟩ => by
    obtain ⟨c, h⟩ := exists_lt b
    exact ⟨(a, c), Prod.mk_lt_mk_iff_right.2 h⟩⟩
#align no_min_order_of_right noMinOrder_of_right

instance {ι : Type u} {π : ι → Type*} [Nonempty ι] [∀ i, Preorder (π i)] [∀ i, NoMaxOrder (π i)] :
    NoMaxOrder (∀ i, π i) :=
  ⟨fun a => by
    classical
    obtain ⟨b, hb⟩ := exists_gt (a <| Classical.arbitrary _)
    exact ⟨_, lt_update_self_iff.2 hb⟩⟩

instance {ι : Type u} {π : ι → Type*} [Nonempty ι] [∀ i, Preorder (π i)] [∀ i, NoMinOrder (π i)] :
    NoMinOrder (∀ i, π i) :=
  ⟨fun a => by
     classical
      obtain ⟨b, hb⟩ := exists_lt (a <| Classical.arbitrary _)
      exact ⟨_, update_lt_self_iff.2 hb⟩⟩

-- Porting note: mathlib3 proof uses `convert`
theorem NoBotOrder.to_noMinOrder (α : Type*) [LinearOrder α] [NoBotOrder α] : NoMinOrder α :=
  { exists_lt := fun a => by simpa [not_le] using exists_not_ge a }
#align no_bot_order.to_no_min_order NoBotOrder.to_noMinOrder

-- Porting note: mathlib3 proof uses `convert`
theorem NoTopOrder.to_noMaxOrder (α : Type*) [LinearOrder α] [NoTopOrder α] : NoMaxOrder α :=
  { exists_gt := fun a => by simpa [not_le] using exists_not_le a }
#align no_top_order.to_no_max_order NoTopOrder.to_noMaxOrder

theorem noBotOrder_iff_noMinOrder (α : Type*) [LinearOrder α] : NoBotOrder α ↔ NoMinOrder α :=
  ⟨fun h =>
    haveI := h
    NoBotOrder.to_noMinOrder α,
    fun h =>
    haveI := h
    inferInstance⟩
#align no_bot_order_iff_no_min_order noBotOrder_iff_noMinOrder

theorem noTopOrder_iff_noMaxOrder (α : Type*) [LinearOrder α] : NoTopOrder α ↔ NoMaxOrder α :=
  ⟨fun h =>
    haveI := h
    NoTopOrder.to_noMaxOrder α,
    fun h =>
    haveI := h
    inferInstance⟩
#align no_top_order_iff_no_max_order noTopOrder_iff_noMaxOrder

theorem NoMinOrder.not_acc [LT α] [NoMinOrder α] (a : α) : ¬Acc (· < ·) a := fun h =>
  Acc.recOn h fun x _ => (exists_lt x).recOn
#align no_min_order.not_acc NoMinOrder.not_acc

theorem NoMaxOrder.not_acc [LT α] [NoMaxOrder α] (a : α) : ¬Acc (· > ·) a := fun h =>
  Acc.recOn h fun x _ => (exists_gt x).recOn
#align no_max_order.not_acc NoMaxOrder.not_acc

section LE

variable [LE α] {a b : α}

/-- `a : α` is a bottom element of `α` if it is less than or equal to any other element of `α`.
This predicate is roughly an unbundled version of `OrderBot`, except that a preorder may have
several bottom elements. When `α` is linear, this is useful to make a case disjunction on
`NoMinOrder α` within a proof. -/
def IsBot (a : α) : Prop :=
  ∀ b, a ≤ b
#align is_bot IsBot

/-- `a : α` is a top element of `α` if it is greater than or equal to any other element of `α`.
This predicate is roughly an unbundled version of `OrderBot`, except that a preorder may have
several top elements. When `α` is linear, this is useful to make a case disjunction on
`NoMaxOrder α` within a proof. -/
def IsTop (a : α) : Prop :=
  ∀ b, b ≤ a
#align is_top IsTop

/-- `a` is a minimal element of `α` if no element is strictly less than it. We spell it without `<`
to avoid having to convert between `≤` and `<`. Instead, `isMin_iff_forall_not_lt` does the
conversion. -/
def IsMin (a : α) : Prop :=
  ∀ ⦃b⦄, b ≤ a → a ≤ b
#align is_min IsMin

/-- `a` is a maximal element of `α` if no element is strictly greater than it. We spell it without
`<` to avoid having to convert between `≤` and `<`. Instead, `isMax_iff_forall_not_lt` does the
conversion. -/
def IsMax (a : α) : Prop :=
  ∀ ⦃b⦄, a ≤ b → b ≤ a
#align is_max IsMax

@[simp]
theorem not_isBot [NoBotOrder α] (a : α) : ¬IsBot a := fun h =>
  let ⟨_, hb⟩ := exists_not_ge a
  hb <| h _
#align not_is_bot not_isBot

@[simp]
theorem not_isTop [NoTopOrder α] (a : α) : ¬IsTop a := fun h =>
  let ⟨_, hb⟩ := exists_not_le a
  hb <| h _
#align not_is_top not_isTop

protected theorem IsBot.isMin (h : IsBot a) : IsMin a := fun b _ => h b
#align is_bot.is_min IsBot.isMin

protected theorem IsTop.isMax (h : IsTop a) : IsMax a := fun b _ => h b
#align is_top.is_max IsTop.isMax

@[simp]
theorem isBot_toDual_iff : IsBot (toDual a) ↔ IsTop a :=
  Iff.rfl
#align is_bot_to_dual_iff isBot_toDual_iff

@[simp]
theorem isTop_toDual_iff : IsTop (toDual a) ↔ IsBot a :=
  Iff.rfl
#align is_top_to_dual_iff isTop_toDual_iff

@[simp]
theorem isMin_toDual_iff : IsMin (toDual a) ↔ IsMax a :=
  Iff.rfl
#align is_min_to_dual_iff isMin_toDual_iff

@[simp]
theorem isMax_toDual_iff : IsMax (toDual a) ↔ IsMin a :=
  Iff.rfl
#align is_max_to_dual_iff isMax_toDual_iff

@[simp]
theorem isBot_ofDual_iff {a : αᵒᵈ} : IsBot (ofDual a) ↔ IsTop a :=
  Iff.rfl
#align is_bot_of_dual_iff isBot_ofDual_iff

@[simp]
theorem isTop_ofDual_iff {a : αᵒᵈ} : IsTop (ofDual a) ↔ IsBot a :=
  Iff.rfl
#align is_top_of_dual_iff isTop_ofDual_iff

@[simp]
theorem isMin_ofDual_iff {a : αᵒᵈ} : IsMin (ofDual a) ↔ IsMax a :=
  Iff.rfl
#align is_min_of_dual_iff isMin_ofDual_iff

@[simp]
theorem isMax_ofDual_iff {a : αᵒᵈ} : IsMax (ofDual a) ↔ IsMin a :=
  Iff.rfl
#align is_max_of_dual_iff isMax_ofDual_iff

alias ⟨_, IsTop.toDual⟩ := isBot_toDual_iff
#align is_top.to_dual IsTop.toDual

alias ⟨_, IsBot.toDual⟩ := isTop_toDual_iff
#align is_bot.to_dual IsBot.toDual

alias ⟨_, IsMax.toDual⟩ := isMin_toDual_iff
#align is_max.to_dual IsMax.toDual

alias ⟨_, IsMin.toDual⟩ := isMax_toDual_iff
#align is_min.to_dual IsMin.toDual

alias ⟨_, IsTop.ofDual⟩ := isBot_ofDual_iff
#align is_top.of_dual IsTop.ofDual

alias ⟨_, IsBot.ofDual⟩ := isTop_ofDual_iff
#align is_bot.of_dual IsBot.ofDual

alias ⟨_, IsMax.ofDual⟩ := isMin_ofDual_iff
#align is_max.of_dual IsMax.ofDual

alias ⟨_, IsMin.ofDual⟩ := isMax_ofDual_iff
#align is_min.of_dual IsMin.ofDual

end LE

section Preorder

variable [Preorder α] {a b : α}

theorem IsBot.mono (ha : IsBot a) (h : b ≤ a) : IsBot b := fun _ => h.trans <| ha _
#align is_bot.mono IsBot.mono

theorem IsTop.mono (ha : IsTop a) (h : a ≤ b) : IsTop b := fun _ => (ha _).trans h
#align is_top.mono IsTop.mono

theorem IsMin.mono (ha : IsMin a) (h : b ≤ a) : IsMin b := fun _ hc => h.trans <| ha <| hc.trans h
#align is_min.mono IsMin.mono

theorem IsMax.mono (ha : IsMax a) (h : a ≤ b) : IsMax b := fun _ hc => (ha <| h.trans hc).trans h
#align is_max.mono IsMax.mono

theorem IsMin.not_lt (h : IsMin a) : ¬b < a := fun hb => hb.not_le <| h hb.le
#align is_min.not_lt IsMin.not_lt

theorem IsMax.not_lt (h : IsMax a) : ¬a < b := fun hb => hb.not_le <| h hb.le
#align is_max.not_lt IsMax.not_lt

@[simp]
theorem not_isMin_of_lt (h : b < a) : ¬IsMin a := fun ha => ha.not_lt h
#align not_is_min_of_lt not_isMin_of_lt

@[simp]
theorem not_isMax_of_lt (h : a < b) : ¬IsMax a := fun ha => ha.not_lt h
#align not_is_max_of_lt not_isMax_of_lt

alias LT.lt.not_isMin := not_isMin_of_lt

alias LT.lt.not_isMax := not_isMax_of_lt

theorem isMin_iff_forall_not_lt : IsMin a ↔ ∀ b, ¬b < a :=
  ⟨fun h _ => h.not_lt, fun h _ hba => of_not_not fun hab => h _ <| hba.lt_of_not_le hab⟩
#align is_min_iff_forall_not_lt isMin_iff_forall_not_lt

theorem isMax_iff_forall_not_lt : IsMax a ↔ ∀ b, ¬a < b :=
  ⟨fun h _ => h.not_lt, fun h _ hba => of_not_not fun hab => h _ <| hba.lt_of_not_le hab⟩
#align is_max_iff_forall_not_lt isMax_iff_forall_not_lt

@[simp]
theorem not_isMin_iff : ¬IsMin a ↔ ∃ b, b < a := by
  simp [lt_iff_le_not_le, IsMin, not_forall, exists_prop]
#align not_is_min_iff not_isMin_iff

@[simp]
theorem not_isMax_iff : ¬IsMax a ↔ ∃ b, a < b := by
  simp [lt_iff_le_not_le, IsMax, not_forall, exists_prop]
#align not_is_max_iff not_isMax_iff

@[simp]
theorem not_isMin [NoMinOrder α] (a : α) : ¬IsMin a :=
  not_isMin_iff.2 <| exists_lt a
#align not_is_min not_isMin

@[simp]
theorem not_isMax [NoMaxOrder α] (a : α) : ¬IsMax a :=
  not_isMax_iff.2 <| exists_gt a
#align not_is_max not_isMax

namespace Subsingleton

variable [Subsingleton α]

protected theorem isBot (a : α) : IsBot a := fun _ => (Subsingleton.elim _ _).le
#align subsingleton.is_bot Subsingleton.isBot

protected theorem isTop (a : α) : IsTop a := fun _ => (Subsingleton.elim _ _).le
#align subsingleton.is_top Subsingleton.isTop

protected theorem isMin (a : α) : IsMin a :=
  (Subsingleton.isBot _).isMin
#align subsingleton.is_min Subsingleton.isMin

protected theorem isMax (a : α) : IsMax a :=
  (Subsingleton.isTop _).isMax
#align subsingleton.is_max Subsingleton.isMax

end Subsingleton

end Preorder

section PartialOrder

variable [PartialOrder α] {a b : α}

protected theorem IsMin.eq_of_le (ha : IsMin a) (h : b ≤ a) : b = a :=
  h.antisymm <| ha h
#align is_min.eq_of_le IsMin.eq_of_le

protected theorem IsMin.eq_of_ge (ha : IsMin a) (h : b ≤ a) : a = b :=
  h.antisymm' <| ha h
#align is_min.eq_of_ge IsMin.eq_of_ge

protected theorem IsMax.eq_of_le (ha : IsMax a) (h : a ≤ b) : a = b :=
  h.antisymm <| ha h
#align is_max.eq_of_le IsMax.eq_of_le

protected theorem IsMax.eq_of_ge (ha : IsMax a) (h : a ≤ b) : b = a :=
  h.antisymm' <| ha h
#align is_max.eq_of_ge IsMax.eq_of_ge

end PartialOrder

section Prod

variable [Preorder α] [Preorder β] {a a₁ a₂ : α} {b b₁ b₂ : β} {x y : α × β}

theorem IsBot.prod_mk (ha : IsBot a) (hb : IsBot b) : IsBot (a, b) := fun _ => ⟨ha _, hb _⟩
#align is_bot.prod_mk IsBot.prod_mk

theorem IsTop.prod_mk (ha : IsTop a) (hb : IsTop b) : IsTop (a, b) := fun _ => ⟨ha _, hb _⟩
#align is_top.prod_mk IsTop.prod_mk

theorem IsMin.prod_mk (ha : IsMin a) (hb : IsMin b) : IsMin (a, b) := fun _ hc => ⟨ha hc.1, hb hc.2⟩
#align is_min.prod_mk IsMin.prod_mk

theorem IsMax.prod_mk (ha : IsMax a) (hb : IsMax b) : IsMax (a, b) := fun _ hc => ⟨ha hc.1, hb hc.2⟩
#align is_max.prod_mk IsMax.prod_mk

theorem IsBot.fst (hx : IsBot x) : IsBot x.1 := fun c => (hx (c, x.2)).1
#align is_bot.fst IsBot.fst

theorem IsBot.snd (hx : IsBot x) : IsBot x.2 := fun c => (hx (x.1, c)).2
#align is_bot.snd IsBot.snd

theorem IsTop.fst (hx : IsTop x) : IsTop x.1 := fun c => (hx (c, x.2)).1
#align is_top.fst IsTop.fst

theorem IsTop.snd (hx : IsTop x) : IsTop x.2 := fun c => (hx (x.1, c)).2
#align is_top.snd IsTop.snd

theorem IsMin.fst (hx : IsMin x) : IsMin x.1 :=
  fun c hc => (hx <| show (c, x.2) ≤ x from (and_iff_left le_rfl).2 hc).1
#align is_min.fst IsMin.fst

theorem IsMin.snd (hx : IsMin x) : IsMin x.2 :=
  fun c hc => (hx <| show (x.1, c) ≤ x from (and_iff_right le_rfl).2 hc).2
#align is_min.snd IsMin.snd

theorem IsMax.fst (hx : IsMax x) : IsMax x.1 :=
  fun c hc => (hx <| show x ≤ (c, x.2) from (and_iff_left le_rfl).2 hc).1
#align is_max.fst IsMax.fst

theorem IsMax.snd (hx : IsMax x) : IsMax x.2 :=
  fun c hc => (hx <| show x ≤ (x.1, c) from (and_iff_right le_rfl).2 hc).2
#align is_max.snd IsMax.snd

theorem Prod.isBot_iff : IsBot x ↔ IsBot x.1 ∧ IsBot x.2 :=
  ⟨fun hx => ⟨hx.fst, hx.snd⟩, fun h => h.1.prod_mk h.2⟩
#align prod.is_bot_iff Prod.isBot_iff

theorem Prod.isTop_iff : IsTop x ↔ IsTop x.1 ∧ IsTop x.2 :=
  ⟨fun hx => ⟨hx.fst, hx.snd⟩, fun h => h.1.prod_mk h.2⟩
#align prod.is_top_iff Prod.isTop_iff

theorem Prod.isMin_iff : IsMin x ↔ IsMin x.1 ∧ IsMin x.2 :=
  ⟨fun hx => ⟨hx.fst, hx.snd⟩, fun h => h.1.prod_mk h.2⟩
#align prod.is_min_iff Prod.isMin_iff

theorem Prod.isMax_iff : IsMax x ↔ IsMax x.1 ∧ IsMax x.2 :=
  ⟨fun hx => ⟨hx.fst, hx.snd⟩, fun h => h.1.prod_mk h.2⟩
#align prod.is_max_iff Prod.isMax_iff

end Prod
