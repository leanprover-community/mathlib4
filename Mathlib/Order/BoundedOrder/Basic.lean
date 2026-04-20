/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Order.Max
public import Mathlib.Order.ULift
public import Mathlib.Tactic.ByCases
public import Mathlib.Tactic.Finiteness.Attr

/-!
# ⊤ and ⊥, bounded lattices and variants

This file defines top and bottom elements (greatest and least elements) of a type, the bounded
variants of different kinds of lattices, sets up the typeclass hierarchy between them and provides
instances for `Prop` and `fun`.

## Main declarations

* `<Top/Bot> α`: Typeclasses to declare the `⊤`/`⊥` notation.
* `Order<Top/Bot> α`: Order with a top/bottom element.
* `BoundedOrder α`: Order with a top and bottom element.

-/

@[expose] public section

assert_not_exists Monotone

universe u v

variable {α : Type u} {β : Type v}

/-! ### Top, bottom element -/

/-- An order is an `OrderTop` if it has a greatest element.
We state this using a data mixin, holding the value of `⊤` and the greatest element constraint. -/
class OrderTop (α : Type u) [LE α] extends Top α where
  /-- `⊤` is the greatest element -/
  le_top : ∀ a : α, a ≤ ⊤

/-- An order is an `OrderBot` if it has a least element.
We state this using a data mixin, holding the value of `⊥` and the least element constraint. -/
@[to_dual] class OrderBot (α : Type u) [LE α] extends Bot α where
  /-- `⊥` is the least element -/
  bot_le : ∀ a : α, ⊥ ≤ a

section OrderTop

/-- An order is (noncomputably) either an `OrderTop` or a `NoTopOrder`. Use as
`cases topOrderOrNoTopOrder α`. -/
@[to_dual /-- An order is (noncomputably) either an `OrderBot` or a `NoBotOrder`. Use as
`cases botOrderOrNoBotOrder α`. -/]
noncomputable def topOrderOrNoTopOrder (α : Type*) [LE α] : OrderTop α ⊕' NoTopOrder α := by
  by_cases! H : ∀ a : α, ∃ b, ¬b ≤ a
  · exact PSum.inr ⟨H⟩
  · letI : Top α := ⟨Classical.choose H⟩
    exact PSum.inl ⟨Classical.choose_spec H⟩

section ite

variable [Top α] {p : Prop} [Decidable p]

@[to_dual (attr := aesop (rule_sets := [finiteness]) unsafe 70% apply)]
theorem dite_ne_top {a : p → α} {b : ¬p → α} (ha : ∀ h, a h ≠ ⊤) (hb : ∀ h, b h ≠ ⊤) :
    (if h : p then a h else b h) ≠ ⊤ := by
  split <;> solve_by_elim

@[to_dual (attr := aesop (rule_sets := [finiteness]) unsafe 70% apply)]
theorem ite_ne_top {a b : α} (ha : p → a ≠ ⊤) (hb : ¬p → b ≠ ⊤) :
    (if p then a else b) ≠ ⊤ :=
  dite_ne_top ha hb

end ite

section LE

variable [LE α] [OrderTop α] {a : α}

@[to_dual (attr := simp) bot_le]
theorem le_top : a ≤ ⊤ :=
  OrderTop.le_top a

@[to_dual (attr := simp)]
theorem isTop_top : IsTop (⊤ : α) := fun _ => le_top

end LE

/-- A top element can be replaced with `⊤`.

Prefer `IsTop.eq_top` if `α` already has a top element. -/
@[to_dual (attr := elab_as_elim) /-- A bottom element can be replaced with `⊥`.

Prefer `IsBot.eq_bot` if `α` already has a bottom element. -/]
protected def IsTop.rec [LE α] {P : (x : α) → IsTop x → Sort*}
    (h : ∀ [OrderTop α], P ⊤ isTop_top) (x : α) (hx : IsTop x) : P x hx := by
  letI : OrderTop α := { top := x, le_top := hx }
  apply h

section Preorder

variable [Preorder α] [OrderTop α] {a b : α}

@[to_dual (attr := simp)]
theorem isMax_top : IsMax (⊤ : α) :=
  isTop_top.isMax

@[to_dual (attr := simp) not_lt_bot]
theorem not_top_lt : ¬⊤ < a :=
  isMax_top.not_lt

@[to_dual ne_bot_of_gt]
theorem ne_top_of_lt (h : a < b) : a ≠ ⊤ :=
  (h.trans_le le_top).ne

@[to_dual] alias LT.lt.ne_top := ne_top_of_lt

@[to_dual bot_lt_of_lt] theorem lt_top_of_lt (h : a < b) : a < ⊤ :=
  lt_of_lt_of_le h le_top

@[to_dual bot_lt] alias LT.lt.lt_top := lt_top_of_lt

attribute [aesop (rule_sets := [finiteness]) unsafe 20%] ne_top_of_lt
-- would have been better to implement this as a "safe" "forward" rule, why doesn't this work?
-- attribute [aesop (rule_sets := [finiteness]) safe forward] ne_top_of_lt

end Preorder

variable [PartialOrder α] [OrderTop α] [Preorder β] {a b : α}

@[to_dual (attr := simp)]
theorem isMax_iff_eq_top : IsMax a ↔ a = ⊤ :=
  ⟨fun h => h.eq_of_le le_top, fun h _ _ => h.symm ▸ le_top⟩

@[to_dual (attr := simp)]
theorem isTop_iff_eq_top : IsTop a ↔ a = ⊤ :=
  ⟨fun h => h.isMax.eq_of_le le_top, fun h _ => h.symm ▸ le_top⟩

@[to_dual]
theorem not_isMax_iff_ne_top : ¬IsMax a ↔ a ≠ ⊤ :=
  isMax_iff_eq_top.not

@[to_dual]
theorem not_isTop_iff_ne_top : ¬IsTop a ↔ a ≠ ⊤ :=
  isTop_iff_eq_top.not

@[to_dual]
alias ⟨IsMax.eq_top, _⟩ := isMax_iff_eq_top

@[to_dual]
alias ⟨IsTop.eq_top, _⟩ := isTop_iff_eq_top

@[to_dual (attr := simp) le_bot_iff]
theorem top_le_iff : ⊤ ≤ a ↔ a = ⊤ :=
  le_top.ge_iff_eq

-- This tells grind that to prove `a = ⊤` it suffices to prove `⊤ ≤ a`.
@[to_dual (attr := grind ←=, grind →)]
theorem top_unique (h : ⊤ ≤ a) : a = ⊤ :=
  le_top.antisymm h

@[to_dual]
theorem eq_top_iff : a = ⊤ ↔ ⊤ ≤ a :=
  top_le_iff.symm

@[to_dual]
theorem eq_top_mono (h : a ≤ b) (h₂ : a = ⊤) : b = ⊤ :=
  top_unique <| h₂ ▸ h

@[to_dual bot_lt_iff_ne_bot]
theorem lt_top_iff_ne_top : a < ⊤ ↔ a ≠ ⊤ :=
  le_top.lt_iff_ne

@[to_dual (attr := simp) not_bot_lt_iff]
theorem not_lt_top_iff : ¬a < ⊤ ↔ a = ⊤ :=
  lt_top_iff_ne_top.not_left

@[to_dual eq_bot_or_bot_lt]
theorem eq_top_or_lt_top (a : α) : a = ⊤ ∨ a < ⊤ :=
  le_top.eq_or_lt

@[aesop (rule_sets := [finiteness]) safe apply, to_dual bot_lt]
theorem Ne.lt_top (h : a ≠ ⊤) : a < ⊤ :=
  lt_top_iff_ne_top.mpr h

@[to_dual bot_lt']
theorem Ne.lt_top' (h : ⊤ ≠ a) : a < ⊤ :=
  h.symm.lt_top

@[to_dual]
theorem ne_top_of_le_ne_top (hb : b ≠ ⊤) (hab : a ≤ b) : a ≠ ⊤ :=
  (hab.trans_lt hb.lt_top).ne

@[to_dual]
lemma top_notMem_iff {s : Set α} : ⊤ ∉ s ↔ ∀ x ∈ s, x < ⊤ :=
  ⟨fun h x hx ↦ Ne.lt_top (fun hx' : x = ⊤ ↦ h (hx' ▸ hx)), fun h h₀ ↦ (h ⊤ h₀).false⟩

variable [Nontrivial α]

@[to_dual]
theorem not_isMin_top : ¬IsMin (⊤ : α) := fun h =>
  let ⟨_, ha⟩ := exists_ne (⊤ : α)
  ha <| top_le_iff.1 <| h le_top

end OrderTop

@[to_dual (reorder := H (x y))]
theorem OrderTop.ext_top {α} {hA : PartialOrder α} (A : OrderTop α) {hB : PartialOrder α}
    (B : OrderTop α) (H : ∀ x y : α, (haveI := hA; x ≤ y) ↔ x ≤ y) :
    (@Top.top α (@OrderTop.toTop α hA.toLE A)) = (@Top.top α (@OrderTop.toTop α hB.toLE B)) := by
  cases PartialOrder.ext H
  apply top_unique
  exact @le_top _ _ A _

namespace OrderDual

variable (α)

@[to_dual]
instance [h : Bot α] : Top αᵒᵈ :=
  ⟨h.bot⟩

@[to_dual]
instance [LE α] [h : OrderBot α] : OrderTop αᵒᵈ where
  le_top := h.bot_le

@[to_dual (attr := simp)] lemma ofDual_top [Bot α] : ofDual ⊤ = (⊥ : α) := rfl
@[to_dual (attr := simp)] lemma toDual_top [Top α] : toDual (⊤ : α) = ⊥ := rfl

@[to_dual (attr := simp)] lemma ofDual_eq_top [Top α] {a : αᵒᵈ} : ofDual a = ⊤ ↔ a = ⊥ := .rfl
@[to_dual (attr := simp)] lemma toDual_eq_top [Bot α] {a : α} : toDual a = ⊤ ↔ a = ⊥ := .rfl

end OrderDual

section OrderBot

variable [PartialOrder α] [OrderBot α] [Preorder β] {a b : α}

@[deprecated not_bot_lt_iff (since := "2025-12-03")]
theorem eq_bot_of_minimal (h : ∀ b, ¬b < a) : a = ⊥ :=
  (eq_bot_or_bot_lt a).resolve_right (h ⊥)

end OrderBot


/-! ### Bounded order -/


/-- A bounded order describes an order `(≤)` with a top and bottom element,
  denoted `⊤` and `⊥` respectively. -/
class BoundedOrder (α : Type u) [LE α] extends OrderTop α, OrderBot α

attribute [to_dual self (reorder := 3 4)] BoundedOrder.mk
attribute [to_dual existing] BoundedOrder.toOrderTop

instance OrderDual.instBoundedOrder (α : Type u) [LE α] [BoundedOrder α] : BoundedOrder αᵒᵈ where

section PartialOrder
variable [PartialOrder α]

@[to_dual]
instance OrderBot.instSubsingleton : Subsingleton (OrderBot α) where
  allEq := by rintro @⟨⟨a⟩, ha⟩ @⟨⟨b⟩, hb⟩; congr; exact le_antisymm (ha _) (hb _)

instance BoundedOrder.instSubsingleton : Subsingleton (BoundedOrder α) where
  allEq := by rintro ⟨⟩ ⟨⟩; congr <;> exact Subsingleton.elim _ _

end PartialOrder

/-! ### Function lattices -/

namespace Pi

variable {ι : Type*} {α' : ι → Type*}

@[to_dual]
instance [∀ i, Bot (α' i)] : Bot (∀ i, α' i) :=
  ⟨fun _ => ⊥⟩

@[to_dual (attr := simp)]
theorem bot_apply [∀ i, Bot (α' i)] (i : ι) : (⊥ : ∀ i, α' i) i = ⊥ :=
  rfl

@[to_dual (attr := push ←)]
theorem bot_def [∀ i, Bot (α' i)] : (⊥ : ∀ i, α' i) = fun _ => ⊥ :=
  rfl

@[to_dual (attr := simp)]
theorem bot_comp {α β γ : Type*} [Bot γ] (x : α → β) : (⊥ : β → γ) ∘ x = ⊥ := by
  rfl

@[to_dual]
instance instOrderBot [∀ i, LE (α' i)] [∀ i, OrderBot (α' i)] : OrderBot (∀ i, α' i) where
  bot_le _ := fun _ => bot_le

instance instBoundedOrder [∀ i, LE (α' i)] [∀ i, BoundedOrder (α' i)] :
    BoundedOrder (∀ i, α' i) where
  __ := (inferInstance : OrderTop (∀ i, α' i))
  __ := (inferInstance : OrderBot (∀ i, α' i))

end Pi

section Subsingleton

variable [PartialOrder α] [BoundedOrder α]

@[to_dual]
theorem eq_bot_of_bot_eq_top (hα : (⊥ : α) = ⊤) (x : α) : x = (⊥ : α) :=
  eq_bot_mono le_top (Eq.symm hα)

@[to_dual]
theorem eq_top_of_bot_eq_top (hα : (⊥ : α) = ⊤) (x : α) : x = (⊤ : α) :=
  eq_top_mono bot_le hα

theorem subsingleton_of_top_le_bot (h : (⊤ : α) ≤ (⊥ : α)) : Subsingleton α :=
  ⟨fun _ _ => le_antisymm
    (le_trans le_top <| le_trans h bot_le) (le_trans le_top <| le_trans h bot_le)⟩

@[to_dual]
theorem subsingleton_of_bot_eq_top (hα : (⊥ : α) = (⊤ : α)) : Subsingleton α :=
  subsingleton_of_top_le_bot (ge_of_eq hα)

@[to_dual]
theorem subsingleton_iff_bot_eq_top : (⊥ : α) = (⊤ : α) ↔ Subsingleton α :=
  ⟨subsingleton_of_bot_eq_top, fun _ => Subsingleton.elim ⊥ ⊤⟩

end Subsingleton

section lift

-- See note [reducible non-instances]
/-- Pullback an `OrderTop`. -/
@[to_dual (reorder := map_le (a b)) /-- Pullback an `OrderBot`. -/]
abbrev OrderTop.lift [LE α] [Top α] [LE β] [OrderTop β] (f : α → β)
    (map_le : ∀ a b, f a ≤ f b → a ≤ b) (map_top : f ⊤ = ⊤) : OrderTop α :=
  ⟨fun a =>
    map_le _ _ <| by
      rw [map_top]
      exact le_top _⟩

-- See note [reducible non-instances]
/-- Pullback a `BoundedOrder`. -/
@[to_dual self (reorder := 4 5, map_le (a b), map_top map_bot)]
abbrev BoundedOrder.lift [LE α] [Top α] [Bot α] [LE β] [BoundedOrder β] (f : α → β)
    (map_le : ∀ a b, f a ≤ f b → a ≤ b) (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) :
    BoundedOrder α where
  __ := OrderTop.lift f map_le map_top
  __ := OrderBot.lift f map_le map_bot

end lift

/-! ### Subtype, order dual, product lattices -/


namespace Subtype

variable {p : α → Prop}

-- See note [reducible non-instances]
/-- A subtype remains a `⊥`-order if the property holds at `⊥`. -/
@[to_dual /-- A subtype remains a `⊤`-order if the property holds at `⊤`. -/]
protected abbrev orderBot [LE α] [OrderBot α] (hbot : p ⊥) : OrderBot { x : α // p x } where
  bot := ⟨⊥, hbot⟩
  bot_le _ := bot_le

-- See note [reducible non-instances]
/-- A subtype remains a bounded order if the property holds at `⊥` and `⊤`. -/
@[to_dual self (reorder := hbot htop)]
protected abbrev boundedOrder [LE α] [BoundedOrder α] (hbot : p ⊥) (htop : p ⊤) :
    BoundedOrder (Subtype p) where
  __ := Subtype.orderTop htop
  __ := Subtype.orderBot hbot

variable [PartialOrder α]

@[to_dual (attr := simp)]
theorem mk_bot [OrderBot α] [OrderBot (Subtype p)] (hbot : p ⊥) : mk ⊥ hbot = ⊥ :=
  le_bot_iff.1 <| coe_le_coe.1 bot_le

@[to_dual]
theorem coe_bot [OrderBot α] [OrderBot (Subtype p)] (hbot : p ⊥) : ((⊥ : Subtype p) : α) = ⊥ :=
  congr_arg Subtype.val (mk_bot hbot).symm

@[to_dual (attr := simp)]
theorem coe_eq_bot_iff [OrderBot α] [OrderBot (Subtype p)] (hbot : p ⊥) {x : { x // p x }} :
    (x : α) = ⊥ ↔ x = ⊥ := by
  rw [← coe_bot hbot, Subtype.ext_iff]

@[to_dual (attr := simp)]
theorem mk_eq_bot_iff [OrderBot α] [OrderBot (Subtype p)] (hbot : p ⊥) {x : α} (hx : p x) :
    (⟨x, hx⟩ : Subtype p) = ⊥ ↔ x = ⊥ :=
  (coe_eq_bot_iff hbot).symm

end Subtype

namespace Prod

variable (α β)

@[to_dual]
instance instTop [Top α] [Top β] : Top (α × β) :=
  ⟨⟨⊤, ⊤⟩⟩

@[to_dual (attr := simp)] lemma fst_top [Top α] [Top β] : (⊤ : α × β).fst = ⊤ := rfl
@[to_dual (attr := simp)] lemma snd_top [Top α] [Top β] : (⊤ : α × β).snd = ⊤ := rfl

@[to_dual]
instance instOrderTop [LE α] [LE β] [OrderTop α] [OrderTop β] : OrderTop (α × β) where
  __ := (inferInstance : Top (α × β))
  le_top _ := ⟨le_top, le_top⟩

instance instBoundedOrder [LE α] [LE β] [BoundedOrder α] [BoundedOrder β] :
    BoundedOrder (α × β) where
  __ := (inferInstance : OrderTop (α × β))
  __ := (inferInstance : OrderBot (α × β))

end Prod

namespace ULift

@[to_dual]
instance [Top α] : Top (ULift.{v} α) where top := up ⊤

@[to_dual (attr := simp)] theorem up_top [Top α] : up (⊤ : α) = ⊤ := rfl
@[to_dual (attr := simp)] theorem down_top [Top α] : down (⊤ : ULift α) = ⊤ := rfl

@[to_dual]
instance [LE α] [OrderBot α] : OrderBot (ULift.{v} α) :=
  OrderBot.lift ULift.down (fun _ _ => down_le.mp) down_bot

instance [LE α] [BoundedOrder α] : BoundedOrder (ULift.{v} α) where

end ULift

section Nontrivial

variable [PartialOrder α] [BoundedOrder α] [Nontrivial α]

@[to_dual (attr := simp)]
theorem bot_ne_top : (⊥ : α) ≠ ⊤ := fun h => not_subsingleton _ <| subsingleton_of_bot_eq_top h

@[simp]
theorem bot_lt_top : (⊥ : α) < ⊤ :=
  lt_top_iff_ne_top.2 bot_ne_top

end Nontrivial

section Bool

open Bool

instance Bool.instBoundedOrder : BoundedOrder Bool where
  top := true
  le_top := Bool.le_true
  bot := false
  bot_le := Bool.false_le

@[simp]
theorem top_eq_true : ⊤ = true :=
  rfl

@[simp]
theorem bot_eq_false : ⊥ = false :=
  rfl

end Bool
