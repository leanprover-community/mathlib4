/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Order.Max
import Mathlib.Order.ULift
import Mathlib.Tactic.Push
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Util.AssertExists

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

assert_not_exists Monotone

universe u v

variable {α : Type u} {β : Type v}

/-! ### Top, bottom element -/

/-- An order is an `OrderTop` if it has a greatest element.
We state this using a data mixin, holding the value of `⊤` and the greatest element constraint. -/
class OrderTop (α : Type u) [LE α] extends Top α where
  /-- `⊤` is the greatest element -/
  le_top : ∀ a : α, a ≤ ⊤

section OrderTop

/-- An order is (noncomputably) either an `OrderTop` or a `NoTopOrder`. Use as
`casesI topOrderOrNoTopOrder α`. -/
noncomputable def topOrderOrNoTopOrder (α : Type*) [LE α] : OrderTop α ⊕' NoTopOrder α := by
  by_cases H : ∀ a : α, ∃ b, ¬b ≤ a
  · exact PSum.inr ⟨H⟩
  · push_neg at H
    letI : Top α := ⟨Classical.choose H⟩
    exact PSum.inl ⟨Classical.choose_spec H⟩

section LE

variable [LE α] [OrderTop α] {a : α}

@[simp]
theorem le_top : a ≤ ⊤ :=
  OrderTop.le_top a

@[simp]
theorem isTop_top : IsTop (⊤ : α) := fun _ => le_top

end LE

/-- A top element can be replaced with `⊤`.

Prefer `IsTop.eq_top` if `α` already has a top element. -/
@[elab_as_elim]
protected def IsTop.rec [LE α] {P : (x : α) → IsTop x → Sort*}
    (h : ∀ [OrderTop α], P ⊤ isTop_top) (x : α) (hx : IsTop x) : P x hx := by
  letI : OrderTop α := { top := x, le_top := hx }
  apply h

section Preorder

variable [Preorder α] [OrderTop α] {a b : α}

@[simp]
theorem isMax_top : IsMax (⊤ : α) :=
  isTop_top.isMax

@[simp]
theorem not_top_lt : ¬⊤ < a :=
  isMax_top.not_lt

theorem ne_top_of_lt (h : a < b) : a ≠ ⊤ :=
  (h.trans_le le_top).ne

alias LT.lt.ne_top := ne_top_of_lt

theorem lt_top_of_lt (h : a < b) : a < ⊤ :=
  lt_of_lt_of_le h le_top

alias LT.lt.lt_top := lt_top_of_lt

attribute [aesop (rule_sets := [finiteness]) unsafe 20%] ne_top_of_lt
-- would have been better to implement this as a "safe" "forward" rule, why doesn't this work?
-- attribute [aesop (rule_sets := [finiteness]) safe forward] ne_top_of_lt

end Preorder

variable [PartialOrder α] [OrderTop α] [Preorder β] {f : α → β} {a b : α}

@[simp]
theorem isMax_iff_eq_top : IsMax a ↔ a = ⊤ :=
  ⟨fun h => h.eq_of_le le_top, fun h _ _ => h.symm ▸ le_top⟩

@[simp]
theorem isTop_iff_eq_top : IsTop a ↔ a = ⊤ :=
  ⟨fun h => h.isMax.eq_of_le le_top, fun h _ => h.symm ▸ le_top⟩

theorem not_isMax_iff_ne_top : ¬IsMax a ↔ a ≠ ⊤ :=
  isMax_iff_eq_top.not

theorem not_isTop_iff_ne_top : ¬IsTop a ↔ a ≠ ⊤ :=
  isTop_iff_eq_top.not

alias ⟨IsMax.eq_top, _⟩ := isMax_iff_eq_top

alias ⟨IsTop.eq_top, _⟩ := isTop_iff_eq_top

@[simp]
theorem top_le_iff : ⊤ ≤ a ↔ a = ⊤ :=
  le_top.ge_iff_eq

theorem top_unique (h : ⊤ ≤ a) : a = ⊤ :=
  le_top.antisymm h

theorem eq_top_iff : a = ⊤ ↔ ⊤ ≤ a :=
  top_le_iff.symm

theorem eq_top_mono (h : a ≤ b) (h₂ : a = ⊤) : b = ⊤ :=
  top_unique <| h₂ ▸ h

theorem lt_top_iff_ne_top : a < ⊤ ↔ a ≠ ⊤ :=
  le_top.lt_iff_ne

@[simp]
theorem not_lt_top_iff : ¬a < ⊤ ↔ a = ⊤ :=
  lt_top_iff_ne_top.not_left

theorem eq_top_or_lt_top (a : α) : a = ⊤ ∨ a < ⊤ :=
  le_top.eq_or_lt

@[aesop (rule_sets := [finiteness]) safe apply]
theorem Ne.lt_top (h : a ≠ ⊤) : a < ⊤ :=
  lt_top_iff_ne_top.mpr h

theorem Ne.lt_top' (h : ⊤ ≠ a) : a < ⊤ :=
  h.symm.lt_top

theorem ne_top_of_le_ne_top (hb : b ≠ ⊤) (hab : a ≤ b) : a ≠ ⊤ :=
  (hab.trans_lt hb.lt_top).ne

lemma top_notMem_iff {s : Set α} : ⊤ ∉ s ↔ ∀ x ∈ s, x < ⊤ :=
  ⟨fun h x hx ↦ Ne.lt_top (fun hx' : x = ⊤ ↦ h (hx' ▸ hx)), fun h h₀ ↦ (h ⊤ h₀).false⟩

@[deprecated (since := "2025-05-23")] alias top_not_mem_iff := top_notMem_iff

variable [Nontrivial α]

theorem not_isMin_top : ¬IsMin (⊤ : α) := fun h =>
  let ⟨_, ha⟩ := exists_ne (⊤ : α)
  ha <| top_le_iff.1 <| h le_top

end OrderTop

theorem OrderTop.ext_top {α} {hA : PartialOrder α} (A : OrderTop α) {hB : PartialOrder α}
    (B : OrderTop α) (H : ∀ x y : α, (haveI := hA; x ≤ y) ↔ x ≤ y) :
    (@Top.top α (@OrderTop.toTop α hA.toLE A)) = (@Top.top α (@OrderTop.toTop α hB.toLE B)) := by
  cases PartialOrder.ext H
  apply top_unique
  exact @le_top _ _ A _

/-- An order is an `OrderBot` if it has a least element.
We state this using a data mixin, holding the value of `⊥` and the least element constraint. -/
class OrderBot (α : Type u) [LE α] extends Bot α where
  /-- `⊥` is the least element -/
  bot_le : ∀ a : α, ⊥ ≤ a

section OrderBot

/-- An order is (noncomputably) either an `OrderBot` or a `NoBotOrder`. Use as
`casesI botOrderOrNoBotOrder α`. -/
noncomputable def botOrderOrNoBotOrder (α : Type*) [LE α] : OrderBot α ⊕' NoBotOrder α := by
  by_cases H : ∀ a : α, ∃ b, ¬a ≤ b
  · exact PSum.inr ⟨H⟩
  · push_neg at H
    letI : Bot α := ⟨Classical.choose H⟩
    exact PSum.inl ⟨Classical.choose_spec H⟩

section LE

variable [LE α] [OrderBot α] {a : α}

@[simp]
theorem bot_le : ⊥ ≤ a :=
  OrderBot.bot_le a

@[simp]
theorem isBot_bot : IsBot (⊥ : α) := fun _ => bot_le

end LE

/-- A bottom element can be replaced with `⊥`.

Prefer `IsBot.eq_bot` if `α` already has a bottom element. -/
@[elab_as_elim]
protected def IsBot.rec [LE α] {P : (x : α) → IsBot x → Sort*}
    (h : ∀ [OrderBot α], P ⊥ isBot_bot) (x : α) (hx : IsBot x) : P x hx := by
  letI : OrderBot α := { bot := x, bot_le := hx }
  apply h

namespace OrderDual

variable (α)

instance instTop [Bot α] : Top αᵒᵈ :=
  ⟨(⊥ : α)⟩

instance instBot [Top α] : Bot αᵒᵈ :=
  ⟨(⊤ : α)⟩

instance instOrderTop [LE α] [OrderBot α] : OrderTop αᵒᵈ where
  __ := inferInstanceAs (Top αᵒᵈ)
  le_top := @bot_le α _ _

instance instOrderBot [LE α] [OrderTop α] : OrderBot αᵒᵈ where
  __ := inferInstanceAs (Bot αᵒᵈ)
  bot_le := @le_top α _ _

@[simp]
theorem ofDual_bot [Top α] : ofDual ⊥ = (⊤ : α) :=
  rfl

@[simp]
theorem ofDual_top [Bot α] : ofDual ⊤ = (⊥ : α) :=
  rfl

@[simp]
theorem toDual_bot [Bot α] : toDual (⊥ : α) = ⊤ :=
  rfl

@[simp]
theorem toDual_top [Top α] : toDual (⊤ : α) = ⊥ :=
  rfl

end OrderDual

section Preorder

variable [Preorder α] [OrderBot α] {a b : α}

@[simp]
theorem isMin_bot : IsMin (⊥ : α) :=
  isBot_bot.isMin

@[simp]
theorem not_lt_bot : ¬a < ⊥ :=
  isMin_bot.not_lt

theorem ne_bot_of_gt (h : a < b) : b ≠ ⊥ :=
  (bot_le.trans_lt h).ne'

alias LT.lt.ne_bot := ne_bot_of_gt

theorem bot_lt_of_lt (h : a < b) : ⊥ < b :=
  lt_of_le_of_lt bot_le h

alias LT.lt.bot_lt := bot_lt_of_lt

end Preorder

variable [PartialOrder α] [OrderBot α] [Preorder β] {f : α → β} {a b : α}

@[simp]
theorem isMin_iff_eq_bot : IsMin a ↔ a = ⊥ :=
  ⟨fun h => h.eq_of_ge bot_le, fun h _ _ => h.symm ▸ bot_le⟩

@[simp]
theorem isBot_iff_eq_bot : IsBot a ↔ a = ⊥ :=
  ⟨fun h => h.isMin.eq_of_ge bot_le, fun h _ => h.symm ▸ bot_le⟩

theorem not_isMin_iff_ne_bot : ¬IsMin a ↔ a ≠ ⊥ :=
  isMin_iff_eq_bot.not

theorem not_isBot_iff_ne_bot : ¬IsBot a ↔ a ≠ ⊥ :=
  isBot_iff_eq_bot.not

alias ⟨IsMin.eq_bot, _⟩ := isMin_iff_eq_bot

alias ⟨IsBot.eq_bot, _⟩ := isBot_iff_eq_bot

@[simp]
theorem le_bot_iff : a ≤ ⊥ ↔ a = ⊥ :=
  bot_le.ge_iff_eq'

theorem bot_unique (h : a ≤ ⊥) : a = ⊥ :=
  h.antisymm bot_le

theorem eq_bot_iff : a = ⊥ ↔ a ≤ ⊥ :=
  le_bot_iff.symm

theorem eq_bot_mono (h : a ≤ b) (h₂ : b = ⊥) : a = ⊥ :=
  bot_unique <| h₂ ▸ h

theorem bot_lt_iff_ne_bot : ⊥ < a ↔ a ≠ ⊥ :=
  bot_le.lt_iff_ne.trans ne_comm

@[simp]
theorem not_bot_lt_iff : ¬⊥ < a ↔ a = ⊥ :=
  bot_lt_iff_ne_bot.not_left

theorem eq_bot_or_bot_lt (a : α) : a = ⊥ ∨ ⊥ < a :=
  bot_le.eq_or_lt'

theorem eq_bot_of_minimal (h : ∀ b, ¬b < a) : a = ⊥ :=
  (eq_bot_or_bot_lt a).resolve_right (h ⊥)

theorem Ne.bot_lt (h : a ≠ ⊥) : ⊥ < a :=
  bot_lt_iff_ne_bot.mpr h

theorem Ne.bot_lt' (h : ⊥ ≠ a) : ⊥ < a :=
  h.symm.bot_lt

theorem ne_bot_of_le_ne_bot (hb : b ≠ ⊥) (hab : b ≤ a) : a ≠ ⊥ :=
  (hb.bot_lt.trans_le hab).ne'

lemma bot_notMem_iff {s : Set α} : ⊥ ∉ s ↔ ∀ x ∈ s, ⊥ < x :=
  top_notMem_iff (α := αᵒᵈ)

@[deprecated (since := "2025-05-23")] alias bot_not_mem_iff := bot_notMem_iff

variable [Nontrivial α]

theorem not_isMax_bot : ¬IsMax (⊥ : α) :=
  @not_isMin_top αᵒᵈ _ _ _

end OrderBot

theorem OrderBot.ext_bot {α} {hA : PartialOrder α} (A : OrderBot α) {hB : PartialOrder α}
    (B : OrderBot α) (H : ∀ x y : α, (haveI := hA; x ≤ y) ↔ x ≤ y) :
    (@Bot.bot α (@OrderBot.toBot α hA.toLE A)) = (@Bot.bot α (@OrderBot.toBot α hB.toLE B)) := by
  cases PartialOrder.ext H
  apply bot_unique
  exact @bot_le _ _ A _

/-! ### Bounded order -/


/-- A bounded order describes an order `(≤)` with a top and bottom element,
  denoted `⊤` and `⊥` respectively. -/
class BoundedOrder (α : Type u) [LE α] extends OrderTop α, OrderBot α

instance OrderDual.instBoundedOrder (α : Type u) [LE α] [BoundedOrder α] : BoundedOrder αᵒᵈ where
  __ := inferInstanceAs (OrderTop αᵒᵈ)
  __ := inferInstanceAs (OrderBot αᵒᵈ)

section PartialOrder
variable [PartialOrder α]

instance OrderBot.instSubsingleton : Subsingleton (OrderBot α) where
  allEq := by rintro @⟨⟨a⟩, ha⟩ @⟨⟨b⟩, hb⟩; congr; exact le_antisymm (ha _) (hb _)

instance OrderTop.instSubsingleton : Subsingleton (OrderTop α) where
  allEq := by rintro @⟨⟨a⟩, ha⟩ @⟨⟨b⟩, hb⟩; congr; exact le_antisymm (hb _) (ha _)

instance BoundedOrder.instSubsingleton : Subsingleton (BoundedOrder α) where
  allEq := by rintro ⟨⟩ ⟨⟩; congr <;> exact Subsingleton.elim _ _

end PartialOrder

/-! ### Function lattices -/

namespace Pi

variable {ι : Type*} {α' : ι → Type*}

instance [∀ i, Bot (α' i)] : Bot (∀ i, α' i) :=
  ⟨fun _ => ⊥⟩

@[simp]
theorem bot_apply [∀ i, Bot (α' i)] (i : ι) : (⊥ : ∀ i, α' i) i = ⊥ :=
  rfl

@[push ←]
theorem bot_def [∀ i, Bot (α' i)] : (⊥ : ∀ i, α' i) = fun _ => ⊥ :=
  rfl

@[simp]
theorem bot_comp {α β γ : Type*} [Bot γ] (x : α → β) : (⊥ : β → γ) ∘ x = ⊥ := by
  rfl

instance [∀ i, Top (α' i)] : Top (∀ i, α' i) :=
  ⟨fun _ => ⊤⟩

@[simp]
theorem top_apply [∀ i, Top (α' i)] (i : ι) : (⊤ : ∀ i, α' i) i = ⊤ :=
  rfl

@[push ←]
theorem top_def [∀ i, Top (α' i)] : (⊤ : ∀ i, α' i) = fun _ => ⊤ :=
  rfl

@[simp]
theorem top_comp {α β γ : Type*} [Top γ] (x : α → β) : (⊤ : β → γ) ∘ x = ⊤ := by
  rfl

instance instOrderTop [∀ i, LE (α' i)] [∀ i, OrderTop (α' i)] : OrderTop (∀ i, α' i) where
  le_top _ := fun _ => le_top

instance instOrderBot [∀ i, LE (α' i)] [∀ i, OrderBot (α' i)] : OrderBot (∀ i, α' i) where
  bot_le _ := fun _ => bot_le

instance instBoundedOrder [∀ i, LE (α' i)] [∀ i, BoundedOrder (α' i)] :
    BoundedOrder (∀ i, α' i) where
  __ := inferInstanceAs (OrderTop (∀ i, α' i))
  __ := inferInstanceAs (OrderBot (∀ i, α' i))

end Pi

section Subsingleton

variable [PartialOrder α] [BoundedOrder α]

theorem eq_bot_of_bot_eq_top (hα : (⊥ : α) = ⊤) (x : α) : x = (⊥ : α) :=
  eq_bot_mono le_top (Eq.symm hα)

theorem eq_top_of_bot_eq_top (hα : (⊥ : α) = ⊤) (x : α) : x = (⊤ : α) :=
  eq_top_mono bot_le hα

theorem subsingleton_of_top_le_bot (h : (⊤ : α) ≤ (⊥ : α)) : Subsingleton α :=
  ⟨fun _ _ => le_antisymm
    (le_trans le_top <| le_trans h bot_le) (le_trans le_top <| le_trans h bot_le)⟩

theorem subsingleton_of_bot_eq_top (hα : (⊥ : α) = (⊤ : α)) : Subsingleton α :=
  subsingleton_of_top_le_bot (ge_of_eq hα)

theorem subsingleton_iff_bot_eq_top : (⊥ : α) = (⊤ : α) ↔ Subsingleton α :=
  ⟨subsingleton_of_bot_eq_top, fun _ => Subsingleton.elim ⊥ ⊤⟩

end Subsingleton

section lift

-- See note [reducible non-instances]
/-- Pullback an `OrderTop`. -/
abbrev OrderTop.lift [LE α] [Top α] [LE β] [OrderTop β] (f : α → β)
    (map_le : ∀ a b, f a ≤ f b → a ≤ b) (map_top : f ⊤ = ⊤) : OrderTop α :=
  ⟨fun a =>
    map_le _ _ <| by
      rw [map_top]
      exact le_top _⟩

-- See note [reducible non-instances]
/-- Pullback an `OrderBot`. -/
abbrev OrderBot.lift [LE α] [Bot α] [LE β] [OrderBot β] (f : α → β)
    (map_le : ∀ a b, f a ≤ f b → a ≤ b) (map_bot : f ⊥ = ⊥) : OrderBot α :=
  ⟨fun a =>
    map_le _ _ <| by
      rw [map_bot]
      exact bot_le _⟩

-- See note [reducible non-instances]
/-- Pullback a `BoundedOrder`. -/
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
protected abbrev orderBot [LE α] [OrderBot α] (hbot : p ⊥) : OrderBot { x : α // p x } where
  bot := ⟨⊥, hbot⟩
  bot_le _ := bot_le

-- See note [reducible non-instances]
/-- A subtype remains a `⊤`-order if the property holds at `⊤`. -/
protected abbrev orderTop [LE α] [OrderTop α] (htop : p ⊤) : OrderTop { x : α // p x } where
  top := ⟨⊤, htop⟩
  le_top _ := le_top

-- See note [reducible non-instances]
/-- A subtype remains a bounded order if the property holds at `⊥` and `⊤`. -/
protected abbrev boundedOrder [LE α] [BoundedOrder α] (hbot : p ⊥) (htop : p ⊤) :
    BoundedOrder (Subtype p) where
  __ := Subtype.orderTop htop
  __ := Subtype.orderBot hbot

variable [PartialOrder α]

@[simp]
theorem mk_bot [OrderBot α] [OrderBot (Subtype p)] (hbot : p ⊥) : mk ⊥ hbot = ⊥ :=
  le_bot_iff.1 <| coe_le_coe.1 bot_le

@[simp]
theorem mk_top [OrderTop α] [OrderTop (Subtype p)] (htop : p ⊤) : mk ⊤ htop = ⊤ :=
  top_le_iff.1 <| coe_le_coe.1 le_top

theorem coe_bot [OrderBot α] [OrderBot (Subtype p)] (hbot : p ⊥) : ((⊥ : Subtype p) : α) = ⊥ :=
  congr_arg Subtype.val (mk_bot hbot).symm

theorem coe_top [OrderTop α] [OrderTop (Subtype p)] (htop : p ⊤) : ((⊤ : Subtype p) : α) = ⊤ :=
  congr_arg Subtype.val (mk_top htop).symm

@[simp]
theorem coe_eq_bot_iff [OrderBot α] [OrderBot (Subtype p)] (hbot : p ⊥) {x : { x // p x }} :
    (x : α) = ⊥ ↔ x = ⊥ := by
  rw [← coe_bot hbot, Subtype.ext_iff]

@[simp]
theorem coe_eq_top_iff [OrderTop α] [OrderTop (Subtype p)] (htop : p ⊤) {x : { x // p x }} :
    (x : α) = ⊤ ↔ x = ⊤ := by
  rw [← coe_top htop, Subtype.ext_iff]

@[simp]
theorem mk_eq_bot_iff [OrderBot α] [OrderBot (Subtype p)] (hbot : p ⊥) {x : α} (hx : p x) :
    (⟨x, hx⟩ : Subtype p) = ⊥ ↔ x = ⊥ :=
  (coe_eq_bot_iff hbot).symm

@[simp]
theorem mk_eq_top_iff [OrderTop α] [OrderTop (Subtype p)] (htop : p ⊤) {x : α} (hx : p x) :
    (⟨x, hx⟩ : Subtype p) = ⊤ ↔ x = ⊤ :=
  (coe_eq_top_iff htop).symm

end Subtype

namespace Prod

variable (α β)

instance instTop [Top α] [Top β] : Top (α × β) :=
  ⟨⟨⊤, ⊤⟩⟩

instance instBot [Bot α] [Bot β] : Bot (α × β) :=
  ⟨⟨⊥, ⊥⟩⟩

@[simp] lemma fst_top [Top α] [Top β] : (⊤ : α × β).fst = ⊤ := rfl
@[simp] lemma snd_top [Top α] [Top β] : (⊤ : α × β).snd = ⊤ := rfl
@[simp] lemma fst_bot [Bot α] [Bot β] : (⊥ : α × β).fst = ⊥ := rfl
@[simp] lemma snd_bot [Bot α] [Bot β] : (⊥ : α × β).snd = ⊥ := rfl

instance instOrderTop [LE α] [LE β] [OrderTop α] [OrderTop β] : OrderTop (α × β) where
  __ := inferInstanceAs (Top (α × β))
  le_top _ := ⟨le_top, le_top⟩

instance instOrderBot [LE α] [LE β] [OrderBot α] [OrderBot β] : OrderBot (α × β) where
  __ := inferInstanceAs (Bot (α × β))
  bot_le _ := ⟨bot_le, bot_le⟩

instance instBoundedOrder [LE α] [LE β] [BoundedOrder α] [BoundedOrder β] :
    BoundedOrder (α × β) where
  __ := inferInstanceAs (OrderTop (α × β))
  __ := inferInstanceAs (OrderBot (α × β))

end Prod

namespace ULift

instance [Top α] : Top (ULift.{v} α) where top := up ⊤

@[simp] theorem up_top [Top α] : up (⊤ : α) = ⊤ := rfl
@[simp] theorem down_top [Top α] : down (⊤ : ULift α) = ⊤ := rfl

instance [Bot α] : Bot (ULift.{v} α) where bot := up ⊥

@[simp] theorem up_bot [Bot α] : up (⊥ : α) = ⊥ := rfl
@[simp] theorem down_bot [Bot α] : down (⊥ : ULift α) = ⊥ := rfl

instance [LE α] [OrderBot α] : OrderBot (ULift.{v} α) :=
  OrderBot.lift ULift.down (fun _ _ => down_le.mp) down_bot

instance [LE α] [OrderTop α] : OrderTop (ULift.{v} α) :=
  OrderTop.lift ULift.down (fun _ _ => down_le.mp) down_top

instance [LE α] [BoundedOrder α] : BoundedOrder (ULift.{v} α) where

end ULift

section Nontrivial

variable [PartialOrder α] [BoundedOrder α] [Nontrivial α]

@[simp]
theorem bot_ne_top : (⊥ : α) ≠ ⊤ := fun h => not_subsingleton _ <| subsingleton_of_bot_eq_top h

@[simp]
theorem top_ne_bot : (⊤ : α) ≠ ⊥ :=
  bot_ne_top.symm

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
