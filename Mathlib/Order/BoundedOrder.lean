/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathbin.Order.Lattice
import Mathbin.Data.Option.Basic

/-!
# ⊤ and ⊥, bounded lattices and variants

This file defines top and bottom elements (greatest and least elements) of a type, the bounded
variants of different kinds of lattices, sets up the typeclass hierarchy between them and provides
instances for `Prop` and `fun`.

## Main declarations

* `has_<top/bot> α`: Typeclasses to declare the `⊤`/`⊥` notation.
* `order_<top/bot> α`: Order with a top/bottom element.
* `bounded_order α`: Order with a top and bottom element.
* `with_<top/bot> α`: Equips `option α` with the order on `α` plus `none` as the top/bottom element.
* `is_compl x y`: In a bounded lattice, predicate for "`x` is a complement of `y`". Note that in a
  non distributive lattice, an element can have several complements.
* `complemented_lattice α`: Typeclass stating that any element of a lattice has a complement.

## Common lattices

* Distributive lattices with a bottom element. Notated by `[distrib_lattice α] [order_bot α]`
  It captures the properties of `disjoint` that are common to `generalized_boolean_algebra` and
  `distrib_lattice` when `order_bot`.
* Bounded and distributive lattice. Notated by `[distrib_lattice α] [bounded_order α]`.
  Typical examples include `Prop` and `set α`.
-/


open Function OrderDual

universe u v

variable {α : Type u} {β : Type v} {γ δ : Type _}

/-! ### Top, bottom element -/


/-- Typeclass for the `⊤` (`\top`) notation -/
@[notation_class]
class HasTop (α : Type u) where
  top : α
#align has_top HasTop

/-- Typeclass for the `⊥` (`\bot`) notation -/
@[notation_class]
class HasBot (α : Type u) where
  bot : α
#align has_bot HasBot

-- mathport name: «expr⊤»
notation "⊤" => HasTop.top

-- mathport name: «expr⊥»
notation "⊥" => HasBot.bot

instance (priority := 100) has_top_nonempty (α : Type u) [HasTop α] : Nonempty α :=
  ⟨⊤⟩
#align has_top_nonempty has_top_nonempty

instance (priority := 100) has_bot_nonempty (α : Type u) [HasBot α] : Nonempty α :=
  ⟨⊥⟩
#align has_bot_nonempty has_bot_nonempty

attribute [match_pattern] HasBot.bot HasTop.top

/-- An order is an `order_top` if it has a greatest element.
We state this using a data mixin, holding the value of `⊤` and the greatest element constraint. -/
class OrderTop (α : Type u) [LE α] extends HasTop α where
  le_top : ∀ a : α, a ≤ ⊤
#align order_top OrderTop

section OrderTop

/-- An order is (noncomputably) either an `order_top` or a `no_order_top`. Use as
`casesI bot_order_or_no_bot_order α`. -/
noncomputable def topOrderOrNoTopOrder (α : Type _) [LE α] : PSum (OrderTop α) (NoTopOrder α) := by
  by_cases H : ∀ a : α, ∃ b, ¬b ≤ a
  · exact PSum.inr ⟨H⟩
    
  · push_neg  at H
    exact PSum.inl ⟨_, Classical.choose_spec H⟩
    
#align top_order_or_no_top_order topOrderOrNoTopOrder

section LE

variable [LE α] [OrderTop α] {a : α}

@[simp]
theorem le_top : a ≤ ⊤ :=
  OrderTop.le_top a
#align le_top le_top

@[simp]
theorem is_top_top : IsTop (⊤ : α) := fun _ => le_top
#align is_top_top is_top_top

end LE

section Preorder

variable [Preorder α] [OrderTop α] {a b : α}

@[simp]
theorem is_max_top : IsMax (⊤ : α) :=
  is_top_top.IsMax
#align is_max_top is_max_top

@[simp]
theorem not_top_lt : ¬⊤ < a :=
  is_max_top.not_lt
#align not_top_lt not_top_lt

theorem ne_top_of_lt (h : a < b) : a ≠ ⊤ :=
  (h.trans_le le_top).Ne
#align ne_top_of_lt ne_top_of_lt

alias ne_top_of_lt ← LT.lt.ne_top

end Preorder

variable [PartialOrder α] [OrderTop α] [Preorder β] {f : α → β} {a b : α}

@[simp]
theorem is_max_iff_eq_top : IsMax a ↔ a = ⊤ :=
  ⟨fun h => h.eq_of_le le_top, fun h b _ => h.symm ▸ le_top⟩
#align is_max_iff_eq_top is_max_iff_eq_top

@[simp]
theorem is_top_iff_eq_top : IsTop a ↔ a = ⊤ :=
  ⟨fun h => h.IsMax.eq_of_le le_top, fun h b => h.symm ▸ le_top⟩
#align is_top_iff_eq_top is_top_iff_eq_top

theorem not_is_max_iff_ne_top : ¬IsMax a ↔ a ≠ ⊤ :=
  is_max_iff_eq_top.Not
#align not_is_max_iff_ne_top not_is_max_iff_ne_top

theorem not_is_top_iff_ne_top : ¬IsTop a ↔ a ≠ ⊤ :=
  is_top_iff_eq_top.Not
#align not_is_top_iff_ne_top not_is_top_iff_ne_top

alias is_max_iff_eq_top ↔ IsMax.eq_top _

alias is_top_iff_eq_top ↔ IsTop.eq_top _

@[simp]
theorem top_le_iff : ⊤ ≤ a ↔ a = ⊤ :=
  le_top.le_iff_eq.trans eq_comm
#align top_le_iff top_le_iff

theorem top_unique (h : ⊤ ≤ a) : a = ⊤ :=
  le_top.antisymm h
#align top_unique top_unique

theorem eq_top_iff : a = ⊤ ↔ ⊤ ≤ a :=
  top_le_iff.symm
#align eq_top_iff eq_top_iff

theorem eq_top_mono (h : a ≤ b) (h₂ : a = ⊤) : b = ⊤ :=
  top_unique <| h₂ ▸ h
#align eq_top_mono eq_top_mono

theorem lt_top_iff_ne_top : a < ⊤ ↔ a ≠ ⊤ :=
  le_top.lt_iff_ne
#align lt_top_iff_ne_top lt_top_iff_ne_top

@[simp]
theorem not_lt_top_iff : ¬a < ⊤ ↔ a = ⊤ :=
  lt_top_iff_ne_top.not_left
#align not_lt_top_iff not_lt_top_iff

theorem eq_top_or_lt_top (a : α) : a = ⊤ ∨ a < ⊤ :=
  le_top.eq_or_lt
#align eq_top_or_lt_top eq_top_or_lt_top

theorem Ne.lt_top (h : a ≠ ⊤) : a < ⊤ :=
  lt_top_iff_ne_top.mpr h
#align ne.lt_top Ne.lt_top

theorem Ne.lt_top' (h : ⊤ ≠ a) : a < ⊤ :=
  h.symm.lt_top
#align ne.lt_top' Ne.lt_top'

theorem ne_top_of_le_ne_top (hb : b ≠ ⊤) (hab : a ≤ b) : a ≠ ⊤ :=
  (hab.trans_lt hb.lt_top).Ne
#align ne_top_of_le_ne_top ne_top_of_le_ne_top

theorem StrictMono.apply_eq_top_iff (hf : StrictMono f) : f a = f ⊤ ↔ a = ⊤ :=
  ⟨fun h => not_lt_top_iff.1 fun ha => (hf ha).Ne h, congr_arg _⟩
#align strict_mono.apply_eq_top_iff StrictMono.apply_eq_top_iff

theorem StrictAnti.apply_eq_top_iff (hf : StrictAnti f) : f a = f ⊤ ↔ a = ⊤ :=
  ⟨fun h => not_lt_top_iff.1 fun ha => (hf ha).ne' h, congr_arg _⟩
#align strict_anti.apply_eq_top_iff StrictAnti.apply_eq_top_iff

variable [Nontrivial α]

theorem not_is_min_top : ¬IsMin (⊤ : α) := fun h =>
  let ⟨a, ha⟩ := exists_ne (⊤ : α)
  ha <| top_le_iff.1 <| h le_top
#align not_is_min_top not_is_min_top

end OrderTop

theorem StrictMono.maximal_preimage_top [LinearOrder α] [Preorder β] [OrderTop β] {f : α → β} (H : StrictMono f) {a}
    (h_top : f a = ⊤) (x : α) : x ≤ a :=
  H.maximal_of_maximal_image
    (fun p => by
      rw [h_top]
      exact le_top)
    x
#align strict_mono.maximal_preimage_top StrictMono.maximal_preimage_top

theorem OrderTop.ext_top {α} {hA : PartialOrder α} (A : OrderTop α) {hB : PartialOrder α} (B : OrderTop α)
    (H :
      ∀ x y : α,
        (haveI := hA
          x ≤ y) ↔
          x ≤ y) :
    (haveI := A
        ⊤ :
        α) =
      ⊤ :=
  top_unique <| by rw [← H] <;> apply le_top
#align order_top.ext_top OrderTop.ext_top

theorem OrderTop.ext {α} [PartialOrder α] {A B : OrderTop α} : A = B := by
  have tt := OrderTop.ext_top A B fun _ _ => Iff.rfl
  cases' A with _ ha
  cases' B with _ hb
  congr
  exact le_antisymm (hb _) (ha _)
#align order_top.ext OrderTop.ext

/-- An order is an `order_bot` if it has a least element.
We state this using a data mixin, holding the value of `⊥` and the least element constraint. -/
class OrderBot (α : Type u) [LE α] extends HasBot α where
  bot_le : ∀ a : α, ⊥ ≤ a
#align order_bot OrderBot

section OrderBot

/-- An order is (noncomputably) either an `order_bot` or a `no_order_bot`. Use as
`casesI bot_order_or_no_bot_order α`. -/
noncomputable def botOrderOrNoBotOrder (α : Type _) [LE α] : PSum (OrderBot α) (NoBotOrder α) := by
  by_cases H : ∀ a : α, ∃ b, ¬a ≤ b
  · exact PSum.inr ⟨H⟩
    
  · push_neg  at H
    exact PSum.inl ⟨_, Classical.choose_spec H⟩
    
#align bot_order_or_no_bot_order botOrderOrNoBotOrder

section LE

variable [LE α] [OrderBot α] {a : α}

@[simp]
theorem bot_le : ⊥ ≤ a :=
  OrderBot.bot_le a
#align bot_le bot_le

@[simp]
theorem is_bot_bot : IsBot (⊥ : α) := fun _ => bot_le
#align is_bot_bot is_bot_bot

end LE

namespace OrderDual

variable (α)

instance [HasBot α] : HasTop αᵒᵈ :=
  ⟨(⊥ : α)⟩

instance [HasTop α] : HasBot αᵒᵈ :=
  ⟨(⊤ : α)⟩

instance [LE α] [OrderBot α] : OrderTop αᵒᵈ :=
  { OrderDual.hasTop α with le_top := @bot_le α _ _ }

instance [LE α] [OrderTop α] : OrderBot αᵒᵈ :=
  { OrderDual.hasBot α with bot_le := @le_top α _ _ }

@[simp]
theorem of_dual_bot [HasTop α] : ofDual ⊥ = (⊤ : α) :=
  rfl
#align order_dual.of_dual_bot OrderDual.of_dual_bot

@[simp]
theorem of_dual_top [HasBot α] : ofDual ⊤ = (⊥ : α) :=
  rfl
#align order_dual.of_dual_top OrderDual.of_dual_top

@[simp]
theorem to_dual_bot [HasBot α] : toDual (⊥ : α) = ⊤ :=
  rfl
#align order_dual.to_dual_bot OrderDual.to_dual_bot

@[simp]
theorem to_dual_top [HasTop α] : toDual (⊤ : α) = ⊥ :=
  rfl
#align order_dual.to_dual_top OrderDual.to_dual_top

end OrderDual

section Preorder

variable [Preorder α] [OrderBot α] {a b : α}

@[simp]
theorem is_min_bot : IsMin (⊥ : α) :=
  is_bot_bot.IsMin
#align is_min_bot is_min_bot

@[simp]
theorem not_lt_bot : ¬a < ⊥ :=
  is_min_bot.not_lt
#align not_lt_bot not_lt_bot

theorem ne_bot_of_gt (h : a < b) : b ≠ ⊥ :=
  (bot_le.trans_lt h).ne'
#align ne_bot_of_gt ne_bot_of_gt

alias ne_bot_of_gt ← LT.lt.ne_bot

end Preorder

variable [PartialOrder α] [OrderBot α] [Preorder β] {f : α → β} {a b : α}

@[simp]
theorem is_min_iff_eq_bot : IsMin a ↔ a = ⊥ :=
  ⟨fun h => h.eq_of_ge bot_le, fun h b _ => h.symm ▸ bot_le⟩
#align is_min_iff_eq_bot is_min_iff_eq_bot

@[simp]
theorem is_bot_iff_eq_bot : IsBot a ↔ a = ⊥ :=
  ⟨fun h => h.IsMin.eq_of_ge bot_le, fun h b => h.symm ▸ bot_le⟩
#align is_bot_iff_eq_bot is_bot_iff_eq_bot

theorem not_is_min_iff_ne_bot : ¬IsMin a ↔ a ≠ ⊥ :=
  is_min_iff_eq_bot.Not
#align not_is_min_iff_ne_bot not_is_min_iff_ne_bot

theorem not_is_bot_iff_ne_bot : ¬IsBot a ↔ a ≠ ⊥ :=
  is_bot_iff_eq_bot.Not
#align not_is_bot_iff_ne_bot not_is_bot_iff_ne_bot

alias is_min_iff_eq_bot ↔ IsMin.eq_bot _

alias is_bot_iff_eq_bot ↔ IsBot.eq_bot _

@[simp]
theorem le_bot_iff : a ≤ ⊥ ↔ a = ⊥ :=
  bot_le.le_iff_eq
#align le_bot_iff le_bot_iff

theorem bot_unique (h : a ≤ ⊥) : a = ⊥ :=
  h.antisymm bot_le
#align bot_unique bot_unique

theorem eq_bot_iff : a = ⊥ ↔ a ≤ ⊥ :=
  le_bot_iff.symm
#align eq_bot_iff eq_bot_iff

theorem eq_bot_mono (h : a ≤ b) (h₂ : b = ⊥) : a = ⊥ :=
  bot_unique <| h₂ ▸ h
#align eq_bot_mono eq_bot_mono

theorem bot_lt_iff_ne_bot : ⊥ < a ↔ a ≠ ⊥ :=
  bot_le.lt_iff_ne.trans ne_comm
#align bot_lt_iff_ne_bot bot_lt_iff_ne_bot

@[simp]
theorem not_bot_lt_iff : ¬⊥ < a ↔ a = ⊥ :=
  bot_lt_iff_ne_bot.not_left
#align not_bot_lt_iff not_bot_lt_iff

theorem eq_bot_or_bot_lt (a : α) : a = ⊥ ∨ ⊥ < a :=
  bot_le.eq_or_gt
#align eq_bot_or_bot_lt eq_bot_or_bot_lt

theorem eq_bot_of_minimal (h : ∀ b, ¬b < a) : a = ⊥ :=
  (eq_bot_or_bot_lt a).resolve_right (h ⊥)
#align eq_bot_of_minimal eq_bot_of_minimal

theorem Ne.bot_lt (h : a ≠ ⊥) : ⊥ < a :=
  bot_lt_iff_ne_bot.mpr h
#align ne.bot_lt Ne.bot_lt

theorem Ne.bot_lt' (h : ⊥ ≠ a) : ⊥ < a :=
  h.symm.bot_lt
#align ne.bot_lt' Ne.bot_lt'

theorem ne_bot_of_le_ne_bot (hb : b ≠ ⊥) (hab : b ≤ a) : a ≠ ⊥ :=
  (hb.bot_lt.trans_le hab).ne'
#align ne_bot_of_le_ne_bot ne_bot_of_le_ne_bot

theorem StrictMono.apply_eq_bot_iff (hf : StrictMono f) : f a = f ⊥ ↔ a = ⊥ :=
  hf.dual.apply_eq_top_iff
#align strict_mono.apply_eq_bot_iff StrictMono.apply_eq_bot_iff

theorem StrictAnti.apply_eq_bot_iff (hf : StrictAnti f) : f a = f ⊥ ↔ a = ⊥ :=
  hf.dual.apply_eq_top_iff
#align strict_anti.apply_eq_bot_iff StrictAnti.apply_eq_bot_iff

variable [Nontrivial α]

theorem not_is_max_bot : ¬IsMax (⊥ : α) :=
  @not_is_min_top αᵒᵈ _ _ _
#align not_is_max_bot not_is_max_bot

end OrderBot

theorem StrictMono.minimal_preimage_bot [LinearOrder α] [PartialOrder β] [OrderBot β] {f : α → β} (H : StrictMono f) {a}
    (h_bot : f a = ⊥) (x : α) : a ≤ x :=
  H.minimal_of_minimal_image
    (fun p => by
      rw [h_bot]
      exact bot_le)
    x
#align strict_mono.minimal_preimage_bot StrictMono.minimal_preimage_bot

theorem OrderBot.ext_bot {α} {hA : PartialOrder α} (A : OrderBot α) {hB : PartialOrder α} (B : OrderBot α)
    (H :
      ∀ x y : α,
        (haveI := hA
          x ≤ y) ↔
          x ≤ y) :
    (haveI := A
        ⊥ :
        α) =
      ⊥ :=
  bot_unique <| by rw [← H] <;> apply bot_le
#align order_bot.ext_bot OrderBot.ext_bot

theorem OrderBot.ext {α} [PartialOrder α] {A B : OrderBot α} : A = B := by
  have tt := OrderBot.ext_bot A B fun _ _ => Iff.rfl
  cases' A with a ha
  cases' B with b hb
  congr
  exact le_antisymm (ha _) (hb _)
#align order_bot.ext OrderBot.ext

section SemilatticeSupTop

variable [SemilatticeSup α] [OrderTop α] {a : α}

@[simp]
theorem top_sup_eq : ⊤ ⊔ a = ⊤ :=
  sup_of_le_left le_top
#align top_sup_eq top_sup_eq

@[simp]
theorem sup_top_eq : a ⊔ ⊤ = ⊤ :=
  sup_of_le_right le_top
#align sup_top_eq sup_top_eq

end SemilatticeSupTop

section SemilatticeSupBot

variable [SemilatticeSup α] [OrderBot α] {a b : α}

@[simp]
theorem bot_sup_eq : ⊥ ⊔ a = a :=
  sup_of_le_right bot_le
#align bot_sup_eq bot_sup_eq

@[simp]
theorem sup_bot_eq : a ⊔ ⊥ = a :=
  sup_of_le_left bot_le
#align sup_bot_eq sup_bot_eq

@[simp]
theorem sup_eq_bot_iff : a ⊔ b = ⊥ ↔ a = ⊥ ∧ b = ⊥ := by rw [eq_bot_iff, sup_le_iff] <;> simp
#align sup_eq_bot_iff sup_eq_bot_iff

end SemilatticeSupBot

section SemilatticeInfTop

variable [SemilatticeInf α] [OrderTop α] {a b : α}

@[simp]
theorem top_inf_eq : ⊤ ⊓ a = a :=
  inf_of_le_right le_top
#align top_inf_eq top_inf_eq

@[simp]
theorem inf_top_eq : a ⊓ ⊤ = a :=
  inf_of_le_left le_top
#align inf_top_eq inf_top_eq

@[simp]
theorem inf_eq_top_iff : a ⊓ b = ⊤ ↔ a = ⊤ ∧ b = ⊤ :=
  @sup_eq_bot_iff αᵒᵈ _ _ _ _
#align inf_eq_top_iff inf_eq_top_iff

end SemilatticeInfTop

section SemilatticeInfBot

variable [SemilatticeInf α] [OrderBot α] {a : α}

@[simp]
theorem bot_inf_eq : ⊥ ⊓ a = ⊥ :=
  inf_of_le_left bot_le
#align bot_inf_eq bot_inf_eq

@[simp]
theorem inf_bot_eq : a ⊓ ⊥ = ⊥ :=
  inf_of_le_right bot_le
#align inf_bot_eq inf_bot_eq

end SemilatticeInfBot

/-! ### Bounded order -/


/-- A bounded order describes an order `(≤)` with a top and bottom element,
  denoted `⊤` and `⊥` respectively. -/
class BoundedOrder (α : Type u) [LE α] extends OrderTop α, OrderBot α
#align bounded_order BoundedOrder

instance (α : Type u) [LE α] [BoundedOrder α] : BoundedOrder αᵒᵈ :=
  { OrderDual.orderTop α, OrderDual.orderBot α with }

theorem BoundedOrder.ext {α} [PartialOrder α] {A B : BoundedOrder α} : A = B := by
  have ht : @BoundedOrder.toOrderTop α _ A = @BoundedOrder.toOrderTop α _ B := OrderTop.ext
  have hb : @BoundedOrder.toOrderBot α _ A = @BoundedOrder.toOrderBot α _ B := OrderBot.ext
  cases A
  cases B
  injection ht with h
  injection hb with h'
  convert rfl
  · exact h.symm
    
  · exact h'.symm
    
#align bounded_order.ext BoundedOrder.ext

/-- Propositions form a distributive lattice. -/
instance PropCat.distribLattice : DistribLattice Prop :=
  { PropCat.partialOrder with sup := Or, le_sup_left := @Or.inl, le_sup_right := @Or.inr,
    sup_le := fun a b c => Or.ndrec, inf := And, inf_le_left := @And.left, inf_le_right := @And.right,
    le_inf := fun a b c Hab Hac Ha => And.intro (Hab Ha) (Hac Ha), le_sup_inf := fun a b c => or_and_left.2 }
#align Prop.distrib_lattice PropCat.distribLattice

/-- Propositions form a bounded order. -/
instance PropCat.boundedOrder : BoundedOrder Prop where
  top := True
  le_top a Ha := True.intro
  bot := False
  bot_le := @False.elim
#align Prop.bounded_order PropCat.boundedOrder

theorem PropCat.bot_eq_false : (⊥ : Prop) = False :=
  rfl
#align Prop.bot_eq_false PropCat.bot_eq_false

theorem PropCat.top_eq_true : (⊤ : Prop) = True :=
  rfl
#align Prop.top_eq_true PropCat.top_eq_true

instance PropCat.le_is_total : IsTotal Prop (· ≤ ·) :=
  ⟨fun p q => by
    change (p → q) ∨ (q → p)
    tauto!⟩
#align Prop.le_is_total PropCat.le_is_total

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [(Command.noncomputable "noncomputable")] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `PropCat.linearOrder [])]
      (Command.declSig [] (Term.typeSpec ":" (Term.app `LinearOrder [(Term.prop "Prop")])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.«tactic_<;>_»
            (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
            "<;>"
            (Tactic.exact "exact" (Term.app `Lattice.toLinearOrder [(Term.prop "Prop")])))])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.«tactic_<;>_»
           (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
           "<;>"
           (Tactic.exact "exact" (Term.app `Lattice.toLinearOrder [(Term.prop "Prop")])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
       "<;>"
       (Tactic.exact "exact" (Term.app `Lattice.toLinearOrder [(Term.prop "Prop")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `Lattice.toLinearOrder [(Term.prop "Prop")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Lattice.toLinearOrder [(Term.prop "Prop")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.prop', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.prop', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.prop "Prop")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Lattice.toLinearOrder
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.skip', expected 'Lean.Parser.Tactic.tacticSeq'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
noncomputable instance PropCat.linearOrder : LinearOrder Prop := by skip <;> exact Lattice.toLinearOrder Prop
#align Prop.linear_order PropCat.linearOrder

@[simp]
theorem sup_Prop_eq : (· ⊔ ·) = (· ∨ ·) :=
  rfl
#align sup_Prop_eq sup_Prop_eq

@[simp]
theorem inf_Prop_eq : (· ⊓ ·) = (· ∧ ·) :=
  rfl
#align inf_Prop_eq inf_Prop_eq

section Logic

/-!
#### In this section we prove some properties about monotone and antitone operations on `Prop`
-/


section Preorder

variable [Preorder α]

theorem monotone_and {p q : α → Prop} (m_p : Monotone p) (m_q : Monotone q) : Monotone fun x => p x ∧ q x :=
  fun a b h => And.imp (m_p h) (m_q h)
#align monotone_and monotone_and

-- Note: by finish [monotone] doesn't work
theorem monotone_or {p q : α → Prop} (m_p : Monotone p) (m_q : Monotone q) : Monotone fun x => p x ∨ q x := fun a b h =>
  Or.imp (m_p h) (m_q h)
#align monotone_or monotone_or

theorem monotone_le {x : α} : Monotone ((· ≤ ·) x) := fun y z h' h => h.trans h'
#align monotone_le monotone_le

theorem monotone_lt {x : α} : Monotone ((· < ·) x) := fun y z h' h => h.trans_le h'
#align monotone_lt monotone_lt

theorem antitone_le {x : α} : Antitone (· ≤ x) := fun y z h' h => h'.trans h
#align antitone_le antitone_le

theorem antitone_lt {x : α} : Antitone (· < x) := fun y z h' h => h'.trans_lt h
#align antitone_lt antitone_lt

theorem Monotone.forall {P : β → α → Prop} (hP : ∀ x, Monotone (P x)) : Monotone fun y => ∀ x, P x y :=
  fun y y' hy h x => hP x hy <| h x
#align monotone.forall Monotone.forall

theorem Antitone.forall {P : β → α → Prop} (hP : ∀ x, Antitone (P x)) : Antitone fun y => ∀ x, P x y :=
  fun y y' hy h x => hP x hy (h x)
#align antitone.forall Antitone.forall

theorem Monotone.ball {P : β → α → Prop} {s : Set β} (hP : ∀ x ∈ s, Monotone (P x)) :
    Monotone fun y => ∀ x ∈ s, P x y := fun y y' hy h x hx => hP x hx hy (h x hx)
#align monotone.ball Monotone.ball

theorem Antitone.ball {P : β → α → Prop} {s : Set β} (hP : ∀ x ∈ s, Antitone (P x)) :
    Antitone fun y => ∀ x ∈ s, P x y := fun y y' hy h x hx => hP x hx hy (h x hx)
#align antitone.ball Antitone.ball

end Preorder

section SemilatticeSup

variable [SemilatticeSup α]

theorem exists_ge_and_iff_exists {P : α → Prop} {x₀ : α} (hP : Monotone P) : (∃ x, x₀ ≤ x ∧ P x) ↔ ∃ x, P x :=
  ⟨fun h => h.imp fun x h => h.2, fun ⟨x, hx⟩ => ⟨x ⊔ x₀, le_sup_right, hP le_sup_left hx⟩⟩
#align exists_ge_and_iff_exists exists_ge_and_iff_exists

end SemilatticeSup

section SemilatticeInf

variable [SemilatticeInf α]

theorem exists_le_and_iff_exists {P : α → Prop} {x₀ : α} (hP : Antitone P) : (∃ x, x ≤ x₀ ∧ P x) ↔ ∃ x, P x :=
  exists_ge_and_iff_exists hP.dual_left
#align exists_le_and_iff_exists exists_le_and_iff_exists

end SemilatticeInf

end Logic

/-! ### Function lattices -/


namespace Pi

variable {ι : Type _} {α' : ι → Type _}

instance [∀ i, HasBot (α' i)] : HasBot (∀ i, α' i) :=
  ⟨fun i => ⊥⟩

@[simp]
theorem bot_apply [∀ i, HasBot (α' i)] (i : ι) : (⊥ : ∀ i, α' i) i = ⊥ :=
  rfl
#align pi.bot_apply Pi.bot_apply

theorem bot_def [∀ i, HasBot (α' i)] : (⊥ : ∀ i, α' i) = fun i => ⊥ :=
  rfl
#align pi.bot_def Pi.bot_def

instance [∀ i, HasTop (α' i)] : HasTop (∀ i, α' i) :=
  ⟨fun i => ⊤⟩

@[simp]
theorem top_apply [∀ i, HasTop (α' i)] (i : ι) : (⊤ : ∀ i, α' i) i = ⊤ :=
  rfl
#align pi.top_apply Pi.top_apply

theorem top_def [∀ i, HasTop (α' i)] : (⊤ : ∀ i, α' i) = fun i => ⊤ :=
  rfl
#align pi.top_def Pi.top_def

instance [∀ i, LE (α' i)] [∀ i, OrderTop (α' i)] : OrderTop (∀ i, α' i) :=
  { Pi.hasTop with le_top := fun _ _ => le_top }

instance [∀ i, LE (α' i)] [∀ i, OrderBot (α' i)] : OrderBot (∀ i, α' i) :=
  { Pi.hasBot with bot_le := fun _ _ => bot_le }

instance [∀ i, LE (α' i)] [∀ i, BoundedOrder (α' i)] : BoundedOrder (∀ i, α' i) :=
  { Pi.orderTop, Pi.orderBot with }

end Pi

section Subsingleton

variable [PartialOrder α] [BoundedOrder α]

theorem eq_bot_of_bot_eq_top (hα : (⊥ : α) = ⊤) (x : α) : x = (⊥ : α) :=
  eq_bot_mono le_top (Eq.symm hα)
#align eq_bot_of_bot_eq_top eq_bot_of_bot_eq_top

theorem eq_top_of_bot_eq_top (hα : (⊥ : α) = ⊤) (x : α) : x = (⊤ : α) :=
  eq_top_mono bot_le hα
#align eq_top_of_bot_eq_top eq_top_of_bot_eq_top

theorem subsingleton_of_top_le_bot (h : (⊤ : α) ≤ (⊥ : α)) : Subsingleton α :=
  ⟨fun a b => le_antisymm (le_trans le_top <| le_trans h bot_le) (le_trans le_top <| le_trans h bot_le)⟩
#align subsingleton_of_top_le_bot subsingleton_of_top_le_bot

theorem subsingleton_of_bot_eq_top (hα : (⊥ : α) = (⊤ : α)) : Subsingleton α :=
  subsingleton_of_top_le_bot (ge_of_eq hα)
#align subsingleton_of_bot_eq_top subsingleton_of_bot_eq_top

theorem subsingleton_iff_bot_eq_top : (⊥ : α) = (⊤ : α) ↔ Subsingleton α :=
  ⟨subsingleton_of_bot_eq_top, fun h => Subsingleton.elim ⊥ ⊤⟩
#align subsingleton_iff_bot_eq_top subsingleton_iff_bot_eq_top

end Subsingleton

section lift

-- See note [reducible non-instances]
/-- Pullback an `order_top`. -/
@[reducible]
def OrderTop.lift [LE α] [HasTop α] [LE β] [OrderTop β] (f : α → β) (map_le : ∀ a b, f a ≤ f b → a ≤ b)
    (map_top : f ⊤ = ⊤) : OrderTop α :=
  ⟨⊤, fun a =>
    map_le _ _ <| by
      rw [map_top]
      exact le_top⟩
#align order_top.lift OrderTop.lift

-- See note [reducible non-instances]
/-- Pullback an `order_bot`. -/
@[reducible]
def OrderBot.lift [LE α] [HasBot α] [LE β] [OrderBot β] (f : α → β) (map_le : ∀ a b, f a ≤ f b → a ≤ b)
    (map_bot : f ⊥ = ⊥) : OrderBot α :=
  ⟨⊥, fun a =>
    map_le _ _ <| by
      rw [map_bot]
      exact bot_le⟩
#align order_bot.lift OrderBot.lift

-- See note [reducible non-instances]
/-- Pullback a `bounded_order`. -/
@[reducible]
def BoundedOrder.lift [LE α] [HasTop α] [HasBot α] [LE β] [BoundedOrder β] (f : α → β)
    (map_le : ∀ a b, f a ≤ f b → a ≤ b) (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) : BoundedOrder α :=
  { OrderTop.lift f map_le map_top, OrderBot.lift f map_le map_bot with }
#align bounded_order.lift BoundedOrder.lift

end lift

/-! ### `with_bot`, `with_top` -/


/-- Attach `⊥` to a type. -/
def WithBot (α : Type _) :=
  Option α
#align with_bot WithBot

namespace WithBot

variable {a b : α}

unsafe instance [has_to_format α] :
    has_to_format (WithBot α) where to_format x :=
    match x with
    | none => "⊥"
    | some x => to_fmt x

instance [Repr α] : Repr (WithBot α) :=
  ⟨fun o =>
    match o with
    | none => "⊥"
    | some a => "↑" ++ repr a⟩

instance : CoeTC α (WithBot α) :=
  ⟨some⟩

instance : HasBot (WithBot α) :=
  ⟨none⟩

unsafe instance {α : Type} [reflected _ α] [has_reflect α] : has_reflect (WithBot α)
  | ⊥ => q(⊥)
  | (a : α) => q((coe : α → WithBot α)).subst q(a)

instance : Inhabited (WithBot α) :=
  ⟨⊥⟩

theorem coe_injective : Injective (coe : α → WithBot α) :=
  Option.some_injective _
#align with_bot.coe_injective WithBot.coe_injective

@[norm_cast]
theorem coe_inj : (a : WithBot α) = b ↔ a = b :=
  Option.some_inj
#align with_bot.coe_inj WithBot.coe_inj

protected theorem forall {p : WithBot α → Prop} : (∀ x, p x) ↔ p ⊥ ∧ ∀ x : α, p x :=
  Option.forall
#align with_bot.forall WithBot.forall

protected theorem exists {p : WithBot α → Prop} : (∃ x, p x) ↔ p ⊥ ∨ ∃ x : α, p x :=
  Option.exists
#align with_bot.exists WithBot.exists

theorem none_eq_bot : (none : WithBot α) = (⊥ : WithBot α) :=
  rfl
#align with_bot.none_eq_bot WithBot.none_eq_bot

theorem some_eq_coe (a : α) : (some a : WithBot α) = (↑a : WithBot α) :=
  rfl
#align with_bot.some_eq_coe WithBot.some_eq_coe

@[simp]
theorem bot_ne_coe : ⊥ ≠ (a : WithBot α) :=
  fun.
#align with_bot.bot_ne_coe WithBot.bot_ne_coe

@[simp]
theorem coe_ne_bot : (a : WithBot α) ≠ ⊥ :=
  fun.
#align with_bot.coe_ne_bot WithBot.coe_ne_bot

/-- Recursor for `with_bot` using the preferred forms `⊥` and `↑a`. -/
@[elab_as_elim]
def recBotCoe {C : WithBot α → Sort _} (h₁ : C ⊥) (h₂ : ∀ a : α, C a) : ∀ n : WithBot α, C n :=
  Option.rec h₁ h₂
#align with_bot.rec_bot_coe WithBot.recBotCoe

@[simp]
theorem rec_bot_coe_bot {C : WithBot α → Sort _} (d : C ⊥) (f : ∀ a : α, C a) : @recBotCoe _ C d f ⊥ = d :=
  rfl
#align with_bot.rec_bot_coe_bot WithBot.rec_bot_coe_bot

@[simp]
theorem rec_bot_coe_coe {C : WithBot α → Sort _} (d : C ⊥) (f : ∀ a : α, C a) (x : α) : @recBotCoe _ C d f ↑x = f x :=
  rfl
#align with_bot.rec_bot_coe_coe WithBot.rec_bot_coe_coe

/-- Specialization of `option.get_or_else` to values in `with_bot α` that respects API boundaries.
-/
def unbot' (d : α) (x : WithBot α) : α :=
  recBotCoe d id x
#align with_bot.unbot' WithBot.unbot'

@[simp]
theorem unbot'_bot {α} (d : α) : unbot' d ⊥ = d :=
  rfl
#align with_bot.unbot'_bot WithBot.unbot'_bot

@[simp]
theorem unbot'_coe {α} (d x : α) : unbot' d x = x :=
  rfl
#align with_bot.unbot'_coe WithBot.unbot'_coe

@[norm_cast]
theorem coe_eq_coe : (a : WithBot α) = b ↔ a = b :=
  Option.some_inj
#align with_bot.coe_eq_coe WithBot.coe_eq_coe

/-- Lift a map `f : α → β` to `with_bot α → with_bot β`. Implemented using `option.map`. -/
def map (f : α → β) : WithBot α → WithBot β :=
  Option.map f
#align with_bot.map WithBot.map

@[simp]
theorem map_bot (f : α → β) : map f ⊥ = ⊥ :=
  rfl
#align with_bot.map_bot WithBot.map_bot

@[simp]
theorem map_coe (f : α → β) (a : α) : map f a = f a :=
  rfl
#align with_bot.map_coe WithBot.map_coe

theorem map_comm {f₁ : α → β} {f₂ : α → γ} {g₁ : β → δ} {g₂ : γ → δ} (h : g₁ ∘ f₁ = g₂ ∘ f₂) (a : α) :
    map g₁ (map f₁ a) = map g₂ (map f₂ a) :=
  Option.map_comm h _
#align with_bot.map_comm WithBot.map_comm

theorem ne_bot_iff_exists {x : WithBot α} : x ≠ ⊥ ↔ ∃ a : α, ↑a = x :=
  Option.ne_none_iff_exists
#align with_bot.ne_bot_iff_exists WithBot.ne_bot_iff_exists

/-- Deconstruct a `x : with_bot α` to the underlying value in `α`, given a proof that `x ≠ ⊥`. -/
def unbot : ∀ x : WithBot α, x ≠ ⊥ → α
  | ⊥, h => absurd rfl h
  | some x, h => x
#align with_bot.unbot WithBot.unbot

@[simp]
theorem coe_unbot (x : WithBot α) (h : x ≠ ⊥) : (x.unbot h : WithBot α) = x := by
  cases x
  simpa using h
  rfl
#align with_bot.coe_unbot WithBot.coe_unbot

@[simp]
theorem unbot_coe (x : α) (h : (x : WithBot α) ≠ ⊥ := coe_ne_bot) : (x : WithBot α).unbot h = x :=
  rfl
#align with_bot.unbot_coe WithBot.unbot_coe

instance canLift : CanLift (WithBot α) α coe fun r => r ≠ ⊥ where prf x h := ⟨x.unbot h, coe_unbot _ _⟩
#align with_bot.can_lift WithBot.canLift

section LE

variable [LE α]

instance (priority := 10) : LE (WithBot α) :=
  ⟨fun o₁ o₂ : Option α => ∀ a ∈ o₁, ∃ b ∈ o₂, a ≤ b⟩

@[simp]
theorem some_le_some : @LE.le (WithBot α) _ (some a) (some b) ↔ a ≤ b := by simp [(· ≤ ·)]
#align with_bot.some_le_some WithBot.some_le_some

@[simp, norm_cast]
theorem coe_le_coe : (a : WithBot α) ≤ b ↔ a ≤ b :=
  some_le_some
#align with_bot.coe_le_coe WithBot.coe_le_coe

@[simp]
theorem none_le {a : WithBot α} : @LE.le (WithBot α) _ none a := fun b h => Option.noConfusion h
#align with_bot.none_le WithBot.none_le

instance : OrderBot (WithBot α) :=
  { WithBot.hasBot with bot_le := fun a => none_le }

instance [OrderTop α] : OrderTop (WithBot α) where
  top := some ⊤
  le_top o a ha := by cases ha <;> exact ⟨_, rfl, le_top⟩

instance [OrderTop α] : BoundedOrder (WithBot α) :=
  { WithBot.orderTop, WithBot.orderBot with }

theorem not_coe_le_bot (a : α) : ¬(a : WithBot α) ≤ ⊥ := fun h =>
  let ⟨b, hb, _⟩ := h _ rfl
  Option.not_mem_none _ hb
#align with_bot.not_coe_le_bot WithBot.not_coe_le_bot

theorem coe_le : ∀ {o : Option α}, b ∈ o → ((a : WithBot α) ≤ o ↔ a ≤ b)
  | _, rfl => coe_le_coe
#align with_bot.coe_le WithBot.coe_le

theorem coe_le_iff : ∀ {x : WithBot α}, ↑a ≤ x ↔ ∃ b : α, x = b ∧ a ≤ b
  | some a => by simp [some_eq_coe, coe_eq_coe]
  | none => iff_of_false (not_coe_le_bot _) <| by simp [none_eq_bot]
#align with_bot.coe_le_iff WithBot.coe_le_iff

theorem le_coe_iff : ∀ {x : WithBot α}, x ≤ b ↔ ∀ a, x = ↑a → a ≤ b
  | some b => by simp [some_eq_coe, coe_eq_coe]
  | none => by simp [none_eq_bot]
#align with_bot.le_coe_iff WithBot.le_coe_iff

protected theorem _root_.is_max.with_bot (h : IsMax a) : IsMax (a : WithBot α)
  | none, _ => bot_le
  | some b, hb => some_le_some.2 <| h <| some_le_some.1 hb
#align with_bot._root_.is_max.with_bot with_bot._root_.is_max.with_bot

end LE

section LT

variable [LT α]

instance (priority := 10) : LT (WithBot α) :=
  ⟨fun o₁ o₂ : Option α => ∃ b ∈ o₂, ∀ a ∈ o₁, a < b⟩

@[simp]
theorem some_lt_some : @LT.lt (WithBot α) _ (some a) (some b) ↔ a < b := by simp [(· < ·)]
#align with_bot.some_lt_some WithBot.some_lt_some

@[simp, norm_cast]
theorem coe_lt_coe : (a : WithBot α) < b ↔ a < b :=
  some_lt_some
#align with_bot.coe_lt_coe WithBot.coe_lt_coe

@[simp]
theorem none_lt_some (a : α) : @LT.lt (WithBot α) _ none (some a) :=
  ⟨a, rfl, fun b hb => (Option.not_mem_none _ hb).elim⟩
#align with_bot.none_lt_some WithBot.none_lt_some

theorem bot_lt_coe (a : α) : (⊥ : WithBot α) < a :=
  none_lt_some a
#align with_bot.bot_lt_coe WithBot.bot_lt_coe

@[simp]
theorem not_lt_none (a : WithBot α) : ¬@LT.lt (WithBot α) _ a none := fun ⟨_, h, _⟩ => Option.not_mem_none _ h
#align with_bot.not_lt_none WithBot.not_lt_none

theorem lt_iff_exists_coe : ∀ {a b : WithBot α}, a < b ↔ ∃ p : α, b = p ∧ a < p
  | a, some b => by simp [some_eq_coe, coe_eq_coe]
  | a, none => iff_of_false (not_lt_none _) <| by simp [none_eq_bot]
#align with_bot.lt_iff_exists_coe WithBot.lt_iff_exists_coe

theorem lt_coe_iff : ∀ {x : WithBot α}, x < b ↔ ∀ a, x = ↑a → a < b
  | some b => by simp [some_eq_coe, coe_eq_coe, coe_lt_coe]
  | none => by simp [none_eq_bot, bot_lt_coe]
#align with_bot.lt_coe_iff WithBot.lt_coe_iff

end LT

instance [Preorder α] : Preorder (WithBot α) where
  le := (· ≤ ·)
  lt := (· < ·)
  lt_iff_le_not_le := by
    intros
    cases a <;> cases b <;> simp [lt_iff_le_not_le] <;> simp [(· < ·), (· ≤ ·)]
  le_refl o a ha := ⟨a, ha, le_rfl⟩
  le_trans o₁ o₂ o₃ h₁ h₂ a ha :=
    let ⟨b, hb, ab⟩ := h₁ a ha
    let ⟨c, hc, bc⟩ := h₂ b hb
    ⟨c, hc, le_trans ab bc⟩

instance [PartialOrder α] : PartialOrder (WithBot α) :=
  { WithBot.preorder with
    le_antisymm := fun o₁ o₂ h₁ h₂ => by
      cases' o₁ with a
      · cases' o₂ with b
        · rfl
          
        rcases h₂ b rfl with ⟨_, ⟨⟩, _⟩
        
      · rcases h₁ a rfl with ⟨b, ⟨⟩, h₁'⟩
        rcases h₂ b rfl with ⟨_, ⟨⟩, h₂'⟩
        rw [le_antisymm h₁' h₂']
         }

theorem coe_strict_mono [Preorder α] : StrictMono (coe : α → WithBot α) := fun a b => some_lt_some.2
#align with_bot.coe_strict_mono WithBot.coe_strict_mono

theorem coe_mono [Preorder α] : Monotone (coe : α → WithBot α) := fun a b => coe_le_coe.2
#align with_bot.coe_mono WithBot.coe_mono

theorem monotone_iff [Preorder α] [Preorder β] {f : WithBot α → β} :
    Monotone f ↔ Monotone (f ∘ coe : α → β) ∧ ∀ x : α, f ⊥ ≤ f x :=
  ⟨fun h => ⟨h.comp WithBot.coe_mono, fun x => h bot_le⟩, fun h =>
    WithBot.forall.2
      ⟨WithBot.forall.2 ⟨fun _ => le_rfl, fun x _ => h.2 x⟩, fun x =>
        WithBot.forall.2 ⟨fun h => (not_coe_le_bot _ h).elim, fun y hle => h.1 (coe_le_coe.1 hle)⟩⟩⟩
#align with_bot.monotone_iff WithBot.monotone_iff

@[simp]
theorem monotone_map_iff [Preorder α] [Preorder β] {f : α → β} : Monotone (WithBot.map f) ↔ Monotone f :=
  monotone_iff.trans <| by simp [Monotone]
#align with_bot.monotone_map_iff WithBot.monotone_map_iff

alias monotone_map_iff ↔ _ _root_.monotone.with_bot_map

theorem strict_mono_iff [Preorder α] [Preorder β] {f : WithBot α → β} :
    StrictMono f ↔ StrictMono (f ∘ coe : α → β) ∧ ∀ x : α, f ⊥ < f x :=
  ⟨fun h => ⟨h.comp WithBot.coe_strict_mono, fun x => h (bot_lt_coe _)⟩, fun h =>
    WithBot.forall.2
      ⟨WithBot.forall.2 ⟨flip absurd (lt_irrefl _), fun x _ => h.2 x⟩, fun x =>
        WithBot.forall.2 ⟨fun h => (not_lt_bot h).elim, fun y hle => h.1 (coe_lt_coe.1 hle)⟩⟩⟩
#align with_bot.strict_mono_iff WithBot.strict_mono_iff

@[simp]
theorem strict_mono_map_iff [Preorder α] [Preorder β] {f : α → β} : StrictMono (WithBot.map f) ↔ StrictMono f :=
  strict_mono_iff.trans <| by simp [StrictMono, bot_lt_coe]
#align with_bot.strict_mono_map_iff WithBot.strict_mono_map_iff

alias strict_mono_map_iff ↔ _ _root_.strict_mono.with_bot_map

theorem map_le_iff [Preorder α] [Preorder β] (f : α → β) (mono_iff : ∀ {a b}, f a ≤ f b ↔ a ≤ b) :
    ∀ a b : WithBot α, a.map f ≤ b.map f ↔ a ≤ b
  | ⊥, _ => by simp only [map_bot, bot_le]
  | (a : α), ⊥ => by simp only [map_coe, map_bot, coe_ne_bot, not_coe_le_bot _]
  | (a : α), (b : α) => by simpa only [map_coe, coe_le_coe] using mono_iff
#align with_bot.map_le_iff WithBot.map_le_iff

theorem le_coe_unbot' [Preorder α] : ∀ (a : WithBot α) (b : α), a ≤ a.unbot' b
  | (a : α), b => le_rfl
  | ⊥, b => bot_le
#align with_bot.le_coe_unbot' WithBot.le_coe_unbot'

theorem unbot'_bot_le_iff [LE α] [OrderBot α] {a : WithBot α} {b : α} : a.unbot' ⊥ ≤ b ↔ a ≤ b := by
  cases a <;> simp [none_eq_bot, some_eq_coe]
#align with_bot.unbot'_bot_le_iff WithBot.unbot'_bot_le_iff

theorem unbot'_lt_iff [LT α] {a : WithBot α} {b c : α} (ha : a ≠ ⊥) : a.unbot' b < c ↔ a < c := by
  lift a to α using ha
  rw [unbot'_coe, coe_lt_coe]
#align with_bot.unbot'_lt_iff WithBot.unbot'_lt_iff

instance [SemilatticeSup α] : SemilatticeSup (WithBot α) :=
  { WithBot.orderBot, WithBot.partialOrder with sup := Option.liftOrGet (· ⊔ ·),
    le_sup_left := fun o₁ o₂ a ha => by cases ha <;> cases o₂ <;> simp [Option.liftOrGet],
    le_sup_right := fun o₁ o₂ a ha => by cases ha <;> cases o₁ <;> simp [Option.liftOrGet],
    sup_le := fun o₁ o₂ o₃ h₁ h₂ a ha => by
      cases' o₁ with b <;> cases' o₂ with c <;> cases ha
      · exact h₂ a rfl
        
      · exact h₁ a rfl
        
      · rcases h₁ b rfl with ⟨d, ⟨⟩, h₁'⟩
        simp at h₂
        exact ⟨d, rfl, sup_le h₁' h₂⟩
         }

theorem coe_sup [SemilatticeSup α] (a b : α) : ((a ⊔ b : α) : WithBot α) = a ⊔ b :=
  rfl
#align with_bot.coe_sup WithBot.coe_sup

instance [SemilatticeInf α] : SemilatticeInf (WithBot α) :=
  { WithBot.orderBot, WithBot.partialOrder with inf := fun o₁ o₂ => o₁.bind fun a => o₂.map fun b => a ⊓ b,
    inf_le_left := fun o₁ o₂ a ha => by
      simp [map] at ha
      rcases ha with ⟨b, rfl, c, rfl, rfl⟩
      exact ⟨_, rfl, inf_le_left⟩,
    inf_le_right := fun o₁ o₂ a ha => by
      simp [map] at ha
      rcases ha with ⟨b, rfl, c, rfl, rfl⟩
      exact ⟨_, rfl, inf_le_right⟩,
    le_inf := fun o₁ o₂ o₃ h₁ h₂ a ha => by
      cases ha
      rcases h₁ a rfl with ⟨b, ⟨⟩, ab⟩
      rcases h₂ a rfl with ⟨c, ⟨⟩, ac⟩
      exact ⟨_, rfl, le_inf ab ac⟩ }

theorem coe_inf [SemilatticeInf α] (a b : α) : ((a ⊓ b : α) : WithBot α) = a ⊓ b :=
  rfl
#align with_bot.coe_inf WithBot.coe_inf

instance [Lattice α] : Lattice (WithBot α) :=
  { WithBot.semilatticeSup, WithBot.semilatticeInf with }

instance [DistribLattice α] : DistribLattice (WithBot α) :=
  { WithBot.lattice with
    le_sup_inf := fun o₁ o₂ o₃ =>
      match o₁, o₂, o₃ with
      | ⊥, ⊥, ⊥ => le_rfl
      | ⊥, ⊥, (a₁ : α) => le_rfl
      | ⊥, (a₁ : α), ⊥ => le_rfl
      | ⊥, (a₁ : α), (a₃ : α) => le_rfl
      | (a₁ : α), ⊥, ⊥ => inf_le_left
      | (a₁ : α), ⊥, (a₃ : α) => inf_le_left
      | (a₁ : α), (a₂ : α), ⊥ => inf_le_right
      | (a₁ : α), (a₂ : α), (a₃ : α) => coe_le_coe.mpr le_sup_inf }

instance decidableLe [LE α] [@DecidableRel α (· ≤ ·)] : @DecidableRel (WithBot α) (· ≤ ·)
  | none, x => is_true fun a h => Option.noConfusion h
  | some x, some y => if h : x ≤ y then isTrue (some_le_some.2 h) else is_false <| by simp [*]
  | some x, none => is_false fun h => by rcases h x rfl with ⟨y, ⟨_⟩, _⟩
#align with_bot.decidable_le WithBot.decidableLe

instance decidableLt [LT α] [@DecidableRel α (· < ·)] : @DecidableRel (WithBot α) (· < ·)
  | none, some x => is_true <| by exists x, rfl <;> rintro _ ⟨⟩
  | some x, some y => if h : x < y then is_true <| by simp [*] else is_false <| by simp [*]
  | x, none => is_false <| by rintro ⟨a, ⟨⟨⟩⟩⟩
#align with_bot.decidable_lt WithBot.decidableLt

instance is_total_le [LE α] [IsTotal α (· ≤ ·)] : IsTotal (WithBot α) (· ≤ ·) :=
  ⟨fun a b =>
    match a, b with
    | none, _ => Or.inl bot_le
    | _, none => Or.inr bot_le
    | some x, some y => (total_of (· ≤ ·) x y).imp some_le_some.2 some_le_some.2⟩
#align with_bot.is_total_le WithBot.is_total_le

instance [LinearOrder α] : LinearOrder (WithBot α) :=
  Lattice.toLinearOrder _

-- this is not marked simp because the corresponding with_top lemmas are used
@[norm_cast]
theorem coe_min [LinearOrder α] (x y : α) : ((min x y : α) : WithBot α) = min x y :=
  rfl
#align with_bot.coe_min WithBot.coe_min

-- this is not marked simp because the corresponding with_top lemmas are used
@[norm_cast]
theorem coe_max [LinearOrder α] (x y : α) : ((max x y : α) : WithBot α) = max x y :=
  rfl
#align with_bot.coe_max WithBot.coe_max

theorem well_founded_lt [Preorder α] (h : @WellFounded α (· < ·)) : @WellFounded (WithBot α) (· < ·) :=
  have acc_bot : Acc ((· < ·) : WithBot α → WithBot α → Prop) ⊥ := Acc.intro _ fun a ha => (not_le_of_gt ha bot_le).elim
  ⟨fun a =>
    Option.recOn a acc_bot fun a =>
      Acc.intro _ fun b =>
        Option.recOn b (fun _ => acc_bot) fun b =>
          WellFounded.induction h b
            (show
              ∀ b : α,
                (∀ c, c < b → (c : WithBot α) < a → Acc ((· < ·) : WithBot α → WithBot α → Prop) c) →
                  (b : WithBot α) < a → Acc ((· < ·) : WithBot α → WithBot α → Prop) b
              from fun b ih hba =>
              Acc.intro _ fun c =>
                Option.recOn c (fun _ => acc_bot) fun c hc => ih _ (some_lt_some.1 hc) (lt_trans hc hba))⟩
#align with_bot.well_founded_lt WithBot.well_founded_lt

instance [LT α] [DenselyOrdered α] [NoMinOrder α] : DenselyOrdered (WithBot α) :=
  ⟨fun a b =>
    match a, b with
    | a, none => fun h : a < ⊥ => (not_lt_none _ h).elim
    | none, some b => fun h =>
      let ⟨a, ha⟩ := exists_lt b
      ⟨a, bot_lt_coe a, coe_lt_coe.2 ha⟩
    | some a, some b => fun h =>
      let ⟨a, ha₁, ha₂⟩ := exists_between (coe_lt_coe.1 h)
      ⟨a, coe_lt_coe.2 ha₁, coe_lt_coe.2 ha₂⟩⟩

theorem lt_iff_exists_coe_btwn [Preorder α] [DenselyOrdered α] [NoMinOrder α] {a b : WithBot α} :
    a < b ↔ ∃ x : α, a < ↑x ∧ ↑x < b :=
  ⟨fun h =>
    let ⟨y, hy⟩ := exists_between h
    let ⟨x, hx⟩ := lt_iff_exists_coe.1 hy.1
    ⟨x, hx.1 ▸ hy⟩,
    fun ⟨x, hx⟩ => lt_trans hx.1 hx.2⟩
#align with_bot.lt_iff_exists_coe_btwn WithBot.lt_iff_exists_coe_btwn

instance [LE α] [NoTopOrder α] [Nonempty α] : NoTopOrder (WithBot α) :=
  ⟨by
    apply rec_bot_coe
    · exact ‹Nonempty α›.elim fun a => ⟨a, not_coe_le_bot a⟩
      
    · intro a
      obtain ⟨b, h⟩ := exists_not_le a
      exact ⟨b, by rwa [coe_le_coe]⟩
      ⟩

instance [LT α] [NoMaxOrder α] [Nonempty α] : NoMaxOrder (WithBot α) :=
  ⟨by
    apply WithBot.recBotCoe
    · apply ‹Nonempty α›.elim
      exact fun a => ⟨a, WithBot.bot_lt_coe a⟩
      
    · intro a
      obtain ⟨b, ha⟩ := exists_gt a
      exact ⟨b, with_bot.coe_lt_coe.mpr ha⟩
      ⟩

end WithBot

--TODO(Mario): Construct using order dual on with_bot
/-- Attach `⊤` to a type. -/
def WithTop (α : Type _) :=
  Option α
#align with_top WithTop

namespace WithTop

variable {a b : α}

unsafe instance [has_to_format α] :
    has_to_format (WithTop α) where to_format x :=
    match x with
    | none => "⊤"
    | some x => to_fmt x

instance [Repr α] : Repr (WithTop α) :=
  ⟨fun o =>
    match o with
    | none => "⊤"
    | some a => "↑" ++ repr a⟩

instance : CoeTC α (WithTop α) :=
  ⟨some⟩

instance : HasTop (WithTop α) :=
  ⟨none⟩

unsafe instance {α : Type} [reflected _ α] [has_reflect α] : has_reflect (WithTop α)
  | ⊤ => q(⊤)
  | (a : α) => q((coe : α → WithTop α)).subst q(a)

instance : Inhabited (WithTop α) :=
  ⟨⊤⟩

protected theorem forall {p : WithTop α → Prop} : (∀ x, p x) ↔ p ⊤ ∧ ∀ x : α, p x :=
  Option.forall
#align with_top.forall WithTop.forall

protected theorem exists {p : WithTop α → Prop} : (∃ x, p x) ↔ p ⊤ ∨ ∃ x : α, p x :=
  Option.exists
#align with_top.exists WithTop.exists

theorem none_eq_top : (none : WithTop α) = (⊤ : WithTop α) :=
  rfl
#align with_top.none_eq_top WithTop.none_eq_top

theorem some_eq_coe (a : α) : (some a : WithTop α) = (↑a : WithTop α) :=
  rfl
#align with_top.some_eq_coe WithTop.some_eq_coe

@[simp]
theorem top_ne_coe : ⊤ ≠ (a : WithTop α) :=
  fun.
#align with_top.top_ne_coe WithTop.top_ne_coe

@[simp]
theorem coe_ne_top : (a : WithTop α) ≠ ⊤ :=
  fun.
#align with_top.coe_ne_top WithTop.coe_ne_top

/-- Recursor for `with_top` using the preferred forms `⊤` and `↑a`. -/
@[elab_as_elim]
def recTopCoe {C : WithTop α → Sort _} (h₁ : C ⊤) (h₂ : ∀ a : α, C a) : ∀ n : WithTop α, C n :=
  Option.rec h₁ h₂
#align with_top.rec_top_coe WithTop.recTopCoe

@[simp]
theorem rec_top_coe_top {C : WithTop α → Sort _} (d : C ⊤) (f : ∀ a : α, C a) : @recTopCoe _ C d f ⊤ = d :=
  rfl
#align with_top.rec_top_coe_top WithTop.rec_top_coe_top

@[simp]
theorem rec_top_coe_coe {C : WithTop α → Sort _} (d : C ⊤) (f : ∀ a : α, C a) (x : α) : @recTopCoe _ C d f ↑x = f x :=
  rfl
#align with_top.rec_top_coe_coe WithTop.rec_top_coe_coe

/-- `with_top.to_dual` is the equivalence sending `⊤` to `⊥` and any `a : α` to `to_dual a : αᵒᵈ`.
See `with_top.to_dual_bot_equiv` for the related order-iso.
-/
protected def toDual : WithTop α ≃ WithBot αᵒᵈ :=
  Equiv.refl _
#align with_top.to_dual WithTop.toDual

/-- `with_top.of_dual` is the equivalence sending `⊤` to `⊥` and any `a : αᵒᵈ` to `of_dual a : α`.
See `with_top.to_dual_bot_equiv` for the related order-iso.
-/
protected def ofDual : WithTop αᵒᵈ ≃ WithBot α :=
  Equiv.refl _
#align with_top.of_dual WithTop.ofDual

/-- `with_bot.to_dual` is the equivalence sending `⊥` to `⊤` and any `a : α` to `to_dual a : αᵒᵈ`.
See `with_bot.to_dual_top_equiv` for the related order-iso.
-/
protected def _root_.with_bot.to_dual : WithBot α ≃ WithTop αᵒᵈ :=
  Equiv.refl _
#align with_top._root_.with_bot.to_dual with_top._root_.with_bot.to_dual

/-- `with_bot.of_dual` is the equivalence sending `⊥` to `⊤` and any `a : αᵒᵈ` to `of_dual a : α`.
See `with_bot.to_dual_top_equiv` for the related order-iso.
-/
protected def _root_.with_bot.of_dual : WithBot αᵒᵈ ≃ WithTop α :=
  Equiv.refl _
#align with_top._root_.with_bot.of_dual with_top._root_.with_bot.of_dual

@[simp]
theorem to_dual_symm_apply (a : WithBot αᵒᵈ) : WithTop.toDual.symm a = a.ofDual :=
  rfl
#align with_top.to_dual_symm_apply WithTop.to_dual_symm_apply

@[simp]
theorem of_dual_symm_apply (a : WithBot α) : WithTop.ofDual.symm a = a.toDual :=
  rfl
#align with_top.of_dual_symm_apply WithTop.of_dual_symm_apply

@[simp]
theorem to_dual_apply_top : WithTop.toDual (⊤ : WithTop α) = ⊥ :=
  rfl
#align with_top.to_dual_apply_top WithTop.to_dual_apply_top

@[simp]
theorem of_dual_apply_top : WithTop.ofDual (⊤ : WithTop α) = ⊥ :=
  rfl
#align with_top.of_dual_apply_top WithTop.of_dual_apply_top

@[simp]
theorem to_dual_apply_coe (a : α) : WithTop.toDual (a : WithTop α) = toDual a :=
  rfl
#align with_top.to_dual_apply_coe WithTop.to_dual_apply_coe

@[simp]
theorem of_dual_apply_coe (a : αᵒᵈ) : WithTop.ofDual (a : WithTop αᵒᵈ) = ofDual a :=
  rfl
#align with_top.of_dual_apply_coe WithTop.of_dual_apply_coe

/-- Specialization of `option.get_or_else` to values in `with_top α` that respects API boundaries.
-/
def untop' (d : α) (x : WithTop α) : α :=
  recTopCoe d id x
#align with_top.untop' WithTop.untop'

@[simp]
theorem untop'_top {α} (d : α) : untop' d ⊤ = d :=
  rfl
#align with_top.untop'_top WithTop.untop'_top

@[simp]
theorem untop'_coe {α} (d x : α) : untop' d x = x :=
  rfl
#align with_top.untop'_coe WithTop.untop'_coe

@[norm_cast]
theorem coe_eq_coe : (a : WithTop α) = b ↔ a = b :=
  Option.some_inj
#align with_top.coe_eq_coe WithTop.coe_eq_coe

/-- Lift a map `f : α → β` to `with_top α → with_top β`. Implemented using `option.map`. -/
def map (f : α → β) : WithTop α → WithTop β :=
  Option.map f
#align with_top.map WithTop.map

@[simp]
theorem map_top (f : α → β) : map f ⊤ = ⊤ :=
  rfl
#align with_top.map_top WithTop.map_top

@[simp]
theorem map_coe (f : α → β) (a : α) : map f a = f a :=
  rfl
#align with_top.map_coe WithTop.map_coe

theorem map_comm {f₁ : α → β} {f₂ : α → γ} {g₁ : β → δ} {g₂ : γ → δ} (h : g₁ ∘ f₁ = g₂ ∘ f₂) (a : α) :
    map g₁ (map f₁ a) = map g₂ (map f₂ a) :=
  Option.map_comm h _
#align with_top.map_comm WithTop.map_comm

theorem map_to_dual (f : αᵒᵈ → βᵒᵈ) (a : WithBot α) : map f (WithBot.toDual a) = a.map (to_dual ∘ f) :=
  rfl
#align with_top.map_to_dual WithTop.map_to_dual

theorem map_of_dual (f : α → β) (a : WithBot αᵒᵈ) : map f (WithBot.ofDual a) = a.map (of_dual ∘ f) :=
  rfl
#align with_top.map_of_dual WithTop.map_of_dual

theorem to_dual_map (f : α → β) (a : WithTop α) :
    WithTop.toDual (map f a) = WithBot.map (to_dual ∘ f ∘ of_dual) a.toDual :=
  rfl
#align with_top.to_dual_map WithTop.to_dual_map

theorem of_dual_map (f : αᵒᵈ → βᵒᵈ) (a : WithTop αᵒᵈ) :
    WithTop.ofDual (map f a) = WithBot.map (of_dual ∘ f ∘ to_dual) a.ofDual :=
  rfl
#align with_top.of_dual_map WithTop.of_dual_map

theorem ne_top_iff_exists {x : WithTop α} : x ≠ ⊤ ↔ ∃ a : α, ↑a = x :=
  Option.ne_none_iff_exists
#align with_top.ne_top_iff_exists WithTop.ne_top_iff_exists

/-- Deconstruct a `x : with_top α` to the underlying value in `α`, given a proof that `x ≠ ⊤`. -/
def untop : ∀ x : WithTop α, x ≠ ⊤ → α :=
  WithBot.unbot
#align with_top.untop WithTop.untop

@[simp]
theorem coe_untop (x : WithTop α) (h : x ≠ ⊤) : (x.untop h : WithTop α) = x :=
  WithBot.coe_unbot x h
#align with_top.coe_untop WithTop.coe_untop

@[simp]
theorem untop_coe (x : α) (h : (x : WithTop α) ≠ ⊤ := coe_ne_top) : (x : WithTop α).untop h = x :=
  rfl
#align with_top.untop_coe WithTop.untop_coe

instance canLift : CanLift (WithTop α) α coe fun r => r ≠ ⊤ where prf x h := ⟨x.untop h, coe_untop _ _⟩
#align with_top.can_lift WithTop.canLift

section LE

variable [LE α]

instance (priority := 10) : LE (WithTop α) :=
  ⟨fun o₁ o₂ : Option α => ∀ a ∈ o₂, ∃ b ∈ o₁, b ≤ a⟩

theorem to_dual_le_iff {a : WithTop α} {b : WithBot αᵒᵈ} : WithTop.toDual a ≤ b ↔ WithBot.ofDual b ≤ a :=
  Iff.rfl
#align with_top.to_dual_le_iff WithTop.to_dual_le_iff

theorem le_to_dual_iff {a : WithBot αᵒᵈ} {b : WithTop α} : a ≤ WithTop.toDual b ↔ b ≤ WithBot.ofDual a :=
  Iff.rfl
#align with_top.le_to_dual_iff WithTop.le_to_dual_iff

@[simp]
theorem to_dual_le_to_dual_iff {a b : WithTop α} : WithTop.toDual a ≤ WithTop.toDual b ↔ b ≤ a :=
  Iff.rfl
#align with_top.to_dual_le_to_dual_iff WithTop.to_dual_le_to_dual_iff

theorem of_dual_le_iff {a : WithTop αᵒᵈ} {b : WithBot α} : WithTop.ofDual a ≤ b ↔ WithBot.toDual b ≤ a :=
  Iff.rfl
#align with_top.of_dual_le_iff WithTop.of_dual_le_iff

theorem le_of_dual_iff {a : WithBot α} {b : WithTop αᵒᵈ} : a ≤ WithTop.ofDual b ↔ b ≤ WithBot.toDual a :=
  Iff.rfl
#align with_top.le_of_dual_iff WithTop.le_of_dual_iff

@[simp]
theorem of_dual_le_of_dual_iff {a b : WithTop αᵒᵈ} : WithTop.ofDual a ≤ WithTop.ofDual b ↔ b ≤ a :=
  Iff.rfl
#align with_top.of_dual_le_of_dual_iff WithTop.of_dual_le_of_dual_iff

@[simp, norm_cast]
theorem coe_le_coe : (a : WithTop α) ≤ b ↔ a ≤ b := by
  simp only [← to_dual_le_to_dual_iff, to_dual_apply_coe, WithBot.coe_le_coe, to_dual_le_to_dual]
#align with_top.coe_le_coe WithTop.coe_le_coe

@[simp]
theorem some_le_some : @LE.le (WithTop α) _ (some a) (some b) ↔ a ≤ b :=
  coe_le_coe
#align with_top.some_le_some WithTop.some_le_some

@[simp]
theorem le_none {a : WithTop α} : @LE.le (WithTop α) _ a none :=
  to_dual_le_to_dual_iff.mp WithBot.none_le
#align with_top.le_none WithTop.le_none

instance : OrderTop (WithTop α) :=
  { WithTop.hasTop with le_top := fun a => le_none }

instance [OrderBot α] : OrderBot (WithTop α) where
  bot := some ⊥
  bot_le o a ha := by cases ha <;> exact ⟨_, rfl, bot_le⟩

instance [OrderBot α] : BoundedOrder (WithTop α) :=
  { WithTop.orderTop, WithTop.orderBot with }

theorem not_top_le_coe (a : α) : ¬(⊤ : WithTop α) ≤ ↑a :=
  WithBot.not_coe_le_bot (toDual a)
#align with_top.not_top_le_coe WithTop.not_top_le_coe

theorem le_coe : ∀ {o : Option α}, a ∈ o → (@LE.le (WithTop α) _ o b ↔ a ≤ b)
  | _, rfl => coe_le_coe
#align with_top.le_coe WithTop.le_coe

theorem le_coe_iff {x : WithTop α} : x ≤ b ↔ ∃ a : α, x = a ∧ a ≤ b := by
  simpa [← to_dual_le_to_dual_iff, WithBot.coe_le_iff]
#align with_top.le_coe_iff WithTop.le_coe_iff

theorem coe_le_iff {x : WithTop α} : ↑a ≤ x ↔ ∀ b, x = ↑b → a ≤ b := by
  simp only [← to_dual_le_to_dual_iff, to_dual_apply_coe, WithBot.le_coe_iff, OrderDual.forall, to_dual_le_to_dual]
  exact forall₂_congr fun _ _ => Iff.rfl
#align with_top.coe_le_iff WithTop.coe_le_iff

protected theorem _root_.is_min.with_top (h : IsMin a) : IsMin (a : WithTop α) := by
  -- defeq to is_max_to_dual_iff.mp (is_max.with_bot _), but that breaks API boundary
  intro _ hb
  rw [← to_dual_le_to_dual_iff] at hb
  simpa [to_dual_le_iff] using (IsMax.with_bot h : IsMax (to_dual a : WithBot αᵒᵈ)) hb
#align with_top._root_.is_min.with_top with_top._root_.is_min.with_top

end LE

section LT

variable [LT α]

instance (priority := 10) : LT (WithTop α) :=
  ⟨fun o₁ o₂ : Option α => ∃ b ∈ o₁, ∀ a ∈ o₂, b < a⟩

theorem to_dual_lt_iff {a : WithTop α} {b : WithBot αᵒᵈ} : WithTop.toDual a < b ↔ WithBot.ofDual b < a :=
  Iff.rfl
#align with_top.to_dual_lt_iff WithTop.to_dual_lt_iff

theorem lt_to_dual_iff {a : WithBot αᵒᵈ} {b : WithTop α} : a < WithTop.toDual b ↔ b < WithBot.ofDual a :=
  Iff.rfl
#align with_top.lt_to_dual_iff WithTop.lt_to_dual_iff

@[simp]
theorem to_dual_lt_to_dual_iff {a b : WithTop α} : WithTop.toDual a < WithTop.toDual b ↔ b < a :=
  Iff.rfl
#align with_top.to_dual_lt_to_dual_iff WithTop.to_dual_lt_to_dual_iff

theorem of_dual_lt_iff {a : WithTop αᵒᵈ} {b : WithBot α} : WithTop.ofDual a < b ↔ WithBot.toDual b < a :=
  Iff.rfl
#align with_top.of_dual_lt_iff WithTop.of_dual_lt_iff

theorem lt_of_dual_iff {a : WithBot α} {b : WithTop αᵒᵈ} : a < WithTop.ofDual b ↔ b < WithBot.toDual a :=
  Iff.rfl
#align with_top.lt_of_dual_iff WithTop.lt_of_dual_iff

@[simp]
theorem of_dual_lt_of_dual_iff {a b : WithTop αᵒᵈ} : WithTop.ofDual a < WithTop.ofDual b ↔ b < a :=
  Iff.rfl
#align with_top.of_dual_lt_of_dual_iff WithTop.of_dual_lt_of_dual_iff

end LT

end WithTop

namespace WithBot

@[simp]
theorem to_dual_symm_apply (a : WithTop αᵒᵈ) : WithBot.toDual.symm a = a.ofDual :=
  rfl
#align with_bot.to_dual_symm_apply WithBot.to_dual_symm_apply

@[simp]
theorem of_dual_symm_apply (a : WithTop α) : WithBot.ofDual.symm a = a.toDual :=
  rfl
#align with_bot.of_dual_symm_apply WithBot.of_dual_symm_apply

@[simp]
theorem to_dual_apply_bot : WithBot.toDual (⊥ : WithBot α) = ⊤ :=
  rfl
#align with_bot.to_dual_apply_bot WithBot.to_dual_apply_bot

@[simp]
theorem of_dual_apply_bot : WithBot.ofDual (⊥ : WithBot α) = ⊤ :=
  rfl
#align with_bot.of_dual_apply_bot WithBot.of_dual_apply_bot

@[simp]
theorem to_dual_apply_coe (a : α) : WithBot.toDual (a : WithBot α) = toDual a :=
  rfl
#align with_bot.to_dual_apply_coe WithBot.to_dual_apply_coe

@[simp]
theorem of_dual_apply_coe (a : αᵒᵈ) : WithBot.ofDual (a : WithBot αᵒᵈ) = ofDual a :=
  rfl
#align with_bot.of_dual_apply_coe WithBot.of_dual_apply_coe

theorem map_to_dual (f : αᵒᵈ → βᵒᵈ) (a : WithTop α) : WithBot.map f (WithTop.toDual a) = a.map (to_dual ∘ f) :=
  rfl
#align with_bot.map_to_dual WithBot.map_to_dual

theorem map_of_dual (f : α → β) (a : WithTop αᵒᵈ) : WithBot.map f (WithTop.ofDual a) = a.map (of_dual ∘ f) :=
  rfl
#align with_bot.map_of_dual WithBot.map_of_dual

theorem to_dual_map (f : α → β) (a : WithBot α) :
    WithBot.toDual (WithBot.map f a) = map (to_dual ∘ f ∘ of_dual) a.toDual :=
  rfl
#align with_bot.to_dual_map WithBot.to_dual_map

theorem of_dual_map (f : αᵒᵈ → βᵒᵈ) (a : WithBot αᵒᵈ) :
    WithBot.ofDual (WithBot.map f a) = map (of_dual ∘ f ∘ to_dual) a.ofDual :=
  rfl
#align with_bot.of_dual_map WithBot.of_dual_map

section LE

variable [LE α] {a b : α}

theorem to_dual_le_iff {a : WithBot α} {b : WithTop αᵒᵈ} : WithBot.toDual a ≤ b ↔ WithTop.ofDual b ≤ a :=
  Iff.rfl
#align with_bot.to_dual_le_iff WithBot.to_dual_le_iff

theorem le_to_dual_iff {a : WithTop αᵒᵈ} {b : WithBot α} : a ≤ WithBot.toDual b ↔ b ≤ WithTop.ofDual a :=
  Iff.rfl
#align with_bot.le_to_dual_iff WithBot.le_to_dual_iff

@[simp]
theorem to_dual_le_to_dual_iff {a b : WithBot α} : WithBot.toDual a ≤ WithBot.toDual b ↔ b ≤ a :=
  Iff.rfl
#align with_bot.to_dual_le_to_dual_iff WithBot.to_dual_le_to_dual_iff

theorem of_dual_le_iff {a : WithBot αᵒᵈ} {b : WithTop α} : WithBot.ofDual a ≤ b ↔ WithTop.toDual b ≤ a :=
  Iff.rfl
#align with_bot.of_dual_le_iff WithBot.of_dual_le_iff

theorem le_of_dual_iff {a : WithTop α} {b : WithBot αᵒᵈ} : a ≤ WithBot.ofDual b ↔ b ≤ WithTop.toDual a :=
  Iff.rfl
#align with_bot.le_of_dual_iff WithBot.le_of_dual_iff

@[simp]
theorem of_dual_le_of_dual_iff {a b : WithBot αᵒᵈ} : WithBot.ofDual a ≤ WithBot.ofDual b ↔ b ≤ a :=
  Iff.rfl
#align with_bot.of_dual_le_of_dual_iff WithBot.of_dual_le_of_dual_iff

end LE

section LT

variable [LT α] {a b : α}

theorem to_dual_lt_iff {a : WithBot α} {b : WithTop αᵒᵈ} : WithBot.toDual a < b ↔ WithTop.ofDual b < a :=
  Iff.rfl
#align with_bot.to_dual_lt_iff WithBot.to_dual_lt_iff

theorem lt_to_dual_iff {a : WithTop αᵒᵈ} {b : WithBot α} : a < WithBot.toDual b ↔ b < WithTop.ofDual a :=
  Iff.rfl
#align with_bot.lt_to_dual_iff WithBot.lt_to_dual_iff

@[simp]
theorem to_dual_lt_to_dual_iff {a b : WithBot α} : WithBot.toDual a < WithBot.toDual b ↔ b < a :=
  Iff.rfl
#align with_bot.to_dual_lt_to_dual_iff WithBot.to_dual_lt_to_dual_iff

theorem of_dual_lt_iff {a : WithBot αᵒᵈ} {b : WithTop α} : WithBot.ofDual a < b ↔ WithTop.toDual b < a :=
  Iff.rfl
#align with_bot.of_dual_lt_iff WithBot.of_dual_lt_iff

theorem lt_of_dual_iff {a : WithTop α} {b : WithBot αᵒᵈ} : a < WithBot.ofDual b ↔ b < WithTop.toDual a :=
  Iff.rfl
#align with_bot.lt_of_dual_iff WithBot.lt_of_dual_iff

@[simp]
theorem of_dual_lt_of_dual_iff {a b : WithBot αᵒᵈ} : WithBot.ofDual a < WithBot.ofDual b ↔ b < a :=
  Iff.rfl
#align with_bot.of_dual_lt_of_dual_iff WithBot.of_dual_lt_of_dual_iff

end LT

end WithBot

namespace WithTop

section LT

variable [LT α] {a b : α}

@[simp, norm_cast]
theorem coe_lt_coe : (a : WithTop α) < b ↔ a < b := by
  simp only [← to_dual_lt_to_dual_iff, to_dual_apply_coe, WithBot.coe_lt_coe, to_dual_lt_to_dual]
#align with_top.coe_lt_coe WithTop.coe_lt_coe

@[simp]
theorem some_lt_some : @LT.lt (WithTop α) _ (some a) (some b) ↔ a < b :=
  coe_lt_coe
#align with_top.some_lt_some WithTop.some_lt_some

theorem coe_lt_top (a : α) : (a : WithTop α) < ⊤ := by simpa [← to_dual_lt_to_dual_iff] using WithBot.bot_lt_coe _
#align with_top.coe_lt_top WithTop.coe_lt_top

@[simp]
theorem some_lt_none (a : α) : @LT.lt (WithTop α) _ (some a) none :=
  coe_lt_top a
#align with_top.some_lt_none WithTop.some_lt_none

@[simp]
theorem not_none_lt (a : WithTop α) : ¬@LT.lt (WithTop α) _ none a := by
  rw [← to_dual_lt_to_dual_iff]
  exact WithBot.not_lt_none _
#align with_top.not_none_lt WithTop.not_none_lt

theorem lt_iff_exists_coe {a b : WithTop α} : a < b ↔ ∃ p : α, a = p ∧ ↑p < b := by
  rw [← to_dual_lt_to_dual_iff, WithBot.lt_iff_exists_coe, OrderDual.exists]
  exact exists_congr fun _ => and_congr_left' Iff.rfl
#align with_top.lt_iff_exists_coe WithTop.lt_iff_exists_coe

theorem coe_lt_iff {x : WithTop α} : ↑a < x ↔ ∀ b, x = ↑b → a < b := by
  simp only [← to_dual_lt_to_dual_iff, WithBot.lt_coe_iff, to_dual_apply_coe, OrderDual.forall, to_dual_lt_to_dual]
  exact forall₂_congr fun _ _ => Iff.rfl
#align with_top.coe_lt_iff WithTop.coe_lt_iff

end LT

instance [Preorder α] : Preorder (WithTop α) where
  le := (· ≤ ·)
  lt := (· < ·)
  lt_iff_le_not_le := by simp [← to_dual_lt_to_dual_iff, lt_iff_le_not_le]
  le_refl _ := to_dual_le_to_dual_iff.mp le_rfl
  le_trans _ _ _ := by
    simp_rw [← to_dual_le_to_dual_iff]
    exact Function.swap le_trans

instance [PartialOrder α] : PartialOrder (WithTop α) :=
  { WithTop.preorder with
    le_antisymm := fun _ _ => by
      simp_rw [← to_dual_le_to_dual_iff]
      exact Function.swap le_antisymm }

theorem coe_strict_mono [Preorder α] : StrictMono (coe : α → WithTop α) := fun a b => some_lt_some.2
#align with_top.coe_strict_mono WithTop.coe_strict_mono

theorem coe_mono [Preorder α] : Monotone (coe : α → WithTop α) := fun a b => coe_le_coe.2
#align with_top.coe_mono WithTop.coe_mono

theorem monotone_iff [Preorder α] [Preorder β] {f : WithTop α → β} :
    Monotone f ↔ Monotone (f ∘ coe : α → β) ∧ ∀ x : α, f x ≤ f ⊤ :=
  ⟨fun h => ⟨h.comp WithTop.coe_mono, fun x => h le_top⟩, fun h =>
    WithTop.forall.2
      ⟨WithTop.forall.2 ⟨fun _ => le_rfl, fun x h => (not_top_le_coe _ h).elim⟩, fun x =>
        WithTop.forall.2 ⟨fun _ => h.2 x, fun y hle => h.1 (coe_le_coe.1 hle)⟩⟩⟩
#align with_top.monotone_iff WithTop.monotone_iff

@[simp]
theorem monotone_map_iff [Preorder α] [Preorder β] {f : α → β} : Monotone (WithTop.map f) ↔ Monotone f :=
  monotone_iff.trans <| by simp [Monotone]
#align with_top.monotone_map_iff WithTop.monotone_map_iff

alias monotone_map_iff ↔ _ _root_.monotone.with_top_map

theorem strict_mono_iff [Preorder α] [Preorder β] {f : WithTop α → β} :
    StrictMono f ↔ StrictMono (f ∘ coe : α → β) ∧ ∀ x : α, f x < f ⊤ :=
  ⟨fun h => ⟨h.comp WithTop.coe_strict_mono, fun x => h (coe_lt_top _)⟩, fun h =>
    WithTop.forall.2
      ⟨WithTop.forall.2 ⟨flip absurd (lt_irrefl _), fun x h => (not_top_lt h).elim⟩, fun x =>
        WithTop.forall.2 ⟨fun _ => h.2 x, fun y hle => h.1 (coe_lt_coe.1 hle)⟩⟩⟩
#align with_top.strict_mono_iff WithTop.strict_mono_iff

@[simp]
theorem strict_mono_map_iff [Preorder α] [Preorder β] {f : α → β} : StrictMono (WithTop.map f) ↔ StrictMono f :=
  strict_mono_iff.trans <| by simp [StrictMono, coe_lt_top]
#align with_top.strict_mono_map_iff WithTop.strict_mono_map_iff

alias strict_mono_map_iff ↔ _ _root_.strict_mono.with_top_map

theorem map_le_iff [Preorder α] [Preorder β] (f : α → β) (a b : WithTop α) (mono_iff : ∀ {a b}, f a ≤ f b ↔ a ≤ b) :
    a.map f ≤ b.map f ↔ a ≤ b := by
  rw [← to_dual_le_to_dual_iff, to_dual_map, to_dual_map, WithBot.map_le_iff, to_dual_le_to_dual_iff]
  simp [mono_iff]
#align with_top.map_le_iff WithTop.map_le_iff

instance [SemilatticeInf α] : SemilatticeInf (WithTop α) :=
  { WithTop.partialOrder with inf := Option.liftOrGet (· ⊓ ·),
    inf_le_left := fun o₁ o₂ a ha => by cases ha <;> cases o₂ <;> simp [Option.liftOrGet],
    inf_le_right := fun o₁ o₂ a ha => by cases ha <;> cases o₁ <;> simp [Option.liftOrGet],
    le_inf := fun o₁ o₂ o₃ h₁ h₂ a ha => by
      cases' o₂ with b <;> cases' o₃ with c <;> cases ha
      · exact h₂ a rfl
        
      · exact h₁ a rfl
        
      · rcases h₁ b rfl with ⟨d, ⟨⟩, h₁'⟩
        simp at h₂
        exact ⟨d, rfl, le_inf h₁' h₂⟩
         }

theorem coe_inf [SemilatticeInf α] (a b : α) : ((a ⊓ b : α) : WithTop α) = a ⊓ b :=
  rfl
#align with_top.coe_inf WithTop.coe_inf

instance [SemilatticeSup α] : SemilatticeSup (WithTop α) :=
  { WithTop.partialOrder with sup := fun o₁ o₂ => o₁.bind fun a => o₂.map fun b => a ⊔ b,
    le_sup_left := fun o₁ o₂ a ha => by
      simp [map] at ha
      rcases ha with ⟨b, rfl, c, rfl, rfl⟩
      exact ⟨_, rfl, le_sup_left⟩,
    le_sup_right := fun o₁ o₂ a ha => by
      simp [map] at ha
      rcases ha with ⟨b, rfl, c, rfl, rfl⟩
      exact ⟨_, rfl, le_sup_right⟩,
    sup_le := fun o₁ o₂ o₃ h₁ h₂ a ha => by
      cases ha
      rcases h₁ a rfl with ⟨b, ⟨⟩, ab⟩
      rcases h₂ a rfl with ⟨c, ⟨⟩, ac⟩
      exact ⟨_, rfl, sup_le ab ac⟩ }

theorem coe_sup [SemilatticeSup α] (a b : α) : ((a ⊔ b : α) : WithTop α) = a ⊔ b :=
  rfl
#align with_top.coe_sup WithTop.coe_sup

instance [Lattice α] : Lattice (WithTop α) :=
  { WithTop.semilatticeSup, WithTop.semilatticeInf with }

instance [DistribLattice α] : DistribLattice (WithTop α) :=
  { WithTop.lattice with
    le_sup_inf := fun o₁ o₂ o₃ =>
      match o₁, o₂, o₃ with
      | ⊤, o₂, o₃ => le_rfl
      | (a₁ : α), ⊤, ⊤ => le_rfl
      | (a₁ : α), ⊤, (a₃ : α) => le_rfl
      | (a₁ : α), (a₂ : α), ⊤ => le_rfl
      | (a₁ : α), (a₂ : α), (a₃ : α) => coe_le_coe.mpr le_sup_inf }

instance decidableLe [LE α] [@DecidableRel α (· ≤ ·)] : @DecidableRel (WithTop α) (· ≤ ·) := fun _ _ =>
  decidable_of_decidable_of_iff (WithBot.decidableLe _ _) to_dual_le_to_dual_iff
#align with_top.decidable_le WithTop.decidableLe

instance decidableLt [LT α] [@DecidableRel α (· < ·)] : @DecidableRel (WithTop α) (· < ·) := fun _ _ =>
  decidable_of_decidable_of_iff (WithBot.decidableLt _ _) to_dual_lt_to_dual_iff
#align with_top.decidable_lt WithTop.decidableLt

instance is_total_le [LE α] [IsTotal α (· ≤ ·)] : IsTotal (WithTop α) (· ≤ ·) :=
  ⟨fun _ _ => by
    simp_rw [← to_dual_le_to_dual_iff]
    exact total_of _ _ _⟩
#align with_top.is_total_le WithTop.is_total_le

instance [LinearOrder α] : LinearOrder (WithTop α) :=
  Lattice.toLinearOrder _

@[simp, norm_cast]
theorem coe_min [LinearOrder α] (x y : α) : (↑(min x y) : WithTop α) = min x y :=
  rfl
#align with_top.coe_min WithTop.coe_min

@[simp, norm_cast]
theorem coe_max [LinearOrder α] (x y : α) : (↑(max x y) : WithTop α) = max x y :=
  rfl
#align with_top.coe_max WithTop.coe_max

theorem well_founded_lt [Preorder α] (h : @WellFounded α (· < ·)) : @WellFounded (WithTop α) (· < ·) :=
  have acc_some : ∀ a : α, Acc ((· < ·) : WithTop α → WithTop α → Prop) (some a) := fun a =>
    Acc.intro _
      (WellFounded.induction h a
        (show
          ∀ b, (∀ c, c < b → ∀ d : WithTop α, d < some c → Acc (· < ·) d) → ∀ y : WithTop α, y < some b → Acc (· < ·) y
          from fun b ih c =>
          Option.recOn c (fun hc => (not_lt_of_ge le_top hc).elim) fun c hc => Acc.intro _ (ih _ (some_lt_some.1 hc))))
  ⟨fun a =>
    Option.recOn a (Acc.intro _ fun y => Option.recOn y (fun h => (lt_irrefl _ h).elim) fun _ _ => acc_some _) acc_some⟩
#align with_top.well_founded_lt WithTop.well_founded_lt

theorem well_founded_gt [Preorder α] (h : @WellFounded α (· > ·)) : @WellFounded (WithTop α) (· > ·) :=
  ⟨fun a => by
    -- ideally, use rel_hom_class.acc, but that is defined later
    have : Acc (· < ·) a.to_dual := WellFounded.apply (WithBot.well_founded_lt h) _
    revert this
    generalize ha : a.to_dual = b
    intro ac
    induction' ac with _ H IH generalizing a
    subst ha
    exact ⟨_, fun a' h => IH a'.toDual (to_dual_lt_to_dual.mpr h) _ rfl⟩⟩
#align with_top.well_founded_gt WithTop.well_founded_gt

theorem _root_.with_bot.well_founded_gt [Preorder α] (h : @WellFounded α (· > ·)) : @WellFounded (WithBot α) (· > ·) :=
  ⟨fun a => by
    -- ideally, use rel_hom_class.acc, but that is defined later
    have : Acc (· < ·) a.to_dual := WellFounded.apply (WithTop.well_founded_lt h) _
    revert this
    generalize ha : a.to_dual = b
    intro ac
    induction' ac with _ H IH generalizing a
    subst ha
    exact ⟨_, fun a' h => IH a'.toDual (to_dual_lt_to_dual.mpr h) _ rfl⟩⟩
#align with_top._root_.with_bot.well_founded_gt with_top._root_.with_bot.well_founded_gt

instance Trichotomous.lt [Preorder α] [IsTrichotomous α (· < ·)] : IsTrichotomous (WithTop α) (· < ·) :=
  ⟨by
    rintro (a | _) (b | _)
    iterate 3 simp
    simpa [Option.some_inj] using @trichotomous _ (· < ·) _ a b⟩
#align with_top.trichotomous.lt WithTop.Trichotomous.lt

instance IsWellOrder.lt [Preorder α] [h : IsWellOrder α (· < ·)] :
    IsWellOrder (WithTop α) (· < ·) where wf := well_founded_lt h.wf
#align with_top.is_well_order.lt WithTop.IsWellOrder.lt

instance Trichotomous.gt [Preorder α] [IsTrichotomous α (· > ·)] : IsTrichotomous (WithTop α) (· > ·) :=
  ⟨by
    rintro (a | _) (b | _)
    iterate 3 simp
    simpa [Option.some_inj] using @trichotomous _ (· > ·) _ a b⟩
#align with_top.trichotomous.gt WithTop.Trichotomous.gt

instance IsWellOrder.gt [Preorder α] [h : IsWellOrder α (· > ·)] :
    IsWellOrder (WithTop α) (· > ·) where wf := well_founded_gt h.wf
#align with_top.is_well_order.gt WithTop.IsWellOrder.gt

instance _root_.with_bot.trichotomous.lt [Preorder α] [h : IsTrichotomous α (· < ·)] :
    IsTrichotomous (WithBot α) (· < ·) :=
  @WithTop.Trichotomous.gt αᵒᵈ _ h
#align with_top._root_.with_bot.trichotomous.lt with_top._root_.with_bot.trichotomous.lt

instance _root_.with_bot.is_well_order.lt [Preorder α] [h : IsWellOrder α (· < ·)] : IsWellOrder (WithBot α) (· < ·) :=
  @WithTop.IsWellOrder.gt αᵒᵈ _ h
#align with_top._root_.with_bot.is_well_order.lt with_top._root_.with_bot.is_well_order.lt

instance _root_.with_bot.trichotomous.gt [Preorder α] [h : IsTrichotomous α (· > ·)] :
    IsTrichotomous (WithBot α) (· > ·) :=
  @WithTop.Trichotomous.lt αᵒᵈ _ h
#align with_top._root_.with_bot.trichotomous.gt with_top._root_.with_bot.trichotomous.gt

instance _root_.with_bot.is_well_order.gt [Preorder α] [h : IsWellOrder α (· > ·)] : IsWellOrder (WithBot α) (· > ·) :=
  @WithTop.IsWellOrder.lt αᵒᵈ _ h
#align with_top._root_.with_bot.is_well_order.gt with_top._root_.with_bot.is_well_order.gt

instance [LT α] [DenselyOrdered α] [NoMaxOrder α] : DenselyOrdered (WithTop α) :=
  OrderDual.densely_ordered (WithBot αᵒᵈ)

theorem lt_iff_exists_coe_btwn [Preorder α] [DenselyOrdered α] [NoMaxOrder α] {a b : WithTop α} :
    a < b ↔ ∃ x : α, a < ↑x ∧ ↑x < b :=
  ⟨fun h =>
    let ⟨y, hy⟩ := exists_between h
    let ⟨x, hx⟩ := lt_iff_exists_coe.1 hy.2
    ⟨x, hx.1 ▸ hy⟩,
    fun ⟨x, hx⟩ => lt_trans hx.1 hx.2⟩
#align with_top.lt_iff_exists_coe_btwn WithTop.lt_iff_exists_coe_btwn

instance [LE α] [NoBotOrder α] [Nonempty α] : NoBotOrder (WithTop α) :=
  OrderDual.no_bot_order (WithBot αᵒᵈ)

instance [LT α] [NoMinOrder α] [Nonempty α] : NoMinOrder (WithTop α) :=
  OrderDual.no_min_order (WithBot αᵒᵈ)

end WithTop

/-! ### Subtype, order dual, product lattices -/


namespace Subtype

variable {p : α → Prop}

-- See note [reducible non-instances]
/-- A subtype remains a `⊥`-order if the property holds at `⊥`. -/
@[reducible]
protected def orderBot [LE α] [OrderBot α] (hbot : p ⊥) : OrderBot { x : α // p x } where
  bot := ⟨⊥, hbot⟩
  bot_le _ := bot_le
#align subtype.order_bot Subtype.orderBot

-- See note [reducible non-instances]
/-- A subtype remains a `⊤`-order if the property holds at `⊤`. -/
@[reducible]
protected def orderTop [LE α] [OrderTop α] (htop : p ⊤) : OrderTop { x : α // p x } where
  top := ⟨⊤, htop⟩
  le_top _ := le_top
#align subtype.order_top Subtype.orderTop

-- See note [reducible non-instances]
/-- A subtype remains a bounded order if the property holds at `⊥` and `⊤`. -/
@[reducible]
protected def boundedOrder [LE α] [BoundedOrder α] (hbot : p ⊥) (htop : p ⊤) : BoundedOrder (Subtype p) :=
  { Subtype.orderTop htop, Subtype.orderBot hbot with }
#align subtype.bounded_order Subtype.boundedOrder

variable [PartialOrder α]

@[simp]
theorem mk_bot [OrderBot α] [OrderBot (Subtype p)] (hbot : p ⊥) : mk ⊥ hbot = ⊥ :=
  le_bot_iff.1 <| coe_le_coe.1 bot_le
#align subtype.mk_bot Subtype.mk_bot

@[simp]
theorem mk_top [OrderTop α] [OrderTop (Subtype p)] (htop : p ⊤) : mk ⊤ htop = ⊤ :=
  top_le_iff.1 <| coe_le_coe.1 le_top
#align subtype.mk_top Subtype.mk_top

theorem coe_bot [OrderBot α] [OrderBot (Subtype p)] (hbot : p ⊥) : ((⊥ : Subtype p) : α) = ⊥ :=
  congr_arg coe (mk_bot hbot).symm
#align subtype.coe_bot Subtype.coe_bot

theorem coe_top [OrderTop α] [OrderTop (Subtype p)] (htop : p ⊤) : ((⊤ : Subtype p) : α) = ⊤ :=
  congr_arg coe (mk_top htop).symm
#align subtype.coe_top Subtype.coe_top

@[simp]
theorem coe_eq_bot_iff [OrderBot α] [OrderBot (Subtype p)] (hbot : p ⊥) {x : { x // p x }} : (x : α) = ⊥ ↔ x = ⊥ := by
  rw [← coe_bot hbot, ext_iff]
#align subtype.coe_eq_bot_iff Subtype.coe_eq_bot_iff

@[simp]
theorem coe_eq_top_iff [OrderTop α] [OrderTop (Subtype p)] (htop : p ⊤) {x : { x // p x }} : (x : α) = ⊤ ↔ x = ⊤ := by
  rw [← coe_top htop, ext_iff]
#align subtype.coe_eq_top_iff Subtype.coe_eq_top_iff

@[simp]
theorem mk_eq_bot_iff [OrderBot α] [OrderBot (Subtype p)] (hbot : p ⊥) {x : α} (hx : p x) :
    (⟨x, hx⟩ : Subtype p) = ⊥ ↔ x = ⊥ :=
  (coe_eq_bot_iff hbot).symm
#align subtype.mk_eq_bot_iff Subtype.mk_eq_bot_iff

@[simp]
theorem mk_eq_top_iff [OrderTop α] [OrderTop (Subtype p)] (htop : p ⊤) {x : α} (hx : p x) :
    (⟨x, hx⟩ : Subtype p) = ⊤ ↔ x = ⊤ :=
  (coe_eq_top_iff htop).symm
#align subtype.mk_eq_top_iff Subtype.mk_eq_top_iff

end Subtype

namespace Prod

variable (α β)

instance [HasTop α] [HasTop β] : HasTop (α × β) :=
  ⟨⟨⊤, ⊤⟩⟩

instance [HasBot α] [HasBot β] : HasBot (α × β) :=
  ⟨⟨⊥, ⊥⟩⟩

instance [LE α] [LE β] [OrderTop α] [OrderTop β] : OrderTop (α × β) :=
  { Prod.hasTop α β with le_top := fun a => ⟨le_top, le_top⟩ }

instance [LE α] [LE β] [OrderBot α] [OrderBot β] : OrderBot (α × β) :=
  { Prod.hasBot α β with bot_le := fun a => ⟨bot_le, bot_le⟩ }

instance [LE α] [LE β] [BoundedOrder α] [BoundedOrder β] : BoundedOrder (α × β) :=
  { Prod.orderTop α β, Prod.orderBot α β with }

end Prod

section LinearOrder

variable [LinearOrder α]

-- `simp` can prove these, so they shouldn't be simp-lemmas.
theorem min_bot_left [OrderBot α] (a : α) : min ⊥ a = ⊥ :=
  bot_inf_eq
#align min_bot_left min_bot_left

theorem max_top_left [OrderTop α] (a : α) : max ⊤ a = ⊤ :=
  top_sup_eq
#align max_top_left max_top_left

theorem min_top_left [OrderTop α] (a : α) : min ⊤ a = a :=
  top_inf_eq
#align min_top_left min_top_left

theorem max_bot_left [OrderBot α] (a : α) : max ⊥ a = a :=
  bot_sup_eq
#align max_bot_left max_bot_left

theorem min_top_right [OrderTop α] (a : α) : min a ⊤ = a :=
  inf_top_eq
#align min_top_right min_top_right

theorem max_bot_right [OrderBot α] (a : α) : max a ⊥ = a :=
  sup_bot_eq
#align max_bot_right max_bot_right

theorem min_bot_right [OrderBot α] (a : α) : min a ⊥ = ⊥ :=
  inf_bot_eq
#align min_bot_right min_bot_right

theorem max_top_right [OrderTop α] (a : α) : max a ⊤ = ⊤ :=
  sup_top_eq
#align max_top_right max_top_right

@[simp]
theorem min_eq_bot [OrderBot α] {a b : α} : min a b = ⊥ ↔ a = ⊥ ∨ b = ⊥ := by
  simp only [← inf_eq_min, ← le_bot_iff, inf_le_iff]
#align min_eq_bot min_eq_bot

@[simp]
theorem max_eq_top [OrderTop α] {a b : α} : max a b = ⊤ ↔ a = ⊤ ∨ b = ⊤ :=
  @min_eq_bot αᵒᵈ _ _ a b
#align max_eq_top max_eq_top

@[simp]
theorem max_eq_bot [OrderBot α] {a b : α} : max a b = ⊥ ↔ a = ⊥ ∧ b = ⊥ :=
  sup_eq_bot_iff
#align max_eq_bot max_eq_bot

@[simp]
theorem min_eq_top [OrderTop α] {a b : α} : min a b = ⊤ ↔ a = ⊤ ∧ b = ⊤ :=
  inf_eq_top_iff
#align min_eq_top min_eq_top

end LinearOrder

/-! ### Disjointness and complements -/


section Disjoint

section PartialOrderBot

variable [PartialOrder α] [OrderBot α] {a b c d : α}

/-- Two elements of a lattice are disjoint if their inf is the bottom element.
  (This generalizes disjoint sets, viewed as members of the subset lattice.)

Note that we define this without reference to `⊓`, as this allows us to talk about orders where
the infimum is not unique, or where implementing `has_inf` would require additional `decidable`
arguments. -/
def Disjoint (a b : α) : Prop :=
  ∀ ⦃x⦄, x ≤ a → x ≤ b → x ≤ ⊥
#align disjoint Disjoint

theorem Disjoint.comm : Disjoint a b ↔ Disjoint b a :=
  forall_congr' fun _ => forall_swap
#align disjoint.comm Disjoint.comm

@[symm]
theorem Disjoint.symm ⦃a b : α⦄ : Disjoint a b → Disjoint b a :=
  Disjoint.comm.1
#align disjoint.symm Disjoint.symm

theorem symmetric_disjoint : Symmetric (Disjoint : α → α → Prop) :=
  Disjoint.symm
#align symmetric_disjoint symmetric_disjoint

@[simp]
theorem disjoint_bot_left : Disjoint ⊥ a := fun x hbot ha => hbot
#align disjoint_bot_left disjoint_bot_left

@[simp]
theorem disjoint_bot_right : Disjoint a ⊥ := fun x ha hbot => hbot
#align disjoint_bot_right disjoint_bot_right

theorem Disjoint.mono (h₁ : a ≤ b) (h₂ : c ≤ d) : Disjoint b d → Disjoint a c := fun h x ha hc =>
  h (ha.trans h₁) (hc.trans h₂)
#align disjoint.mono Disjoint.mono

theorem Disjoint.mono_left (h : a ≤ b) : Disjoint b c → Disjoint a c :=
  Disjoint.mono h le_rfl
#align disjoint.mono_left Disjoint.mono_left

theorem Disjoint.mono_right : b ≤ c → Disjoint a c → Disjoint a b :=
  Disjoint.mono le_rfl
#align disjoint.mono_right Disjoint.mono_right

@[simp]
theorem disjoint_self : Disjoint a a ↔ a = ⊥ :=
  ⟨fun hd => bot_unique <| hd le_rfl le_rfl, fun h x ha hb => ha.trans_eq h⟩
#align disjoint_self disjoint_self

/- TODO: Rename `disjoint.eq_bot` to `disjoint.inf_eq` and `disjoint.eq_bot_of_self` to
`disjoint.eq_bot` -/
alias disjoint_self ↔ Disjoint.eq_bot_of_self _

theorem Disjoint.ne (ha : a ≠ ⊥) (hab : Disjoint a b) : a ≠ b := fun h => ha <| disjoint_self.1 <| by rwa [← h] at hab
#align disjoint.ne Disjoint.ne

theorem Disjoint.eq_bot_of_le (hab : Disjoint a b) (h : a ≤ b) : a = ⊥ :=
  eq_bot_iff.2 <| hab le_rfl h
#align disjoint.eq_bot_of_le Disjoint.eq_bot_of_le

theorem Disjoint.eq_bot_of_ge (hab : Disjoint a b) : b ≤ a → b = ⊥ :=
  hab.symm.eq_bot_of_le
#align disjoint.eq_bot_of_ge Disjoint.eq_bot_of_ge

end PartialOrderBot

section PartialBoundedOrder

variable [PartialOrder α] [BoundedOrder α] {a : α}

@[simp]
theorem disjoint_top : Disjoint a ⊤ ↔ a = ⊥ :=
  ⟨fun h => bot_unique <| h le_rfl le_top, fun h x ha htop => ha.trans_eq h⟩
#align disjoint_top disjoint_top

@[simp]
theorem top_disjoint : Disjoint ⊤ a ↔ a = ⊥ :=
  ⟨fun h => bot_unique <| h le_top le_rfl, fun h x htop ha => ha.trans_eq h⟩
#align top_disjoint top_disjoint

end PartialBoundedOrder

section SemilatticeInfBot

variable [SemilatticeInf α] [OrderBot α] {a b c d : α}

theorem disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b ≤ ⊥ :=
  ⟨fun hd => hd inf_le_left inf_le_right, fun h x ha hb => (le_inf ha hb).trans h⟩
#align disjoint_iff_inf_le disjoint_iff_inf_le

theorem disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥ :=
  disjoint_iff_inf_le.trans le_bot_iff
#align disjoint_iff disjoint_iff

theorem Disjoint.le_bot : Disjoint a b → a ⊓ b ≤ ⊥ :=
  disjoint_iff_inf_le.mp
#align disjoint.le_bot Disjoint.le_bot

theorem Disjoint.eq_bot : Disjoint a b → a ⊓ b = ⊥ :=
  bot_unique ∘ Disjoint.le_bot
#align disjoint.eq_bot Disjoint.eq_bot

theorem disjoint_assoc : Disjoint (a ⊓ b) c ↔ Disjoint a (b ⊓ c) := by
  rw [disjoint_iff_inf_le, disjoint_iff_inf_le, inf_assoc]
#align disjoint_assoc disjoint_assoc

theorem disjoint_left_comm : Disjoint a (b ⊓ c) ↔ Disjoint b (a ⊓ c) := by simp_rw [disjoint_iff_inf_le, inf_left_comm]
#align disjoint_left_comm disjoint_left_comm

theorem disjoint_right_comm : Disjoint (a ⊓ b) c ↔ Disjoint (a ⊓ c) b := by
  simp_rw [disjoint_iff_inf_le, inf_right_comm]
#align disjoint_right_comm disjoint_right_comm

variable (c)

theorem Disjoint.inf_left (h : Disjoint a b) : Disjoint (a ⊓ c) b :=
  h.mono_left inf_le_left
#align disjoint.inf_left Disjoint.inf_left

theorem Disjoint.inf_left' (h : Disjoint a b) : Disjoint (c ⊓ a) b :=
  h.mono_left inf_le_right
#align disjoint.inf_left' Disjoint.inf_left'

theorem Disjoint.inf_right (h : Disjoint a b) : Disjoint a (b ⊓ c) :=
  h.mono_right inf_le_left
#align disjoint.inf_right Disjoint.inf_right

theorem Disjoint.inf_right' (h : Disjoint a b) : Disjoint a (c ⊓ b) :=
  h.mono_right inf_le_right
#align disjoint.inf_right' Disjoint.inf_right'

variable {c}

theorem Disjoint.of_disjoint_inf_of_le (h : Disjoint (a ⊓ b) c) (hle : a ≤ c) : Disjoint a b :=
  disjoint_iff.2 <| h.eq_bot_of_le <| inf_le_of_left_le hle
#align disjoint.of_disjoint_inf_of_le Disjoint.of_disjoint_inf_of_le

theorem Disjoint.of_disjoint_inf_of_le' (h : Disjoint (a ⊓ b) c) (hle : b ≤ c) : Disjoint a b :=
  disjoint_iff.2 <| h.eq_bot_of_le <| inf_le_of_right_le hle
#align disjoint.of_disjoint_inf_of_le' Disjoint.of_disjoint_inf_of_le'

end SemilatticeInfBot

section DistribLatticeBot

variable [DistribLattice α] [OrderBot α] {a b c : α}

@[simp]
theorem disjoint_sup_left : Disjoint (a ⊔ b) c ↔ Disjoint a c ∧ Disjoint b c := by
  simp only [disjoint_iff, inf_sup_right, sup_eq_bot_iff]
#align disjoint_sup_left disjoint_sup_left

@[simp]
theorem disjoint_sup_right : Disjoint a (b ⊔ c) ↔ Disjoint a b ∧ Disjoint a c := by
  simp only [disjoint_iff, inf_sup_left, sup_eq_bot_iff]
#align disjoint_sup_right disjoint_sup_right

theorem Disjoint.sup_left (ha : Disjoint a c) (hb : Disjoint b c) : Disjoint (a ⊔ b) c :=
  disjoint_sup_left.2 ⟨ha, hb⟩
#align disjoint.sup_left Disjoint.sup_left

theorem Disjoint.sup_right (hb : Disjoint a b) (hc : Disjoint a c) : Disjoint a (b ⊔ c) :=
  disjoint_sup_right.2 ⟨hb, hc⟩
#align disjoint.sup_right Disjoint.sup_right

theorem Disjoint.left_le_of_le_sup_right (h : a ≤ b ⊔ c) (hd : Disjoint a c) : a ≤ b :=
  le_of_inf_le_sup_le (le_trans hd.le_bot bot_le) <| sup_le h le_sup_right
#align disjoint.left_le_of_le_sup_right Disjoint.left_le_of_le_sup_right

theorem Disjoint.left_le_of_le_sup_left (h : a ≤ c ⊔ b) (hd : Disjoint a c) : a ≤ b :=
  hd.left_le_of_le_sup_right <| by rwa [sup_comm]
#align disjoint.left_le_of_le_sup_left Disjoint.left_le_of_le_sup_left

end DistribLatticeBot

end Disjoint

section Codisjoint

section PartialOrderTop

variable [PartialOrder α] [OrderTop α] {a b c d : α}

/-- Two elements of a lattice are codisjoint if their sup is the top element.

Note that we define this without reference to `⊔`, as this allows us to talk about orders where
the supremum is not unique, or where implement `has_sup` would require additional `decidable`
arguments. -/
def Codisjoint (a b : α) : Prop :=
  ∀ ⦃x⦄, a ≤ x → b ≤ x → ⊤ ≤ x
#align codisjoint Codisjoint

theorem Codisjoint.comm : Codisjoint a b ↔ Codisjoint b a :=
  forall_congr' fun _ => forall_swap
#align codisjoint.comm Codisjoint.comm

@[symm]
theorem Codisjoint.symm ⦃a b : α⦄ : Codisjoint a b → Codisjoint b a :=
  Codisjoint.comm.1
#align codisjoint.symm Codisjoint.symm

theorem symmetric_codisjoint : Symmetric (Codisjoint : α → α → Prop) :=
  Codisjoint.symm
#align symmetric_codisjoint symmetric_codisjoint

@[simp]
theorem codisjoint_top_left : Codisjoint ⊤ a := fun x htop ha => htop
#align codisjoint_top_left codisjoint_top_left

@[simp]
theorem codisjoint_top_right : Codisjoint a ⊤ := fun x ha htop => htop
#align codisjoint_top_right codisjoint_top_right

theorem Codisjoint.mono (h₁ : a ≤ b) (h₂ : c ≤ d) : Codisjoint a c → Codisjoint b d := fun h x ha hc =>
  h (h₁.trans ha) (h₂.trans hc)
#align codisjoint.mono Codisjoint.mono

theorem Codisjoint.mono_left (h : a ≤ b) : Codisjoint a c → Codisjoint b c :=
  Codisjoint.mono h le_rfl
#align codisjoint.mono_left Codisjoint.mono_left

theorem Codisjoint.mono_right : b ≤ c → Codisjoint a b → Codisjoint a c :=
  Codisjoint.mono le_rfl
#align codisjoint.mono_right Codisjoint.mono_right

@[simp]
theorem codisjoint_self : Codisjoint a a ↔ a = ⊤ :=
  ⟨fun hd => top_unique <| hd le_rfl le_rfl, fun h x ha hb => h.symm.trans_le ha⟩
#align codisjoint_self codisjoint_self

/- TODO: Rename `codisjoint.eq_top` to `codisjoint.sup_eq` and `codisjoint.eq_top_of_self` to
`codisjoint.eq_top` -/
alias codisjoint_self ↔ Codisjoint.eq_top_of_self _

theorem Codisjoint.ne (ha : a ≠ ⊤) (hab : Codisjoint a b) : a ≠ b := fun h =>
  ha <| codisjoint_self.1 <| by rwa [← h] at hab
#align codisjoint.ne Codisjoint.ne

theorem Codisjoint.eq_top_of_le (hab : Codisjoint a b) (h : b ≤ a) : a = ⊤ :=
  eq_top_iff.2 <| hab le_rfl h
#align codisjoint.eq_top_of_le Codisjoint.eq_top_of_le

theorem Codisjoint.eq_top_of_ge (hab : Codisjoint a b) : a ≤ b → b = ⊤ :=
  hab.symm.eq_top_of_le
#align codisjoint.eq_top_of_ge Codisjoint.eq_top_of_ge

end PartialOrderTop

section PartialBoundedOrder

variable [PartialOrder α] [BoundedOrder α] {a : α}

@[simp]
theorem codisjoint_bot : Codisjoint a ⊥ ↔ a = ⊤ :=
  ⟨fun h => top_unique <| h le_rfl bot_le, fun h x ha htop => h.symm.trans_le ha⟩
#align codisjoint_bot codisjoint_bot

@[simp]
theorem bot_codisjoint : Codisjoint ⊥ a ↔ a = ⊤ :=
  ⟨fun h => top_unique <| h bot_le le_rfl, fun h x htop ha => h.symm.trans_le ha⟩
#align bot_codisjoint bot_codisjoint

end PartialBoundedOrder

section SemilatticeSupTop

variable [SemilatticeSup α] [OrderTop α] {a b c d : α}

theorem codisjoint_iff_le_sup : Codisjoint a b ↔ ⊤ ≤ a ⊔ b :=
  @disjoint_iff_inf_le αᵒᵈ _ _ _ _
#align codisjoint_iff_le_sup codisjoint_iff_le_sup

theorem codisjoint_iff : Codisjoint a b ↔ a ⊔ b = ⊤ :=
  @disjoint_iff αᵒᵈ _ _ _ _
#align codisjoint_iff codisjoint_iff

theorem Codisjoint.top_le : Codisjoint a b → ⊤ ≤ a ⊔ b :=
  @Disjoint.le_bot αᵒᵈ _ _ _ _
#align codisjoint.top_le Codisjoint.top_le

theorem Codisjoint.eq_top : Codisjoint a b → a ⊔ b = ⊤ :=
  @Disjoint.eq_bot αᵒᵈ _ _ _ _
#align codisjoint.eq_top Codisjoint.eq_top

theorem codisjoint_assoc : Codisjoint (a ⊔ b) c ↔ Codisjoint a (b ⊔ c) :=
  @disjoint_assoc αᵒᵈ _ _ _ _ _
#align codisjoint_assoc codisjoint_assoc

theorem codisjoint_left_comm : Codisjoint a (b ⊔ c) ↔ Codisjoint b (a ⊔ c) :=
  @disjoint_left_comm αᵒᵈ _ _ _ _ _
#align codisjoint_left_comm codisjoint_left_comm

theorem codisjoint_right_comm : Codisjoint (a ⊔ b) c ↔ Codisjoint (a ⊔ c) b :=
  @disjoint_right_comm αᵒᵈ _ _ _ _ _
#align codisjoint_right_comm codisjoint_right_comm

variable (c)

theorem Codisjoint.sup_left (h : Codisjoint a b) : Codisjoint (a ⊔ c) b :=
  h.mono_left le_sup_left
#align codisjoint.sup_left Codisjoint.sup_left

theorem Codisjoint.sup_left' (h : Codisjoint a b) : Codisjoint (c ⊔ a) b :=
  h.mono_left le_sup_right
#align codisjoint.sup_left' Codisjoint.sup_left'

theorem Codisjoint.sup_right (h : Codisjoint a b) : Codisjoint a (b ⊔ c) :=
  h.mono_right le_sup_left
#align codisjoint.sup_right Codisjoint.sup_right

theorem Codisjoint.sup_right' (h : Codisjoint a b) : Codisjoint a (c ⊔ b) :=
  h.mono_right le_sup_right
#align codisjoint.sup_right' Codisjoint.sup_right'

variable {c}

theorem Codisjoint.of_codisjoint_sup_of_le (h : Codisjoint (a ⊔ b) c) (hle : c ≤ a) : Codisjoint a b :=
  @Disjoint.of_disjoint_inf_of_le αᵒᵈ _ _ _ _ _ h hle
#align codisjoint.of_codisjoint_sup_of_le Codisjoint.of_codisjoint_sup_of_le

theorem Codisjoint.of_codisjoint_sup_of_le' (h : Codisjoint (a ⊔ b) c) (hle : c ≤ b) : Codisjoint a b :=
  @Disjoint.of_disjoint_inf_of_le' αᵒᵈ _ _ _ _ _ h hle
#align codisjoint.of_codisjoint_sup_of_le' Codisjoint.of_codisjoint_sup_of_le'

end SemilatticeSupTop

section DistribLatticeTop

variable [DistribLattice α] [OrderTop α] {a b c : α}

@[simp]
theorem codisjoint_inf_left : Codisjoint (a ⊓ b) c ↔ Codisjoint a c ∧ Codisjoint b c := by
  simp only [codisjoint_iff, sup_inf_right, inf_eq_top_iff]
#align codisjoint_inf_left codisjoint_inf_left

@[simp]
theorem codisjoint_inf_right : Codisjoint a (b ⊓ c) ↔ Codisjoint a b ∧ Codisjoint a c := by
  simp only [codisjoint_iff, sup_inf_left, inf_eq_top_iff]
#align codisjoint_inf_right codisjoint_inf_right

theorem Codisjoint.inf_left (ha : Codisjoint a c) (hb : Codisjoint b c) : Codisjoint (a ⊓ b) c :=
  codisjoint_inf_left.2 ⟨ha, hb⟩
#align codisjoint.inf_left Codisjoint.inf_left

theorem Codisjoint.inf_right (hb : Codisjoint a b) (hc : Codisjoint a c) : Codisjoint a (b ⊓ c) :=
  codisjoint_inf_right.2 ⟨hb, hc⟩
#align codisjoint.inf_right Codisjoint.inf_right

theorem Codisjoint.left_le_of_le_inf_right (h : a ⊓ b ≤ c) (hd : Codisjoint b c) : a ≤ c :=
  @Disjoint.left_le_of_le_sup_right αᵒᵈ _ _ _ _ _ h hd.symm
#align codisjoint.left_le_of_le_inf_right Codisjoint.left_le_of_le_inf_right

theorem Codisjoint.left_le_of_le_inf_left (h : b ⊓ a ≤ c) (hd : Codisjoint b c) : a ≤ c :=
  hd.left_le_of_le_inf_right <| by rwa [inf_comm]
#align codisjoint.left_le_of_le_inf_left Codisjoint.left_le_of_le_inf_left

end DistribLatticeTop

end Codisjoint

theorem Disjoint.dual [SemilatticeInf α] [OrderBot α] {a b : α} : Disjoint a b → Codisjoint (toDual a) (toDual b) :=
  id
#align disjoint.dual Disjoint.dual

theorem Codisjoint.dual [SemilatticeSup α] [OrderTop α] {a b : α} : Codisjoint a b → Disjoint (toDual a) (toDual b) :=
  id
#align codisjoint.dual Codisjoint.dual

@[simp]
theorem disjoint_to_dual_iff [SemilatticeSup α] [OrderTop α] {a b : α} :
    Disjoint (toDual a) (toDual b) ↔ Codisjoint a b :=
  Iff.rfl
#align disjoint_to_dual_iff disjoint_to_dual_iff

@[simp]
theorem disjoint_of_dual_iff [SemilatticeInf α] [OrderBot α] {a b : αᵒᵈ} :
    Disjoint (ofDual a) (ofDual b) ↔ Codisjoint a b :=
  Iff.rfl
#align disjoint_of_dual_iff disjoint_of_dual_iff

@[simp]
theorem codisjoint_to_dual_iff [SemilatticeInf α] [OrderBot α] {a b : α} :
    Codisjoint (toDual a) (toDual b) ↔ Disjoint a b :=
  Iff.rfl
#align codisjoint_to_dual_iff codisjoint_to_dual_iff

@[simp]
theorem codisjoint_of_dual_iff [SemilatticeSup α] [OrderTop α] {a b : αᵒᵈ} :
    Codisjoint (ofDual a) (ofDual b) ↔ Disjoint a b :=
  Iff.rfl
#align codisjoint_of_dual_iff codisjoint_of_dual_iff

section DistribLattice

variable [DistribLattice α] [BoundedOrder α] {a b c : α}

theorem Disjoint.le_of_codisjoint (hab : Disjoint a b) (hbc : Codisjoint b c) : a ≤ c := by
  rw [← @inf_top_eq _ _ _ a, ← @bot_sup_eq _ _ _ c, ← hab.eq_bot, ← hbc.eq_top, sup_inf_right]
  exact inf_le_inf_right _ le_sup_left
#align disjoint.le_of_codisjoint Disjoint.le_of_codisjoint

end DistribLattice

section IsCompl

/-- Two elements `x` and `y` are complements of each other if `x ⊔ y = ⊤` and `x ⊓ y = ⊥`. -/
@[protect_proj]
structure IsCompl [PartialOrder α] [BoundedOrder α] (x y : α) : Prop where
  Disjoint : Disjoint x y
  Codisjoint : Codisjoint x y
#align is_compl IsCompl

theorem is_compl_iff [PartialOrder α] [BoundedOrder α] {a b : α} : IsCompl a b ↔ Disjoint a b ∧ Codisjoint a b :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
#align is_compl_iff is_compl_iff

namespace IsCompl

section BoundedPartialOrder

variable [PartialOrder α] [BoundedOrder α] {x y z : α}

@[symm]
protected theorem symm (h : IsCompl x y) : IsCompl y x :=
  ⟨h.1.symm, h.2.symm⟩
#align is_compl.symm IsCompl.symm

theorem dual (h : IsCompl x y) : IsCompl (toDual x) (toDual y) :=
  ⟨h.2, h.1⟩
#align is_compl.dual IsCompl.dual

theorem of_dual {a b : αᵒᵈ} (h : IsCompl a b) : IsCompl (ofDual a) (ofDual b) :=
  ⟨h.2, h.1⟩
#align is_compl.of_dual IsCompl.of_dual

end BoundedPartialOrder

section BoundedLattice

variable [Lattice α] [BoundedOrder α] {x y z : α}

theorem of_le (h₁ : x ⊓ y ≤ ⊥) (h₂ : ⊤ ≤ x ⊔ y) : IsCompl x y :=
  ⟨disjoint_iff_inf_le.mpr h₁, codisjoint_iff_le_sup.mpr h₂⟩
#align is_compl.of_le IsCompl.of_le

theorem of_eq (h₁ : x ⊓ y = ⊥) (h₂ : x ⊔ y = ⊤) : IsCompl x y :=
  ⟨disjoint_iff.mpr h₁, codisjoint_iff.mpr h₂⟩
#align is_compl.of_eq IsCompl.of_eq

theorem inf_eq_bot (h : IsCompl x y) : x ⊓ y = ⊥ :=
  h.Disjoint.eq_bot
#align is_compl.inf_eq_bot IsCompl.inf_eq_bot

theorem sup_eq_top (h : IsCompl x y) : x ⊔ y = ⊤ :=
  h.Codisjoint.eq_top
#align is_compl.sup_eq_top IsCompl.sup_eq_top

end BoundedLattice

variable [DistribLattice α] [BoundedOrder α] {a b x y z : α}

theorem inf_left_le_of_le_sup_right (h : IsCompl x y) (hle : a ≤ b ⊔ y) : a ⊓ x ≤ b :=
  calc
    a ⊓ x ≤ (b ⊔ y) ⊓ x := inf_le_inf hle le_rfl
    _ = b ⊓ x ⊔ y ⊓ x := inf_sup_right
    _ = b ⊓ x := by rw [h.symm.inf_eq_bot, sup_bot_eq]
    _ ≤ b := inf_le_left
    
#align is_compl.inf_left_le_of_le_sup_right IsCompl.inf_left_le_of_le_sup_right

theorem le_sup_right_iff_inf_left_le {a b} (h : IsCompl x y) : a ≤ b ⊔ y ↔ a ⊓ x ≤ b :=
  ⟨h.inf_left_le_of_le_sup_right, h.symm.dual.inf_left_le_of_le_sup_right⟩
#align is_compl.le_sup_right_iff_inf_left_le IsCompl.le_sup_right_iff_inf_left_le

theorem inf_left_eq_bot_iff (h : IsCompl y z) : x ⊓ y = ⊥ ↔ x ≤ z := by
  rw [← le_bot_iff, ← h.le_sup_right_iff_inf_left_le, bot_sup_eq]
#align is_compl.inf_left_eq_bot_iff IsCompl.inf_left_eq_bot_iff

theorem inf_right_eq_bot_iff (h : IsCompl y z) : x ⊓ z = ⊥ ↔ x ≤ y :=
  h.symm.inf_left_eq_bot_iff
#align is_compl.inf_right_eq_bot_iff IsCompl.inf_right_eq_bot_iff

theorem disjoint_left_iff (h : IsCompl y z) : Disjoint x y ↔ x ≤ z := by
  rw [disjoint_iff]
  exact h.inf_left_eq_bot_iff
#align is_compl.disjoint_left_iff IsCompl.disjoint_left_iff

theorem disjoint_right_iff (h : IsCompl y z) : Disjoint x z ↔ x ≤ y :=
  h.symm.disjoint_left_iff
#align is_compl.disjoint_right_iff IsCompl.disjoint_right_iff

theorem le_left_iff (h : IsCompl x y) : z ≤ x ↔ Disjoint z y :=
  h.disjoint_right_iff.symm
#align is_compl.le_left_iff IsCompl.le_left_iff

theorem le_right_iff (h : IsCompl x y) : z ≤ y ↔ Disjoint z x :=
  h.symm.le_left_iff
#align is_compl.le_right_iff IsCompl.le_right_iff

theorem left_le_iff (h : IsCompl x y) : x ≤ z ↔ Codisjoint z y :=
  h.dual.le_left_iff
#align is_compl.left_le_iff IsCompl.left_le_iff

theorem right_le_iff (h : IsCompl x y) : y ≤ z ↔ Codisjoint z x :=
  h.symm.left_le_iff
#align is_compl.right_le_iff IsCompl.right_le_iff

protected theorem antitone {x' y'} (h : IsCompl x y) (h' : IsCompl x' y') (hx : x ≤ x') : y' ≤ y :=
  h'.right_le_iff.2 <| h.symm.Codisjoint.mono_right hx
#align is_compl.antitone IsCompl.antitone

theorem right_unique (hxy : IsCompl x y) (hxz : IsCompl x z) : y = z :=
  le_antisymm (hxz.Antitone hxy <| le_refl x) (hxy.Antitone hxz <| le_refl x)
#align is_compl.right_unique IsCompl.right_unique

theorem left_unique (hxz : IsCompl x z) (hyz : IsCompl y z) : x = y :=
  hxz.symm.RightUnique hyz.symm
#align is_compl.left_unique IsCompl.left_unique

theorem sup_inf {x' y'} (h : IsCompl x y) (h' : IsCompl x' y') : IsCompl (x ⊔ x') (y ⊓ y') :=
  of_eq
    (by rw [inf_sup_right, ← inf_assoc, h.inf_eq_bot, bot_inf_eq, bot_sup_eq, inf_left_comm, h'.inf_eq_bot, inf_bot_eq])
    (by
      rw [sup_inf_left, @sup_comm _ _ x, sup_assoc, h.sup_eq_top, sup_top_eq, top_inf_eq, sup_assoc, sup_left_comm,
        h'.sup_eq_top, sup_top_eq])
#align is_compl.sup_inf IsCompl.sup_inf

theorem inf_sup {x' y'} (h : IsCompl x y) (h' : IsCompl x' y') : IsCompl (x ⊓ x') (y ⊔ y') :=
  (h.symm.sup_inf h'.symm).symm
#align is_compl.inf_sup IsCompl.inf_sup

end IsCompl

namespace Prod

variable [PartialOrder α] [PartialOrder β]

protected theorem disjoint_iff [OrderBot α] [OrderBot β] {x y : α × β} :
    Disjoint x y ↔ Disjoint x.1 y.1 ∧ Disjoint x.2 y.2 := by
  constructor
  · intro h
    refine' ⟨fun a hx hy => (@h (a, ⊥) ⟨hx, _⟩ ⟨hy, _⟩).1, fun b hx hy => (@h (⊥, b) ⟨_, hx⟩ ⟨_, hy⟩).2⟩
    all_goals exact bot_le
    
  · rintro ⟨ha, hb⟩ z hza hzb
    refine' ⟨ha hza.1 hzb.1, hb hza.2 hzb.2⟩
    
#align prod.disjoint_iff Prod.disjoint_iff

protected theorem codisjoint_iff [OrderTop α] [OrderTop β] {x y : α × β} :
    Codisjoint x y ↔ Codisjoint x.1 y.1 ∧ Codisjoint x.2 y.2 :=
  @Prod.disjoint_iff αᵒᵈ βᵒᵈ _ _ _ _ _ _
#align prod.codisjoint_iff Prod.codisjoint_iff

protected theorem is_compl_iff [BoundedOrder α] [BoundedOrder β] {x y : α × β} :
    IsCompl x y ↔ IsCompl x.1 y.1 ∧ IsCompl x.2 y.2 := by
  simp_rw [is_compl_iff, Prod.disjoint_iff, Prod.codisjoint_iff, and_and_and_comm]
#align prod.is_compl_iff Prod.is_compl_iff

end Prod

namespace Pi

variable {ι : Type _} {α' : ι → Type _} [∀ i, PartialOrder (α' i)]

theorem disjoint_iff [∀ i, OrderBot (α' i)] {f g : ∀ i, α' i} : Disjoint f g ↔ ∀ i, Disjoint (f i) (g i) := by
  constructor
  · intro h i x hf hg
    refine' (update_le_iff.mp <| h (update_le_iff.mpr ⟨hf, fun _ _ => _⟩) (update_le_iff.mpr ⟨hg, fun _ _ => _⟩)).1
    · exact ⊥
      
    · exact bot_le
      
    · exact bot_le
      
    
  · intro h x hf hg i
    apply h i (hf i) (hg i)
    
#align pi.disjoint_iff Pi.disjoint_iff

theorem codisjoint_iff [∀ i, OrderTop (α' i)] {f g : ∀ i, α' i} : Codisjoint f g ↔ ∀ i, Codisjoint (f i) (g i) :=
  @disjoint_iff _ (fun i => (α' i)ᵒᵈ) _ _ _ _
#align pi.codisjoint_iff Pi.codisjoint_iff

theorem is_compl_iff [∀ i, BoundedOrder (α' i)] {f g : ∀ i, α' i} : IsCompl f g ↔ ∀ i, IsCompl (f i) (g i) := by
  simp_rw [is_compl_iff, disjoint_iff, codisjoint_iff, forall_and]
#align pi.is_compl_iff Pi.is_compl_iff

end Pi

@[simp]
theorem PropCat.disjoint_iff {P Q : Prop} : Disjoint P Q ↔ ¬(P ∧ Q) :=
  disjoint_iff_inf_le
#align Prop.disjoint_iff PropCat.disjoint_iff

@[simp]
theorem PropCat.codisjoint_iff {P Q : Prop} : Codisjoint P Q ↔ P ∨ Q :=
  codisjoint_iff_le_sup.trans <| forall_const _
#align Prop.codisjoint_iff PropCat.codisjoint_iff

@[simp]
theorem PropCat.is_compl_iff {P Q : Prop} : IsCompl P Q ↔ ¬(P ↔ Q) := by
  rw [is_compl_iff, PropCat.disjoint_iff, PropCat.codisjoint_iff, not_iff]
  tauto
#align Prop.is_compl_iff PropCat.is_compl_iff

section

variable [Lattice α] [BoundedOrder α] {a b x : α}

@[simp]
theorem is_compl_to_dual_iff : IsCompl (toDual a) (toDual b) ↔ IsCompl a b :=
  ⟨IsCompl.of_dual, IsCompl.dual⟩
#align is_compl_to_dual_iff is_compl_to_dual_iff

@[simp]
theorem is_compl_of_dual_iff {a b : αᵒᵈ} : IsCompl (ofDual a) (ofDual b) ↔ IsCompl a b :=
  ⟨IsCompl.dual, IsCompl.of_dual⟩
#align is_compl_of_dual_iff is_compl_of_dual_iff

theorem is_compl_bot_top : IsCompl (⊥ : α) ⊤ :=
  IsCompl.of_eq bot_inf_eq sup_top_eq
#align is_compl_bot_top is_compl_bot_top

theorem is_compl_top_bot : IsCompl (⊤ : α) ⊥ :=
  IsCompl.of_eq inf_bot_eq top_sup_eq
#align is_compl_top_bot is_compl_top_bot

theorem eq_top_of_is_compl_bot (h : IsCompl x ⊥) : x = ⊤ :=
  sup_bot_eq.symm.trans h.sup_eq_top
#align eq_top_of_is_compl_bot eq_top_of_is_compl_bot

theorem eq_top_of_bot_is_compl (h : IsCompl ⊥ x) : x = ⊤ :=
  eq_top_of_is_compl_bot h.symm
#align eq_top_of_bot_is_compl eq_top_of_bot_is_compl

theorem eq_bot_of_is_compl_top (h : IsCompl x ⊤) : x = ⊥ :=
  eq_top_of_is_compl_bot h.dual
#align eq_bot_of_is_compl_top eq_bot_of_is_compl_top

theorem eq_bot_of_top_is_compl (h : IsCompl ⊤ x) : x = ⊥ :=
  eq_top_of_bot_is_compl h.dual
#align eq_bot_of_top_is_compl eq_bot_of_top_is_compl

end

/-- A complemented bounded lattice is one where every element has a (not necessarily unique)
complement. -/
class ComplementedLattice (α) [Lattice α] [BoundedOrder α] : Prop where
  exists_is_compl : ∀ a : α, ∃ b : α, IsCompl a b
#align complemented_lattice ComplementedLattice

export ComplementedLattice (exists_is_compl)

namespace ComplementedLattice

variable [Lattice α] [BoundedOrder α] [ComplementedLattice α]

instance : ComplementedLattice αᵒᵈ :=
  ⟨fun a =>
    let ⟨b, hb⟩ := exists_is_compl (show α from a)
    ⟨b, hb.dual⟩⟩

end ComplementedLattice

end IsCompl

section Nontrivial

variable [PartialOrder α] [BoundedOrder α] [Nontrivial α]

@[simp]
theorem bot_ne_top : (⊥ : α) ≠ ⊤ := fun h => not_subsingleton _ <| subsingleton_of_bot_eq_top h
#align bot_ne_top bot_ne_top

@[simp]
theorem top_ne_bot : (⊤ : α) ≠ ⊥ :=
  bot_ne_top.symm
#align top_ne_bot top_ne_bot

@[simp]
theorem bot_lt_top : (⊥ : α) < ⊤ :=
  lt_top_iff_ne_top.2 bot_ne_top
#align bot_lt_top bot_lt_top

end Nontrivial

section Bool

open Bool

instance : BoundedOrder Bool where
  top := true
  le_top x := le_true
  bot := false
  bot_le x := false_le

@[simp]
theorem top_eq_tt : ⊤ = tt :=
  rfl
#align top_eq_tt top_eq_tt

@[simp]
theorem bot_eq_ff : ⊥ = ff :=
  rfl
#align bot_eq_ff bot_eq_ff

end Bool

