/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Order.WithBot
import Mathlib.Algebra.Order.Monoid.Unbundled.OrderDual

#align_import algebra.order.monoid.with_top from "leanprover-community/mathlib"@"0111834459f5d7400215223ea95ae38a1265a907"

/-! # Adjoining top/bottom elements to ordered monoids.
-/

universe u v

variable {α : Type u} {β : Type v}

open Function

namespace WithTop

section One

variable [One α] {a : α}

@[to_additive]
instance one : One (WithTop α) :=
  ⟨(1 : α)⟩
#align with_top.has_one WithTop.one
#align with_top.has_zero WithTop.zero

@[to_additive (attr := simp, norm_cast)]
theorem coe_one : ((1 : α) : WithTop α) = 1 :=
  rfl
#align with_top.coe_one WithTop.coe_one
#align with_top.coe_zero WithTop.coe_zero

@[to_additive (attr := simp, norm_cast)]
lemma coe_eq_one : (a : WithTop α) = 1 ↔ a = 1 := coe_eq_coe
#align with_top.coe_eq_one WithTop.coe_eq_one
#align with_top.coe_eq_zero WithTop.coe_eq_zero

@[to_additive (attr := simp, norm_cast)]
lemma one_eq_coe : 1 = (a : WithTop α) ↔ a = 1 := eq_comm.trans coe_eq_one
#align with_top.one_eq_coe WithTop.one_eq_coe
#align with_top.zero_eq_coe WithTop.zero_eq_coe

@[to_additive (attr := simp)] lemma top_ne_one : (⊤ : WithTop α) ≠ 1 := top_ne_coe
#align with_top.top_ne_one WithTop.top_ne_one
#align with_top.top_ne_zero WithTop.top_ne_zero

@[to_additive (attr := simp)] lemma one_ne_top : (1 : WithTop α) ≠ ⊤ := coe_ne_top
#align with_top.one_ne_top WithTop.one_ne_top
#align with_top.zero_ne_top WithTop.zero_ne_top

@[to_additive (attr := simp)]
theorem untop_one : (1 : WithTop α).untop coe_ne_top = 1 :=
  rfl
#align with_top.untop_one WithTop.untop_one
#align with_top.untop_zero WithTop.untop_zero

@[to_additive (attr := simp)]
theorem untop_one' (d : α) : (1 : WithTop α).untop' d = 1 :=
  rfl
#align with_top.untop_one' WithTop.untop_one'
#align with_top.untop_zero' WithTop.untop_zero'

@[to_additive (attr := simp, norm_cast) coe_nonneg]
theorem one_le_coe [LE α] {a : α} : 1 ≤ (a : WithTop α) ↔ 1 ≤ a :=
  coe_le_coe
#align with_top.one_le_coe WithTop.one_le_coe
#align with_top.coe_nonneg WithTop.coe_nonneg

@[to_additive (attr := simp, norm_cast) coe_le_zero]
theorem coe_le_one [LE α] {a : α} : (a : WithTop α) ≤ 1 ↔ a ≤ 1 :=
  coe_le_coe
#align with_top.coe_le_one WithTop.coe_le_one
#align with_top.coe_le_zero WithTop.coe_le_zero

@[to_additive (attr := simp, norm_cast) coe_pos]
theorem one_lt_coe [LT α] {a : α} : 1 < (a : WithTop α) ↔ 1 < a :=
  coe_lt_coe
#align with_top.one_lt_coe WithTop.one_lt_coe
#align with_top.coe_pos WithTop.coe_pos

@[to_additive (attr := simp, norm_cast) coe_lt_zero]
theorem coe_lt_one [LT α] {a : α} : (a : WithTop α) < 1 ↔ a < 1 :=
  coe_lt_coe
#align with_top.coe_lt_one WithTop.coe_lt_one
#align with_top.coe_lt_zero WithTop.coe_lt_zero

@[to_additive (attr := simp)]
protected theorem map_one {β} (f : α → β) : (1 : WithTop α).map f = (f 1 : WithTop β) :=
  rfl
#align with_top.map_one WithTop.map_one
#align with_top.map_zero WithTop.map_zero


instance zeroLEOneClass [Zero α] [One α] [LE α] [ZeroLEOneClass α] : ZeroLEOneClass (WithTop α) :=
  ⟨coe_le_coe.2 zero_le_one⟩

end One

end WithTop

namespace WithBot
section One
variable [One α] {a : α}

@[to_additive] instance one : One (WithBot α) := WithTop.one

@[to_additive (attr := simp, norm_cast)] lemma coe_one : ((1 : α) : WithBot α) = 1 := rfl
#align with_bot.coe_one WithBot.coe_one
#align with_bot.coe_zero WithBot.coe_zero

@[to_additive (attr := simp, norm_cast)]
lemma coe_eq_one : (a : WithBot α) = 1 ↔ a = 1 := coe_eq_coe
#align with_bot.coe_eq_one WithBot.coe_eq_one
#align with_bot.coe_eq_zero WithBot.coe_eq_zero

@[to_additive (attr := simp, norm_cast)]
lemma one_eq_coe : 1 = (a : WithBot α) ↔ a = 1 := eq_comm.trans coe_eq_one

@[to_additive (attr := simp)] lemma bot_ne_one : (⊥ : WithBot α) ≠ 1 := bot_ne_coe
@[to_additive (attr := simp)] lemma one_ne_bot : (1 : WithBot α) ≠ ⊥ := coe_ne_bot

@[to_additive (attr := simp)]
theorem unbot_one : (1 : WithBot α).unbot coe_ne_bot = 1 :=
  rfl
#align with_bot.unbot_one WithBot.unbot_one
#align with_bot.unbot_zero WithBot.unbot_zero

@[to_additive (attr := simp)]
theorem unbot_one' (d : α) : (1 : WithBot α).unbot' d = 1 :=
  rfl
#align with_bot.unbot_one' WithBot.unbot_one'
#align with_bot.unbot_zero' WithBot.unbot_zero'

@[to_additive (attr := simp, norm_cast) coe_nonneg]
theorem one_le_coe [LE α] : 1 ≤ (a : WithBot α) ↔ 1 ≤ a := coe_le_coe
#align with_bot.one_le_coe WithBot.one_le_coe
#align with_bot.coe_nonneg WithBot.coe_nonneg

@[to_additive (attr := simp, norm_cast) coe_le_zero]
theorem coe_le_one [LE α] : (a : WithBot α) ≤ 1 ↔ a ≤ 1 := coe_le_coe
#align with_bot.coe_le_one WithBot.coe_le_one
#align with_bot.coe_le_zero WithBot.coe_le_zero

@[to_additive (attr := simp, norm_cast) coe_pos]
theorem one_lt_coe [LT α] : 1 < (a : WithBot α) ↔ 1 < a := coe_lt_coe
#align with_bot.one_lt_coe WithBot.one_lt_coe
#align with_bot.coe_pos WithBot.coe_pos

@[to_additive (attr := simp, norm_cast) coe_lt_zero]
theorem coe_lt_one [LT α] : (a : WithBot α) < 1 ↔ a < 1 := coe_lt_coe
#align with_bot.coe_lt_one WithBot.coe_lt_one
#align with_bot.coe_lt_zero WithBot.coe_lt_zero

@[to_additive (attr := simp)]
protected theorem map_one {β} (f : α → β) : (1 : WithBot α).map f = (f 1 : WithBot β) :=
  rfl
#align with_bot.map_one WithBot.map_one
#align with_bot.map_zero WithBot.map_zero

instance zeroLEOneClass [Zero α] [LE α] [ZeroLEOneClass α] : ZeroLEOneClass (WithBot α) :=
  ⟨coe_le_coe.2 zero_le_one⟩

end One

end WithBot
