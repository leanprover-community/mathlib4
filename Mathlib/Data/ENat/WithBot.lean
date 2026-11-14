/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Data.ENat.Basic
public import Mathlib.Order.WithBotTop

/-!

# Lemmas for WithBot ENat

-/

public section

namespace ENat.WithBot

lemma eq_natCast_of_ne_bot_of_ne_top {x : WithBot ℕ∞} (ne1 : x ≠ ⊥) (ne2 : x ≠ ⊤) :
    ∃ n : ℕ, x = n :=
  WithBotTop.eq_coe_of_ne_bot_of_ne_top ne1 ne2

/-- A recursor for `WithBot ℕ∞` in terms of the `NatCast`. -/
@[induction_eliminator]
def recBotTopCoe {C : WithBot ℕ∞ → Sort*} (bot : C ⊥) (top : C ⊤) (coe : ∀ n : ℕ, C n) : ∀ x, C x
  | ⊥ => bot
  | (m : ℕ∞) => by
    induction m with
    | top => exact top
    | coe n => exact coe n

end ENat.WithBot
