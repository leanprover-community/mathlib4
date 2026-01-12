/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Kevin Buzzard
-/
module

public import Mathlib.Order.WithBot

/-!
# The extended integers

This file defines `EInt`, `ℤ` with a top element `⊤` and a bottom element `⊥`,
implemented as `WithBot (WithTop ℤ)`.

-/

@[expose] public section

/-- The type of extended integers `[-∞, ∞]`, constructed as `WithBot (WithTop ℤ)`. -/
def EInt := WithBot (WithTop ℤ)

/-- The canonical inclusion from integers to e-integers. Registered as a coercion. -/
@[coe] def Int.toEInt : ℤ → EInt := WithBot.some ∘ WithTop.some

namespace EInt

instance : LinearOrder EInt := inferInstanceAs (LinearOrder (WithBot (WithTop ℤ)))

instance : OrderBot EInt := inferInstanceAs (OrderBot (WithBot (WithTop ℤ)))

instance : OrderTop EInt := inferInstanceAs (OrderTop (WithBot (WithTop ℤ)))

instance : Coe ℤ EInt := ⟨Int.toEInt⟩

theorem coe_strictMono : StrictMono Int.toEInt :=
  WithBot.coe_strictMono.comp WithTop.coe_strictMono

theorem coe_injective : Function.Injective Int.toEInt :=
  coe_strictMono.injective

lemma coe_monotone : Monotone Int.toEInt := coe_strictMono.monotone

section

variable {motive : EInt → Sort*}
  (bot : motive ⊥) (coe : ∀ a : ℤ, motive a) (top : motive ⊤)

/-- A recursor for `EInt` in terms of the coercion. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
protected def rec : ∀ a : EInt, motive a
  | ⊥ => bot
  | (a : ℤ) => coe a
  | ⊤ => top

@[simp] lemma rec_bot : EInt.rec (motive := motive) bot coe top ⊥ = bot := rfl
@[simp] lemma rec_coe (a : ℤ) : EInt.rec (motive := motive) bot coe top a = coe a := rfl
@[simp] lemma rec_top : EInt.rec (motive := motive) bot coe top ⊤ = top := rfl

end

@[simp]
lemma coe_le_coe_iff (a b : ℤ) :
    (a : EInt) ≤ b ↔ a ≤ b :=
  coe_strictMono.le_iff_le

@[simp]
lemma coe_lt_coe_iff (a b : ℤ) :
    (a : EInt) < b ↔ a < b :=
  coe_strictMono.lt_iff_lt

@[simp]
lemma coe_eq_bot_iff (a : ℤ) :
    (a : EInt) = ⊥ ↔ False := by
  simp only [iff_false]
  rintro ⟨⟩

@[simp]
lemma coe_eq_top_iff (a : ℤ) :
    (a : EInt) = ⊤ ↔ False := by
  simp only [iff_false]
  rintro ⟨⟩

@[simp]
lemma top_eq_bot_iff :
    (⊤ : EInt) = ⊥ ↔ False := by
  simp only [iff_false]
  exact ne_of_beq_false rfl

end EInt
