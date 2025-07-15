/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Order.Synonym

/-!
# Cast of natural numbers (additional theorems)

This file proves additional properties about the *canonical* homomorphism from
the natural numbers into an additive monoid with a one (`Nat.cast`).
-/

variable {α : Type*}

/-! ### Order dual -/


open OrderDual

instance [h : NatCast α] : NatCast αᵒᵈ :=
  h

instance [h : AddMonoidWithOne α] : AddMonoidWithOne αᵒᵈ :=
  h

instance [h : AddCommMonoidWithOne α] : AddCommMonoidWithOne αᵒᵈ :=
  h

@[simp]
theorem toDual_natCast [NatCast α] (n : ℕ) : toDual (n : α) = n :=
  rfl

@[simp]
theorem toDual_ofNat [NatCast α] (n : ℕ) [n.AtLeastTwo] :
    (toDual (ofNat(n) : α)) = ofNat(n) :=
  rfl

@[simp]
theorem ofDual_natCast [NatCast α] (n : ℕ) : (ofDual n : α) = n :=
  rfl

@[simp]
theorem ofDual_ofNat [NatCast α] (n : ℕ) [n.AtLeastTwo] :
    (ofDual (ofNat(n) : αᵒᵈ)) = ofNat(n) :=
  rfl

/-! ### Lexicographic order -/


instance [h : NatCast α] : NatCast (Lex α) :=
  h

instance [h : AddMonoidWithOne α] : AddMonoidWithOne (Lex α) :=
  h

instance [h : AddCommMonoidWithOne α] : AddCommMonoidWithOne (Lex α) :=
  h

@[simp]
theorem toLex_natCast [NatCast α] (n : ℕ) : toLex (n : α) = n :=
  rfl

@[simp]
theorem toLex_ofNat [NatCast α] (n : ℕ) [n.AtLeastTwo] :
    toLex (ofNat(n) : α) = OfNat.ofNat n :=
  rfl

@[simp]
theorem ofLex_natCast [NatCast α] (n : ℕ) : (ofLex n : α) = n :=
  rfl

@[simp]
theorem ofLex_ofNat [NatCast α] (n : ℕ) [n.AtLeastTwo] :
    ofLex (ofNat(n) : Lex α) = OfNat.ofNat n :=
  rfl
