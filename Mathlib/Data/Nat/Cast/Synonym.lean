/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Group.Synonym
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Order.Synonym

/-!
# Cast of natural numbers (additional theorems)

This file proves additional properties about the *canonical* homomorphism from
the natural numbers into an additive monoid with a one (`Nat.cast`).
-/

@[expose] public section

variable {α : Type*}

/-! ### Order dual -/


open OrderDual

instance [h : NatCast α] : NatCast αᵒᵈ where
  natCast n := toDual n

instance [h : AddMonoidWithOne α] : AddMonoidWithOne αᵒᵈ where
  __ := inferInstanceAs (AddMonoid αᵒᵈ)
  __ := inferInstanceAs (One αᵒᵈ)
  __ := inferInstanceAs (NatCast αᵒᵈ)
  natCast_zero := congrArg toDual (Nat.cast_zero)
  natCast_succ n := congrArg toDual (Nat.cast_succ n)

instance [h : AddCommMonoidWithOne α] : AddCommMonoidWithOne αᵒᵈ where
  __ := inferInstanceAs (AddMonoidWithOne αᵒᵈ)
  __ := inferInstanceAs (AddCommMonoid αᵒᵈ)

instance [h : IntCast α] : IntCast αᵒᵈ where
  intCast n := toDual (n : α)

@[simp]
theorem toDual_natCast [NatCast α] (n : ℕ) : toDual (n : α) = (n : αᵒᵈ) :=
  rfl

@[simp]
theorem ofDual_natCast [NatCast α] (n : ℕ) : ofDual (n : αᵒᵈ) = (n : α) :=
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
