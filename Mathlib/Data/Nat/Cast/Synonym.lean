/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Order.Synonym

#align_import data.nat.cast.basic from "leanprover-community/mathlib"@"acebd8d49928f6ed8920e502a6c90674e75bd441"

/-!
# Cast of natural numbers (additional theorems)

This file proves additional properties about the *canonical* homomorphism from
the natural numbers into an additive monoid with a one (`Nat.cast`).

## Main declarations

* `castAddMonoidHom`: `cast` bundled as an `AddMonoidHom`.
* `castRingHom`: `cast` bundled as a `RingHom`.
-/

-- Porting note: There are many occasions below where we need `simp [map_zero f]`
-- where `simp [map_zero]` should suffice. (Similarly for `map_one`.)
-- See https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/simp.20regression.20with.20MonoidHomClass

variable {α β : Type*}

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
#align to_dual_nat_cast toDual_natCast

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem toDual_ofNat [NatCast α] (n : ℕ) [n.AtLeastTwo] :
    (toDual (no_index (OfNat.ofNat n : α))) = OfNat.ofNat n :=
  rfl

@[simp]
theorem ofDual_natCast [NatCast α] (n : ℕ) : (ofDual n : α) = n :=
  rfl
#align of_dual_nat_cast ofDual_natCast

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem ofDual_ofNat [NatCast α] (n : ℕ) [n.AtLeastTwo] :
    (ofDual (no_index (OfNat.ofNat n : αᵒᵈ))) = OfNat.ofNat n :=
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
#align to_lex_nat_cast toLex_natCast

@[simp]
theorem toLex_ofNat [NatCast α] (n : ℕ) [n.AtLeastTwo] :
    (toLex (no_index (OfNat.ofNat n : α))) = OfNat.ofNat n :=
  rfl

@[simp]
theorem ofLex_natCast [NatCast α] (n : ℕ) : (ofLex n : α) = n :=
  rfl

@[simp]
theorem ofLex_ofNat [NatCast α] (n : ℕ) [n.AtLeastTwo] :
    (ofLex (no_index (OfNat.ofNat n : Lex α))) = OfNat.ofNat n :=
  rfl

#align of_lex_nat_cast ofLex_natCast
