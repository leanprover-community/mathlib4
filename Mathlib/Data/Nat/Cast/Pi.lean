/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Moritz Doll
-/
module

public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Push.Attr

/-!
# Cast of integers to function types

This file provides a (pointwise) cast from `ℕ` to function types.

## Main declarations

* `Pi.instNatCast`: map `n : ℕ` to the constant function `n : ∀ i, π i`
-/

@[expose] public section

assert_not_exists IsOrderedMonoid RingHom

namespace Pi

variable {ι : Type*} {π : ι → Type*} [∀ i, NatCast (π i)]

instance instNatCast : NatCast (∀ i, π i) where natCast n _ := n

@[simp]
theorem natCast_apply (n : ℕ) (i : ι) : (n : ∀ i, π i) i = n :=
  rfl

@[push ←]
theorem natCast_def (n : ℕ) : (n : ∀ i, π i) = fun _ => ↑n :=
  rfl

end Pi

@[simp]
theorem Sum.elim_natCast_natCast {α β γ : Type*} [NatCast γ] (n : ℕ) :
    Sum.elim (n : α → γ) (n : β → γ) = n :=
  Sum.elim_lam_const_lam_const (γ := γ) n
