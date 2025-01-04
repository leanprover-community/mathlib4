/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Batteries.Tactic.Alias
import Mathlib.Data.Int.Notation
import Mathlib.Tactic.TypeStar
import Mathlib.Util.AssertExists

/-!
# Cast of integers to function types

This file provides a (pointwise) cast from `ℤ` to function types.

## Main declarations

* `Pi.instIntCast`: map `n : ℤ` to the constant function `n : ∀ i, π i`
-/

assert_not_exists OrderedCommMonoid
assert_not_exists RingHom

namespace Pi

variable {ι : Type*} {π : ι → Type*} [∀ i, IntCast (π i)]

instance instIntCast : IntCast (∀ i, π i) where intCast n _ := n

theorem intCast_apply (n : ℤ) (i : ι) : (n : ∀ i, π i) i = n :=
  rfl

@[simp]
theorem intCast_def (n : ℤ) : (n : ∀ i, π i) = fun _ => ↑n :=
  rfl

@[deprecated (since := "2024-04-05")] alias int_apply := intCast_apply
@[deprecated (since := "2024-04-05")] alias coe_int := intCast_def

end Pi

theorem Sum.elim_intCast_intCast {α β γ : Type*} [IntCast γ] (n : ℤ) :
    Sum.elim (n : α → γ) (n : β → γ) = n :=
  Sum.elim_lam_const_lam_const (γ := γ) n
