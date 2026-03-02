/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Tactic.InferInstanceAsPercent

/-!
# Tests for `inferInstanceAs%`

Demonstrates that `inferInstanceAs%` fixes type leakage in synthesized instances:
when defining a typeclass instance for a type alias, the lambda binder domains
use the alias type (not an internal unfolding).
-/

class MyInv (α : Type) where
  myInv : α → α

instance : MyInv Nat where
  myInv n := n + 1

def MyNat : Type := Nat

-- `inferInstanceAs` leaks the source type `Nat` as the carrier
instance myNatInv_leaky : MyInv MyNat :=
  inferInstanceAs (MyInv Nat)

-- `inferInstanceAs%` fixes this — the carrier and lambda domain are `MyNat`
instance myNatInv_fixed : MyInv MyNat :=
  inferInstanceAs% (MyInv Nat)

-- Verify the leaky instance: carrier is `Nat`, not `MyNat`
/--
info: @[implicit_reducible] def myNatInv_leaky : MyInv MyNat :=
@inferInstanceAs.{1} (MyInv Nat) instMyInvNat
-/
#guard_msgs in
set_option pp.all true in
#print myNatInv_leaky

-- Verify the fixed instance: carrier and lambda domain are `MyNat`
/--
info: @[implicit_reducible] def myNatInv_fixed : MyInv MyNat :=
@MyInv.mk MyNat fun (n : MyNat) =>
  @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
-/
#guard_msgs in
set_option pp.all true in
#print myNatInv_fixed

-- Both instances should compute the same thing
example : myNatInv_leaky.myInv (α := MyNat) (5 : Nat) = myNatInv_fixed.myInv (5 : Nat) := rfl
