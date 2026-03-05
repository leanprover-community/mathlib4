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
  inferInstanceAs% (MyInv Nat)

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

/-! ## Deeper hierarchy: reproducing the grind failure pattern

The original failure involved `Field (FiniteResidueField K)` defined via
`inferInstanceAs% (Field (IsLocalRing.ResidueField _))`. Deeply nested sub-instances
(e.g. `DivisionMonoid.toDivInvOneMonoid.toInvOneClass.toInv`) had lambda domains
referring to `IsLocalRing.ResidueField _` instead of `FiniteResidueField K`.
This caused `isDefEq` failures at `instances` transparency — the level used by
grind's `checkInst`.

We reproduce the pattern with a smaller 3-level hierarchy and verify the
transparency-level failure directly.
-/

class TestInv (α : Type) where
  inv : α → α

class TestDivInvMonoid (α : Type) extends TestInv α where
  mul : α → α → α

class TestField (α : Type) extends TestDivInvMonoid α where
  add : α → α → α
  neg : α → α

instance : TestField Nat where
  inv n := n
  mul := Nat.mul
  add := Nat.add
  neg n := n

def TestNat := Nat

-- Direct instance: all lambda domains correctly use TestNat
instance testField_direct : TestField TestNat where
  inv n := n
  mul := Nat.mul
  add := Nat.add
  neg n := n

-- Leaky: internal lambda domains use Nat instead of TestNat
instance testField_leaky : TestField TestNat := inferInstanceAs% (TestField Nat)

-- Fixed: inferInstanceAs% patches lambda domains to use TestNat
-- (warns about leaky sub-instances that could be defined separately)
/--
warning: inferInstanceAs%: the synthesized instance for TestInv
  TestNat has carrier type leakage (it uses the source carrier type internally instead of the target). `inferInstanceAs%` will patch the sub-instance inline, but consider defining it separately with `inferInstanceAs%` for cleaner results.
  To suppress this warning: `set_option inferInstanceAsPercent.leakySubInstWarning false`
---
warning: inferInstanceAs%: the synthesized instance for TestDivInvMonoid
  TestNat has carrier type leakage (it uses the source carrier type internally instead of the target). `inferInstanceAs%` will patch the sub-instance inline, but consider defining it separately with `inferInstanceAs%` for cleaner results.
  To suppress this warning: `set_option inferInstanceAsPercent.leakySubInstWarning false`
-/
#guard_msgs in
instance testField_fixed : TestField TestNat := inferInstanceAs% (TestField Nat)

-- The warning can be disabled:
#guard_msgs in
set_option inferInstanceAsPercent.leakySubInstWarning false in
instance testField_fixed' : TestField TestNat := inferInstanceAs% (TestField Nat)

-- All three are defeq at default transparency (Nat = TestNat at this level).
example : testField_leaky = testField_direct := rfl
example : testField_fixed = testField_direct := rfl

-- At `instances` transparency (the level grind's `checkInst` uses):
-- the leaky instance is NOT defeq to a directly-defined instance,
-- because lambda domains say `Nat` instead of `TestNat` and
-- `TestNat := Nat` is not unfolded at this transparency.
/--
error: Tactic `rfl` failed: The left-hand side
  testField_leaky
is not definitionally equal to the right-hand side
  testField_direct

⊢ testField_leaky = testField_direct
-/
#guard_msgs in
example : testField_leaky = testField_direct := by with_reducible_and_instances rfl

-- The fixed instance IS defeq at `instances` transparency.
example : testField_fixed = testField_direct := by with_reducible_and_instances rfl

/-! ## Sub-instances already defined with `inferInstanceAs%`

When a sub-instance has already been defined with `inferInstanceAs%`,
defining a parent instance with `inferInstanceAs%` should NOT warn about
leaky sub-instances — the sub-instance is already clean.

This was reported by Sébastien Gouëzel: when `AddMonoid SGNNReal` is defined
with `inferInstanceAs%`, defining `AddCancelCommMonoid SGNNReal` with
`inferInstanceAs%` should not warn about `AddMonoid` being leaky.

The warning only fires when `trySynthInstance` finds a pre-existing instance for
the sub-class. So we test this by first defining a clean `TestInv` instance,
then a leaky parent (so synthesis can find sub-instances through projection),
and finally verifying that `inferInstanceAs%` suppresses the `TestInv` warning.
-/

-- Define a clean sub-instance for TestInv
instance testInv_clean : TestInv TestNat := inferInstanceAs% (TestInv Nat)

-- Now `testInv_clean` provides a clean `TestInv TestNat`, and
-- `testField_direct`/`testField_fixed` provide clean `TestDivInvMonoid TestNat`
-- through projection. So no warnings should fire:
#guard_msgs in
instance testField_with_clean_inv : TestField TestNat := inferInstanceAs% (TestField Nat)

/-! ## Head alignment: universe mismatches and type abbreviations

`inferInstanceAs%` should handle cases where the source and expected types have
different head expressions due to:
1. Universe-level differences (same constant name, different universe levels)
2. Type abbreviations (different constant names that unfold to a common head)

These are reproductions of failures reported by Sébastien Gouëzel.
-/

-- Universe mismatch: `MyVec α n` is a `def` with type `Type u`, but its body
-- `{l : List α // l.length = n}` has type `Sort (max 1 (u+1))`.
-- This causes `DecidableEq` to be elaborated at `DecidableEq.{u+1}` for the expected
-- type vs `DecidableEq.{max 1 (u+1)}` for the source — structurally different but equal.
def MyVec (α : Type u) (n : Nat) := {l : List α // l.length = n}

#guard_msgs in
instance [DecidableEq α] : DecidableEq (MyVec α n) :=
  inferInstanceAs% (DecidableEq {l : List α // l.length = n})

-- Abbreviation head mismatch: `TestAbbrevRel` unfolds to `TestBaseRel`
class TestBaseRel (r : Nat → Nat → Prop) where
  decide : Nat → Nat → Bool

abbrev TestAbbrevRel := TestBaseRel (· < ·)

instance : TestBaseRel (· < ·) where
  decide := (· < ·)

#guard_msgs in
instance : TestAbbrevRel := inferInstanceAs% (TestBaseRel (· < ·))
