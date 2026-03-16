/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Tactic.FastInstance

/-!
# Tests for `inferInstanceAs%`

Demonstrates that `inferInstanceAs%` fixes type leakage in synthesized instances:
when defining a typeclass instance for a type alias, the lambda binder domains
use the alias type (not an internal unfolding).
-/

set_option pp.funBinderTypes true

class MyInv (α : Type) where
  myInv : α → α

instance : MyInv Nat where
  myInv n := n + 1

def MyNat : Type := Nat

-- `inferInstanceAs` leaks the source type `Nat` as the carrier
@[implicit_reducible]
def myNatInv_leaky : MyInv MyNat :=
  inferInstanceAs (MyInv Nat)

-- `inferInstanceAs%` fixes this — the carrier and lambda domain are `MyNat`
instance myNatInv_fixed : MyInv MyNat :=
  inferInstanceAs% (MyInv Nat)

-- The binder type is `MyNat`:
/--
info: @[implicit_reducible] def myNatInv_fixed : MyInv MyNat :=
{ myInv := fun (a : MyNat) => a + 1 }
-/
#guard_msgs in
#print myNatInv_fixed

-- Both instances should compute the same thing
example : myNatInv_leaky.myInv (α := MyNat) (5 : Nat) = myNatInv_fixed.myInv (5 : Nat) := rfl

/-! ## Deeper hierarchy: reproducing the grind failure pattern

The original failure involved `Field (FiniteResidueField K)` defined via
`inferInstanceAs (Field (IsLocalRing.ResidueField _))`. Deeply nested sub-instances
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
@[implicit_reducible]
def testField_direct : TestField TestNat where
  inv n := n
  mul := Nat.mul
  add := Nat.add
  neg n := n

-- Leaky: internal lambda domains use Nat instead of TestNat
@[implicit_reducible]
def testField_leaky : TestField TestNat := inferInstanceAs (TestField Nat)

-- Fixed: inferInstanceAs% patches lambda domains to use TestNat
@[implicit_reducible]
def testField_fixed : TestField TestNat := inferInstanceAs% (TestField Nat)

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

/-! ## Warning for leaky sub-instances

When `fast_instance%` or `inferInstanceAs%` encounters a synthesized sub-instance that has
leaky binder types, it warns the user so they can fix it with `fast_instance%` or
`inferInstanceAs%`. The warning is suppressed with
`set_option Elab.fast_instance.warnLeakySubInstances false`.
-/

-- A two-level class hierarchy.
class WarnSub (α : Type) where
  warnSubOp : α → α

class WarnParent (α : Type) extends WarnSub α where
  warnParentOp : α → α → α

def WarnMyNat : Type := Nat

instance : WarnSub Nat where warnSubOp n := n + 1
instance : WarnParent Nat where warnParentOp := Nat.add

-- A leaky sub-instance: binder type is `Nat` instead of `WarnMyNat`.
instance warnLeakySub : WarnSub WarnMyNat := inferInstanceAs (WarnSub Nat)

-- When `inferInstanceAs%` normalizes a `WarnParent WarnMyNat` instance, synthesis finds
-- `warnLeakySub` for the sub-instance field. Because `warnLeakySub` is leaky, a warning fires.
/--
warning: fast_instance%: 'warnLeakySub' (for
  WarnSub
    WarnMyNat) has leaky data-field binder types, which may cause `isDefEq` failures at instances transparency (e.g. in `grind`). Consider redefining it with `fast_instance%` or `inferInstanceAs%`.
To suppress: `set_option Elab.fast_instance.warnLeakySubInstances false`
-/
#guard_msgs in
@[implicit_reducible] def warnParentLeaky : WarnParent WarnMyNat := inferInstanceAs% (WarnParent Nat)

-- The warning is suppressed with the option:
#guard_msgs in
set_option Elab.fast_instance.warnLeakySubInstances false in
@[implicit_reducible] def warnParentSuppressed : WarnParent WarnMyNat := inferInstanceAs% (WarnParent Nat)

-- Using a fresh alias shows that fixing the sub-instance eliminates the warning.
-- (Using a different alias avoids conflicting with `warnLeakySub` above.)
def WarnMyNat2 : Type := Nat
instance warnFixedSub2 : WarnSub WarnMyNat2 := inferInstanceAs% (WarnSub Nat)
-- No warning because `warnFixedSub2` is canonical:
#guard_msgs in
@[implicit_reducible] def warnParentFixed : WarnParent WarnMyNat2 := inferInstanceAs% (WarnParent Nat)
