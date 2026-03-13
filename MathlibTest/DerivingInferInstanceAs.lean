/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Tactic.DerivingInferInstanceAs

/-!
# Tests for deriving hook with `inferInstanceAs%` normalization

Verifies that `deriving instance ... for ...` on definitions produces clean instances
(no carrier type leakage at `reducibleAndInstances` transparency).
-/

-- Set up a test class hierarchy (same as InferInstanceAsPercent tests)
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

-- Test 1: `deriving instance` for a definition produces clean instances
set_option inferInstanceAsPercent.leakySubInstWarning false in
deriving instance TestField for TestNat

-- Direct instance for comparison
instance testField_direct : TestField TestNat where
  inv n := n
  mul := Nat.mul
  add := Nat.add
  neg n := n

-- The derived instance should be defeq to the direct one at `reducibleAndInstances` transparency
-- (this would fail with the standard delta handler due to carrier type leakage)
example : instTestFieldTestNat = testField_direct := by with_reducible_and_instances rfl

-- Test 2: `def ... deriving ...` also produces clean instances
set_option inferInstanceAsPercent.leakySubInstWarning false in
def TestNat2 := Nat deriving TestField

instance testField_direct2 : TestField TestNat2 where
  inv n := n
  mul := Nat.mul
  add := Nat.add
  neg n := n

example : instTestFieldTestNat2 = testField_direct2 := by with_reducible_and_instances rfl

-- Verify the normalization is actually happening by printing the derived instance
set_option pp.all true in
#print instTestFieldTestNat
