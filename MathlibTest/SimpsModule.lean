/-
Copyright (c) 2025 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

import Mathlib.Tactic.Simps.Basic

/-! ## Non-exposed definitions

Test that `@[simps]` works correctly on definitions whose body is not exposed.
See https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/.40.5Bsimps.5D.20respects.20non-exposed.20body.3F

This file uses `module`, so definitions have non-exposed bodies by default.
The fix ensures `@[simps]` doesn't call `inferDefEqAttr` when the body is not exposed,
avoiding `@[defeq]` validation errors.
-/

structure MyStruct where
  val : Nat

/-- A helper definition that won't be exposed -/
def helperVal : Nat := 42

/-- Using the non-exposed helper in the definition body should not cause errors -/
@[simps]
def myDef : MyStruct := ⟨helperVal⟩

/-- The generated simp lemma should work correctly -/
example : myDef.val = helperVal := by simp
