/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang, Damiano Testa
-/

import Mathlib.Tactic.Linter.GlobalAttributeIn

/-! Tests for the `globalAttributeIn` linter. -/

-- Since lean4#13223 applying a global attribute using ... `in` ... is an error

class Dummy where
  field : True

@[reducible] def dummyInst : Dummy := ⟨True.intro⟩

/--
error: Despite the `in`, the attribute instance 1100 is added globally to dummyInst
please remove the `in` or make this a `local instance 1100`
-/
#guard_msgs in
set_option autoImplicit false in
attribute [instance 1100] dummyInst in
set_option autoImplicit false in
instance : Inhabited Int where
  default := 0

/--
error: Despite the `in`, the attribute instance is added globally to dummyInst
please remove the `in` or make this a `local instance`
-/
#guard_msgs in
attribute [instance] dummyInst in
instance : Inhabited Int where
  default := 0

/--
error: Despite the `in`, the attribute simp is added globally to Int.add
please remove the `in` or make this a `local simp`
-/
#guard_msgs in
attribute [simp] Int.add in
instance : Inhabited Int where
  default := 0

namespace X

-- Here's another example, with nested attributes.
/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem foo (x y : Nat) : x = y := sorry

/--
error: Despite the `in`, the attribute simp is added globally to foo
please remove the `in` or make this a `local simp`
---
error: Despite the `in`, the attribute ext is added globally to foo
please remove the `in` or make this a `local ext`
-/
#guard_msgs in
set_option warning.simp.varHead false in
attribute [simp, local simp, ext, -simp, -ext] foo in
def bar := False

#guard_msgs in
-- `local instance` is allowed with `in`
attribute [local instance] dummyInst in
instance : Inhabited Int where
  default := 0

#guard_msgs in
-- `local instance priority` is allowed with `in`
attribute [local instance 42] dummyInst in
instance : Inhabited Int where
  default := 0

#guard_msgs in
-- `scoped instance` is allowed with `in`
attribute [scoped instance] dummyInst in
instance : Inhabited Int where
  default := 0

#guard_msgs in
-- `scoped instance priority` is allowed with `in`
attribute [scoped instance 42] dummyInst in
instance : Inhabited Int where
  default := 0

end X
