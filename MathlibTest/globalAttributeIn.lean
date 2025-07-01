/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang, Damiano Testa
-/

import Mathlib.Tactic.Linter.GlobalAttributeIn

/-! Tests for the `globalAttributeIn` linter. -/

-- Test disabling the linter.
set_option linter.globalAttributeIn false

set_option autoImplicit false in
attribute [instance] Int.add in
instance : Inhabited Int where
  default := 0

set_option linter.globalAttributeIn true

set_option linter.globalAttributeIn false in
attribute [instance] Int.add in
instance : Inhabited Int where
  default := 0

-- Global instances with `in`, are linted, as they are a footgun.

/--
warning: Despite the `in`, the attribute 'instance 1100' is added globally to 'Int.add'
please remove the `in` or make this a `local instance 1100`

Note: This linter can be disabled with `set_option linter.globalAttributeIn false`
-/
#guard_msgs in
set_option autoImplicit false in
attribute [instance 1100] Int.add in
set_option autoImplicit false in
instance : Inhabited Int where
  default := 0

/--
warning: Despite the `in`, the attribute 'instance' is added globally to 'Int.add'
please remove the `in` or make this a `local instance`

Note: This linter can be disabled with `set_option linter.globalAttributeIn false`
-/
#guard_msgs in
attribute [instance] Int.add in
instance : Inhabited Int where
  default := 0

/--
warning: Despite the `in`, the attribute 'simp' is added globally to 'Int.add'
please remove the `in` or make this a `local simp`

Note: This linter can be disabled with `set_option linter.globalAttributeIn false`
-/
#guard_msgs in
attribute [simp] Int.add in
instance : Inhabited Int where
  default := 0

namespace X

-- Here's another example, with nested attributes.
/-- warning: declaration uses 'sorry' -/
#guard_msgs in
theorem foo (x y : Nat) : x = y := sorry

/--
warning: Despite the `in`, the attribute 'simp' is added globally to 'foo'
please remove the `in` or make this a `local simp`

Note: This linter can be disabled with `set_option linter.globalAttributeIn false`
---
warning: Despite the `in`, the attribute 'ext' is added globally to 'foo'
please remove the `in` or make this a `local ext`

Note: This linter can be disabled with `set_option linter.globalAttributeIn false`
-/
#guard_msgs in
attribute [simp, local simp, ext, scoped instance, -simp, -ext] foo in
def bar := False

#guard_msgs in
-- `local instance` is allowed with `in`
attribute [local instance] Int.add in
instance : Inhabited Int where
  default := 0

#guard_msgs in
-- `local instance priority` is allowed with `in`
attribute [local instance 42] Int.add in
instance : Inhabited Int where
  default := 0

#guard_msgs in
-- `scoped instance` is allowed with `in`
attribute [scoped instance] Int.add in
instance : Inhabited Int where
  default := 0

#guard_msgs in
-- `scoped instance priority` is allowed with `in`
attribute [scoped instance 42] Int.add in
instance : Inhabited Int where
  default := 0

end X

-- Omitting the `in` is also fine.

attribute [local instance 42] X.foo

-- Global instance without the `in` are also left alone.
attribute [instance 20000] X.foo

namespace X

attribute [scoped instance 0] foo
