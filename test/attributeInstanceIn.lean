/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang, Damiano Testa
-/

import Mathlib.Tactic.Linter.AttributeInstanceIn

/-! Tests for the `attributeInstanceIn` linter. -/

-- Test disabling the linter.
set_option linter.attributeInstanceIn false

set_option autoImplicit false in
attribute [instance] Int.add in
instance : Inhabited Int where
  default := 0

set_option linter.attributeInstanceIn true

set_option linter.attributeInstanceIn false in
attribute [instance] Int.add in
instance : Inhabited Int where
  default := 0

-- Global instances with `in`, are linted, as they are a footgun.

set_option linter.attributeInstanceIn false in
/--
warning: `attribute [instance] ... in` declarations are surprising:
they are **not** limited to the subsequent declaration, but define global instances
please remove the `in` or make this a `local instance` instead
note: this linter can be disabled with `set_option linter.attributeInstanceIn false`
-/
#guard_msgs in
set_option autoImplicit false in
set_option linter.attributeInstanceIn true in
attribute [instance 1100] Int.add in
set_option autoImplicit false in
instance : Inhabited Int where
  default := 0

set_option linter.attributeInstanceIn false in
/--
warning: `attribute [instance] ... in` declarations are surprising:
they are **not** limited to the subsequent declaration, but define global instances
please remove the `in` or make this a `local instance` instead
note: this linter can be disabled with `set_option linter.attributeInstanceIn false`
-/
#guard_msgs in
set_option linter.attributeInstanceIn true in
attribute [instance] Int.add in
instance : Inhabited Int where
  default := 0

#guard_msgs in
-- non-`instance` attributes are allowed with `in`
#guard_msgs in
attribute [simp] Int.add in
instance : Inhabited Int where
  default := 0

-- Here's another example, with nested attributes.
def foo := True

#guard_msgs in
-- TODO: where's the docBlame linter defined? what do I need to import?
--attribute [nolint docBlame] foo in
attribute [simp] foo in
def bar := False

namespace X

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

attribute [local instance 42] foo

-- Global instance without the `in` are also left alone.
attribute [instance 20000] foo

namespace X

attribute [scoped instance 0] foo
