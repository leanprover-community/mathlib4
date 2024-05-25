import Mathlib.Tactic.Linter.GenericSyntaxLinter

set_option linter.generic false in
/--
warning: careful: `attribute [instance] ... in` declarations are surprising:
they are **not** limited to the subsequent declaration,
but define global instances please remove the `in` or make this a `local instance` instead
note: this linter can be disabled with `set_option linter.generic false`
---
warning: cdots should use `·`
note: this linter can be disabled with `set_option linter.generic false`
---
warning: cdots should use `·`
note: this linter can be disabled with `set_option linter.generic false`
---
warning: cdots should use `·`
note: this linter can be disabled with `set_option linter.generic false`
-/
#guard_msgs in
set_option linter.generic true in
attribute [instance] Int.add in
instance : Inhabited Nat where
  default := by
    . have := 0
      · have : Nat → Nat → Nat := (· + .)
        . exact 0

/--
warning: careful: `attribute [instance] ... in` declarations are surprising:
they are **not** limited to the subsequent declaration,
but define global instances please remove the `in` or make this a `local instance` instead
note: this linter can be disabled with `set_option linter.generic false`
-/
#guard_msgs in
attribute [instance 0] Int.add in
instance : Inhabited Int where
  default := 0

#guard_msgs in
-- `local instance` is allowed with `in`
attribute [local instance] Int.add in
instance : Inhabited Int where
  default := 0

#guard_msgs in
-- `local instance priority` is allowed with `in`
attribute [local instance 0] Int.add in
instance : Inhabited Int where
  default := 0

namespace X
#guard_msgs in
-- `scoped instance` is allowed with `in`
attribute [scoped instance] Int.add in
instance : Inhabited Int where
  default := 0

#guard_msgs in
-- `scoped instance priority` is allowed with `in`
attribute [scoped instance 0] Int.add in
instance : Inhabited Int where
  default := 0

#guard_msgs in
-- non-`instance` attributes are allowed with `in`
attribute [simp] Int.add in
instance : Inhabited Int where
  default := 0

#guard_msgs in
-- non-`in` attributes are allowed
attribute [instance] Int.add
instance : Inhabited Int where
  default := 0

#guard_msgs in
-- non-`in` attributes are allowed
attribute [instance 0] Int.add
instance : Inhabited Int where
  default := 0

#guard_msgs in
-- non-`in` attributes are allowed
attribute [local instance] Int.add
instance : Inhabited Int where
  default := 0

#guard_msgs in
-- non-`in` attributes are allowed
attribute [local instance 0] Int.add
instance : Inhabited Int where
  default := 0

namespace X
#guard_msgs in
-- non-`in` attributes are allowed
attribute [scoped instance] Int.add
instance : Inhabited Int where
  default := 0

#guard_msgs in
-- non-`in` attributes are allowed
attribute [scoped instance 0] Int.add
instance : Inhabited Int where
  default := 0

#guard_msgs in
-- non-`in` attributes are allowed
attribute [simp] Int.add
instance : Inhabited Int where
  default := 0
