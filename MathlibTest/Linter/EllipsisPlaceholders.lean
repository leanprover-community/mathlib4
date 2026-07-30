import Mathlib.Tactic.Linter.EllipsisPlaceholders

set_option linter.style.ellipsisPlaceholders true
-- Unit tests use a lower threshold than the default (`4`).
set_option linter.style.ellipsisPlaceholders.minTrailingHoles 2

def ellipsisTestFn (a b c : Nat) : Nat := a + b + c
def ellipsisTestFnFour (a b c d : Nat) : Nat := a + b + c + d
def ellipsisTestFnOpt (a : Nat) (b : Nat := 0) (c : Nat := 0) : Nat := a + b + c
def ellipsisTestFnAuto (a : Nat) (b : Nat := by decide) : Nat := a + b

/--
warning: Replace 2 trailing `_` placeholders with `..`.

Note: This linter can be disabled with `set_option linter.style.ellipsisPlaceholders false`
-/
#guard_msgs(warning, drop info) in
#check ellipsisTestFn 1 _ _

/--
warning: Replace 3 trailing `_` placeholders with `..`.

Note: This linter can be disabled with `set_option linter.style.ellipsisPlaceholders false`
-/
#guard_msgs(warning, drop info) in
#check ellipsisTestFnFour 1 _ _ _

#guard_msgs(drop warning, drop info) in
#check ellipsisTestFnFour 1 2 3 _

#guard_msgs(drop warning, drop info) in
#check ellipsisTestFnFour 1 ..

#guard_msgs(drop warning, drop info) in
#check ellipsisTestFnFour 1 _ 3 _

#guard_msgs(drop warning, drop info) in
#check ellipsisTestFnOpt 1 _

#guard_msgs(drop warning, drop info) in
#check ellipsisTestFnOpt 1 _ _

#guard_msgs(drop warning, drop info) in
#check ellipsisTestFnAuto 1 _

set_option linter.style.ellipsisPlaceholders false in
#guard_msgs(drop warning, drop info) in
#check ellipsisTestFn 1 _ _

example : Nat := by
  set_option linter.style.ellipsisPlaceholders true in
  exact ellipsisTestFn 1 2 3

#check ellipsisTestFn 1 _ _

-- Typed holes are never rewritten.
#guard_msgs(drop warning, drop info) in
#check ellipsisTestFn 1 (_ : Nat) (_ : Nat)
