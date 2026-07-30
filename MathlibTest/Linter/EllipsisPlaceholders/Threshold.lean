import Mathlib.Tactic.Linter.EllipsisPlaceholders

set_option linter.style.ellipsisPlaceholders true
set_option linter.unusedVariables false

def sixArg (a b c d e f : Nat) : Nat := a

def mixedTail (a b c d e f : Nat) : Nat := a

section DefaultThreshold

-- Default `minTrailingHoles` is `4` (≥ semantics: lint at 4 or more).

#guard_msgs(drop warning, drop info) in
#check sixArg 1 _ _

#guard_msgs(drop warning, drop info) in
#check sixArg 1 _ _ _

#guard_msgs(drop warning, drop info) in
#check sixArg 1 _ _ _ _

/--
warning: Replace 4 trailing `_` placeholders with `..`.

Note: This linter can be disabled with `set_option linter.style.ellipsisPlaceholders false`
-/
#guard_msgs(warning, drop info) in
#check sixArg 1 _ _ _ _

-- Should NOT lint: `?_` anywhere in the hole suffix
#guard_msgs(drop warning, drop info) in
#check sixArg 1 _ _ _ ?_ ?_

#guard_msgs(drop warning, drop info) in
#check mixedTail _ _ _ ?_ _ _

end DefaultThreshold

section CustomThreshold

section Min2

set_option linter.style.ellipsisPlaceholders.minTrailingHoles 2

/--
warning: Replace 2 trailing `_` placeholders with `..`.

Note: This linter can be disabled with `set_option linter.style.ellipsisPlaceholders false`
-/
#guard_msgs(warning, drop info) in
#check sixArg 1 _ _

#guard_msgs(drop warning, drop info) in
#check sixArg 1 _ _ _

end Min2

section Min3

set_option linter.style.ellipsisPlaceholders.minTrailingHoles 3

#guard_msgs(drop warning, drop info) in
#check sixArg 1 _ _

/--
warning: Replace 3 trailing `_` placeholders with `..`.

Note: This linter can be disabled with `set_option linter.style.ellipsisPlaceholders false`
-/
#guard_msgs(warning, drop info) in
#check sixArg 1 _ _ _

end Min3

end CustomThreshold
