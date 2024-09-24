import Mathlib.Tactic.Linter.TransitiveSorry

set_option linter.transitiveSorry false
/--
warning: declaration uses 'sorry'
---
warning: 'X' relies on 'sorryAx'
note: this linter can be disabled with `set_option linter.transitiveSorry false`
-/
#guard_msgs in
set_option linter.transitiveSorry true in
theorem X : True := sorry

set_option linter.transitiveSorry true

/---/
#guard_msgs in
theorem X1 : True := .intro

namespace _root_
set_option linter.transitiveSorry false

/--
warning: '_root_.Y' relies on 'sorryAx'
note: this linter can be disabled with `set_option linter.transitiveSorry false`
-/
#guard_msgs in
set_option linter.transitiveSorry true in
theorem Y : True := X

/--
warning: '_root_.Y._root_.Z' relies on 'sorryAx'
note: this linter can be disabled with `set_option linter.transitiveSorry false`
-/
#guard_msgs in
set_option linter.transitiveSorry true in
theorem Y._root_.Z : True := Y

/---/
#guard_msgs in
set_option linter.transitiveSorry true in
theorem Y._root_.Z1 : True := X1

end _root_
