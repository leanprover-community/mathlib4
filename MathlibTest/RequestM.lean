module

import Mathlib.Util.RequestM

set_option linter.test.logCodeActions true

/--
@ +1:25...31
info: Try this:
  [apply] exact True.intro
---
@ +1:26...29
info: Code action (quickfix):
💡️ Try this: exact True.intro

@@ +0:25-+0:31 @@
- exact?
+ exact True.intro
-/
#guard_msgs (positions := true) in
theorem foo : True := by exact?
                        --^^^

/--
@ +2:30...34
error: This range does not have characters above it.
-/
#guard_msgs (positions := true) in
example : True :=
                            --^^^^
  trivial
