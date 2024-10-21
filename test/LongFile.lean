import Mathlib.Tactic.Linter.Lint

/-
# Testing the `longFile` linter

Things to note:
* `set_option linter.style.longFile 0` disables the linter, allowing us to set a value smaller than
  `1500` without triggering the warning for setting a small value for the option;
* `guard_msgs ... in #exit` and `set_option ... in #exit` allow processing of the file *beyond*
  `#exit`, since they wrap `#exit` inside an anonymous section,
  making Lean active again *after* that anonymous section.

-/

section longFile

/--
warning: The default value of the `longFile` linter is 1500.
The current value of 1500 does not exceed the allowed bound.
Please, remove the `set_option linter.style.longFile 1500`.
-/
#guard_msgs in
-- Do not allow setting a "small" `longFile` linter option
set_option linter.style.longFile 1500

/--
warning: using 'exit' to interrupt Lean
---
warning: The default value of the `longFile` linter is 1500.
This file is 36 lines long which does not exceed the allowed bound.
Please, remove the `set_option linter.style.longFile 1600`.
-/
#guard_msgs in
-- Do not allow unnecessarily increasing the `longFile` linter option
set_option linter.style.longFile 1600 in
#exit

/--
warning: using 'exit' to interrupt Lean
---
warning: This file is 51 lines long, but the limit is 10.

You can extend the allowed length of the file using `set_option linter.style.longFile 1500`.
You can completely disable this linter by setting the length limit to `0`.
-/
#guard_msgs in
-- First, we silence the linter, so that we can set a default value smaller than 1500.
set_option linter.style.longFile 0 in
-- Next, we test that the `longFile` linter warns when a file exceeds the allowed value.
set_option linter.style.longFile 10 in
#exit

/--
warning: using 'exit' to interrupt Lean
---
warning: The default value of the `longFile` linter is 1500.
This file is 66 lines long which does not exceed the allowed bound.
Please, remove the `set_option linter.style.longFile 1700`.
-/
#guard_msgs in
-- First, we silence the linter, so that we can set a default value smaller than 1500.
set_option linter.style.longFile 0 in
-- If we set the allowed bound for the `longFile` linter that is too large,
-- the linter tells us to use a smaller bound.
set_option linter.style.longFile 1700 in
#exit

end longFile
