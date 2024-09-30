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
-- Do not allow setting a `longFile` linter option if the file does not exceed the `defValue`
set_option linter.style.longFile 1500

/--
warning: using 'exit' to interrupt Lean
---
warning: The default value of the `longFile` linter is 50.
This file is 37 lines long which does not exceed the allowed bound.
Please, remove the `set_option linter.style.longFile 60`.
-/
#guard_msgs in
-- Do not allow unnecessarily increasing the `longFile` linter option
set_option linter.style.longFileDefValue 50 in
set_option linter.style.longFile 60 in
#exit

/--
warning: using 'exit' to interrupt Lean
---
warning: This file is 51 lines long, but the limit is 20.

You can extend the allowed length of the file using `set_option linter.style.longFile 200`.
You can completely disable this linter by setting the length limit to `0`.
-/
#guard_msgs in
-- We test that the `longFile` linter warns when a file exceeds the allowed value.
set_option linter.style.longFileDefValue 10 in
set_option linter.style.longFile 20 in
#exit

/-- warning: using 'exit' to interrupt Lean -/
#guard_msgs in
-- Check that the `candidate` value is allowed
set_option linter.style.longFileDefValue 10 in
set_option linter.style.longFile 200 in
#exit

/-- warning: using 'exit' to interrupt Lean -/
#guard_msgs in
-- Check that the `candidate - 100` value is allowed
set_option linter.style.longFileDefValue 10 in
set_option linter.style.longFile 100 in
#exit

/--
warning: using 'exit' to interrupt Lean
---
warning: This file is 78 lines long. The current limit is 101, but it is expected to be 200:
`set_option linter.style.longFile 200`.
You can completely disable this linter by setting the length limit to `0`.
-/
#guard_msgs in
-- Check that a value different from `candidate` or `candidate - 100` value is not allowed
set_option linter.style.longFileDefValue 10 in
set_option linter.style.longFile 101 in
#exit

end longFile
