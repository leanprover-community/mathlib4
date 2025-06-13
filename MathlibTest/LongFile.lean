import Mathlib.Tactic.Linter.Style

/-
# Testing the `longFile` linter

Things to note:
* `set_option linter.style.longFile 0` disables the linter, allowing us to set a value smaller than
  `linter.style.longFileDefValue` without triggering the warning for setting a small value
  for the option;
* `guard_msgs ... in #exit` and `set_option ... in #exit` allow processing of the file *beyond*
  `#exit`, since they wrap `#exit` inside an anonymous section,
  making Lean active again *after* that anonymous section.

-/

section longFile

/--
warning: The default value of the `longFile` linter is 1500.
The current value of 1500 does not exceed the allowed bound.
Please, remove the `set_option linter.style.longFile 1500`.
note: this linter can be disabled with `set_option linter.style.longFile 0`
-/
#guard_msgs in
-- Do not allow setting a `longFile` linter option if the file does not exceed the `defValue`
set_option linter.style.longFile 1500

/--
warning: using 'exit' to interrupt Lean
---
warning: The default value of the `longFile` linter is 50.
This file is 40 lines long which does not exceed the allowed bound.
Please, remove the `set_option linter.style.longFile 60`.
note: this linter can be disabled with `set_option linter.style.longFile 0`
-/
#guard_msgs in
-- Do not allow unnecessarily increasing the `longFile` linter option
set_option linter.style.longFileDefValue 50 in
set_option linter.style.longFile 60 in
#exit

/--
warning: using 'exit' to interrupt Lean
---
warning: This file is 55 lines long, but the limit is 20.

You can extend the allowed length of the file using `set_option linter.style.longFile 200`.
You can completely disable this linter by setting the length limit to `0`.
note: this linter can be disabled with `set_option linter.style.longFile 0`
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
warning: This file is 82 lines long. The current limit is 101, but it is expected to be 200:
`set_option linter.style.longFile 200`.
note: this linter can be disabled with `set_option linter.style.longFile 0`
-/
#guard_msgs in
-- Check that a value different from `candidate` or `candidate - 100` value is not allowed
set_option linter.style.longFileDefValue 10 in
set_option linter.style.longFile 101 in
#exit

-- The following test is a little artificial: it follows a path in the code that should only
-- be accessible after modifying the linter options appropriately.
-- Specifically, in the line `if lastLine ≤ defValue && defValue < linterBound then`, the failure
-- of *only* the second condition would produce the error message below
set_option linter.style.longFileDefValue 400
set_option linter.style.longFile 500
set_option linter.style.longFileDefValue 1000
/--
warning: using 'exit' to interrupt Lean
---
warning: This file is 99 lines long. The current limit is 500, but it is expected to be 1000:
`set_option linter.style.longFile 1000`.
note: this linter can be disabled with `set_option linter.style.longFile 0`
-/
#guard_msgs in
#exit
/-
warning: using 'exit' to interrupt Lean
---
warning: The default value of the `longFile` linter is 1000.
This file is 95 lines long which does not exceed the allowed bound.
Please, remove the `set_option linter.style.longFile 500`.
-/

set_option linter.style.longFileDefValue 2000
/--
warning: The default value of the `longFile` linter is 2000.
The current value of 1999 does not exceed the allowed bound.
Please, remove the `set_option linter.style.longFile 1999`.
note: this linter can be disabled with `set_option linter.style.longFile 0`
-/
#guard_msgs in
-- Do not allow setting a `longFile` linter option if the file does not exceed the `defValue`
set_option linter.style.longFile 1999

end longFile

set_option linter.style.longFileDefValue 400

/--
warning: using 'exit' to interrupt Lean
---
warning: The default value of the `longFile` linter is 400.
This file is 133 lines long which does not exceed the allowed bound.
Please, remove the `set_option linter.style.longFile 5000`.
note: this linter can be disabled with `set_option linter.style.longFile 0`
-/
#guard_msgs in
set_option linter.style.longFile 5000 in
#exit
