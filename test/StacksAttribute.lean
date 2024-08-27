import Mathlib.Tactic.StacksAttribute

/--
warning: Tag '04 Q' should only consist of digits and uppercase letters
---
warning: Tag '044QQ' is 5 characters long, but it should be 4 characters long
---
warning: Tag 'loA1' should only consist of digits and uppercase letters
-/
#guard_msgs in
@[stacks 04 Q "", stacks A04Q "A comment", stacks 044QQ , stacks loA1]
example : True := .intro
