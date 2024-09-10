import Mathlib.Tactic.StacksAttribute

/-- info: No tags found. -/
#guard_msgs in
#stacks_tags

namespace X
/--
warning: Tag '04 Q' should only consist of digits and uppercase letters
---
warning: Tag '044QQ' is 5 characters long, but it should be 4 characters long
---
warning: Tag 'loA1' should only consist of digits and uppercase letters
-/
#guard_msgs in
@[stacks 04 Q "", stacks A04Q "A comment", stacks 044QQ, stacks loA1]
theorem tagged : True := .intro

end X

/--
warning: Please, enter a Tag after `stacks`.
---
warning: Please, enter a Tag after `stacks`.
-/
#guard_msgs in
@[stacks "", stacks]
example : True := .intro

/--
info:
[Stacks Tag A04Q](https://stacks.math.columbia.edu/tag/A04Q) corresponds to declaration 'X.tagged'. (A comment)
-/
#guard_msgs in
#stacks_tags

/--
info:
[Stacks Tag A04Q](https://stacks.math.columbia.edu/tag/A04Q) corresponds to declaration 'X.tagged'. (A comment)
True
-/
#guard_msgs in
#stacks_tags!
