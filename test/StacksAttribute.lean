import Mathlib.Tactic.StacksAttribute

/-- info: No tags found. -/
#guard_msgs in
#stacks_tags

namespace X

@[stacks A04Q "A comment"]
theorem tagged : True := .intro

end X

#guard_msgs in
@[stacks 0BR2, stacks 0X12]
example : True := .intro

@[stacks 0BR2, stacks 0X14 "I can also have a comment"]
example : True := .intro

@[stacks 0X14 "I can also have a comment"]
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
