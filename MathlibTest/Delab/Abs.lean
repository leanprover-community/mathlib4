import Mathlib.Algebra.Order.Group.Unbundled.Abs

variable {α β : Type*} [Lattice α] [Lattice β] [Group α] [AddGroup β] {a : α} {b : β}

/-- info: |a|ₘ : α -/
#guard_msgs in
#check |a|ₘ

/-- info: |b| : β -/
#guard_msgs in
#check |b|

/-- info: |(|b|)| : β -/
#guard_msgs in
#check |(|b|)|

/-- info: |(|a|ₘ)|ₘ : α -/
#guard_msgs in
#check |(|a|ₘ)|ₘ

/-- info: |(-b)| : β -/
#guard_msgs in
#check |(-b)|
