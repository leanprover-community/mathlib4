import Mathlib.Data.Fintype.Defs

variable {α : Type*} [Fintype α] {p : α → Prop} {s : Finset α} {a : α}
    [DecidablePred p] [DecidableEq α] [Singleton α (Finset α)] [HasCompl (Finset α)]

/-- info: {x | p x} : Finset α -/
#guard_msgs in
#check ({x | p x} : Finset α)

/-- info: {x ∈ s | p x} : Finset α -/
#guard_msgs in
#check ({x ∈ s | p x})

/-- info: {x ≠ a | p x} : Finset α -/
#guard_msgs in
#check ({x ≠ a | p x} : Finset α)

/-- info: {x ∉ s | p x} : Finset α -/
#guard_msgs in
#check ({x ∉ s | p x})

/-- info: {x : α | p x} : Finset α -/
#guard_msgs in
set_option pp.funBinderTypes true in
#check ({x | p x} : Finset α)

/-- info: {x ∈ s | p x} : Finset α -/
#guard_msgs in
set_option pp.funBinderTypes true in
#check ({x ∈ s | p x})

/-- info: {x ≠ a | p x} : Finset α -/
#guard_msgs in
set_option pp.funBinderTypes true in
#check ({x ≠ a | p x} : Finset α)

/-- info: {x ∉ s | p x} : Finset α -/
#guard_msgs in
set_option pp.funBinderTypes true in
#check ({x ∉ s | p x})
