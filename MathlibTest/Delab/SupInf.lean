import Mathlib

/-- info: max 1 2 : ℕ -/
#guard_msgs in
#check max (1 : ℕ) 2

/-- info: max 1 2 : ℝ -/
#guard_msgs in
#check max (1 : ℝ) 2

/-- info: {1} ⊔ {2} : Set ℕ -/
#guard_msgs in
#check max ({1} : Set Nat) {2}

variable {α : Type*} (a b : α)

variable [Lattice α] in
/-- info: a ⊔ b : α -/
#guard_msgs in
#check max a b

variable [LinearOrder α] in
/-- info: max a b : α -/
#guard_msgs in
#check max a b

variable [CompleteLinearOrder α] in
/-- info: max a b : α -/
#guard_msgs in
#check max a b

variable [ConditionallyCompleteLinearOrder α] in
/-- info: max a b : α -/
#guard_msgs in
#check max a b
