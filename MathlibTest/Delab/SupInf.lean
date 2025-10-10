import Mathlib


/-- info: max 1 2 : ℕ -/
#guard_msgs in
#check max (1 : ℕ) 2

/-- info: max 1 2 : ℝ -/
#guard_msgs in
#check max (1 : ℝ) 2

/-- info: ({0} ⊔ {1} ⊔ ({2} ⊔ {3})) ⊓ ({4} ⊔ {5}) ⊔ {6} ⊓ {7} ⊓ ({8} ⊓ {9}) : Set ℕ -/
#guard_msgs in
#check (max (min (max (max {0} {1}) (max {2} {3})) (max {4} {5})) (min (min {6} {7}) (min {8} {9})) : Set ℕ)

section

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

end

universe u

/-- info: fun α [Lattice α] a b => a ⊔ b : (α : Type u) → [Lattice α] → α → α → α -/
#guard_msgs in
#check fun (α : Type u) [Lattice α] (a b : α) => max a b

/-- info: fun α [LinearOrder α] a b => max a b : (α : Type u) → [LinearOrder α] → α → α → α -/
#guard_msgs in
#check fun (α : Type u) [LinearOrder α] (a b : α) => max a b

/--
info: fun α [CompleteLinearOrder α] a b => max a b : (α : Type u) → [CompleteLinearOrder α] → α → α → α
-/
#guard_msgs in
#check fun (α : Type u) [CompleteLinearOrder α] (a b : α) => max a b

/--
info: fun α [ConditionallyCompleteLinearOrder α] a b =>
  max a b : (α : Type u) → [ConditionallyCompleteLinearOrder α] → α → α → α
-/
#guard_msgs in
#check fun (α : Type u) [ConditionallyCompleteLinearOrder α] (a b : α) => max a b

-- In this section we check that the delaborator respects the options `pp.explicit` and `pp.notation`.
section

variable [Min α] [Max α] (a b c : α)

/-- info: (a ⊔ b) ⊓ c : α -/
#guard_msgs in
#check min (max a b) c

set_option pp.notation false in
/-- info: min (max a b) c : α -/
#guard_msgs in
#check min (max a b) c

set_option pp.explicit true in
/-- info: @min α inst✝¹ (@max α inst✝ a b) c : α -/
#guard_msgs in
#check min (max a b) c

end
