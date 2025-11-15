import Mathlib.Tactic.Linter.DeprecatedSimpLemma

/-- info: Deprecated lemmas should not have the simp attribute -/
#guard_msgs in
@[simp, deprecated "We now believe 1 + 1 = 3" (since := "Today")]
theorem test1 : 1 + 1 = 2 := rfl


/-- info: Deprecated lemmas should not have the simp attribute -/
#guard_msgs in
@[simp high, deprecated "We now believe 1 + 1 = 3" (since := "Today")]
theorem test2 : 1 + 1 = 2 := rfl


/-- info: Deprecated lemmas should not have the simp attribute -/
#guard_msgs in
@[deprecated "We now believe 1 + 1 = 3" (since := "Today"), simp]
theorem test3 : 1 + 1 = 2 := rfl


/-- info: Deprecated lemmas should not have the simp attribute -/
#guard_msgs in
@[deprecated "We now believe 1 + 1 = 3" (since := "Today"), simp ←]
theorem test4 : 1 + 1 = 2 := rfl


/-- info: Deprecated lemmas should not have the simp attribute -/
#guard_msgs in
@[deprecated "We now believe 1 + 1 = 3" (since := "Today"), simp ← high]
theorem test6 : 1 + 1 = 2 := rfl


/--
warning: `test6` has been deprecated: We now believe 1 + 1 = 3
---
info: Deprecated lemmas should not have the simp attribute
-/
#guard_msgs in
@[deprecated "We now believe 1 + 1 = 3" (since := "Today"), simp ← high]
abbrev test7 := test6
