import Mathlib.Tactic.Linter.DeprecatedSimpLemma

/-- info: Deprecated declarations should not have the simp attribute -/
#guard_msgs in
@[simp, deprecated "We now believe 1 + 1 = 3" (since := "Today")]
theorem test1 : 1 + 1 = 2 := rfl


/-- info: Deprecated declarations should not have the simp attribute -/
#guard_msgs in
@[simp high, deprecated "We now believe 1 + 1 = 3" (since := "Today")]
theorem test2 : 1 + 1 = 2 := rfl


/--
warning: `[deprecated]` attribute should specify either a new name or a deprecation message
---
warning: `[deprecated]` attribute should specify the date or library version at which the deprecation was introduced, using `(since := "...")`
---
info: Deprecated declarations should not have the simp attribute
-/
#guard_msgs in
@[deprecated, simp]
theorem test3 : 1 + 1 = 2 := rfl


/--
warning: `[deprecated]` attribute should specify the date or library version at which the deprecation was introduced, using `(since := "...")`
---
info: Deprecated declarations should not have the simp attribute
-/
#guard_msgs in
@[deprecated "some message", simp]
instance test4 : Add Nat := inferInstance


/-- info: Deprecated declarations should not have the simp attribute -/
#guard_msgs in
@[deprecated "We now believe 1 + 1 = 3" (since := "Today"), simp ← high]
def test6 : 1 + 1 = 2 := rfl


/--
warning: `test6` has been deprecated: We now believe 1 + 1 = 3
---
info: Deprecated declarations should not have the simp attribute
-/
#guard_msgs in
@[deprecated "We now believe 1 + 1 = 3" (since := "Today"), simp ← high]
abbrev test7 := test6
