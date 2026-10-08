import Mathlib.Tactic.Linter.DeprecatedSimpLemma

/--
warning: Deprecated declarations should not have the simp attribute

Note: This linter can be disabled with `set_option linter.deprecatedSimpLemma false`
-/
#guard_msgs in
@[simp, deprecated "We now believe 1 + 1 = 3" (since := "Today")]
theorem test1 : 1 + 1 = 2 := rfl


/--
warning: Deprecated declarations should not have the simp attribute

Note: This linter can be disabled with `set_option linter.deprecatedSimpLemma false`
-/
#guard_msgs in
@[simp high, deprecated "We now believe 1 + 1 = 3" (since := "Today")]
theorem test2 : 1 + 1 = 2 := rfl


/--
warning: `[deprecated]` attribute should specify either a new name or a deprecation message
---
warning: `[deprecated]` attribute should specify the date or library version at which the deprecation was introduced, using `(since := "...")`
---
warning: Deprecated declarations should not have the simp attribute

Note: This linter can be disabled with `set_option linter.deprecatedSimpLemma false`
-/
#guard_msgs in
@[deprecated, simp]
theorem test3 : 1 + 1 = 2 := rfl


/--
warning: `[deprecated]` attribute should specify the date or library version at which the deprecation was introduced, using `(since := "...")`
---
warning: Deprecated declarations should not have the simp attribute

Note: This linter can be disabled with `set_option linter.deprecatedSimpLemma false`
-/
#guard_msgs in
@[deprecated "some message", simp]
instance test4 : Add Nat := inferInstance


/--
warning: Deprecated declarations should not have the simp attribute

Note: This linter can be disabled with `set_option linter.deprecatedSimpLemma false`
-/
#guard_msgs in
@[deprecated "We now believe 1 + 1 = 3" (since := "Today"), simp ← high]
def test6 : 1 + 1 = 2 := rfl


/--
warning: `test6` has been deprecated: We now believe 1 + 1 = 3
---
warning: Deprecated declarations should not have the simp attribute

Note: This linter can be disabled with `set_option linter.deprecatedSimpLemma false`
-/
#guard_msgs in
@[deprecated "We now believe 1 + 1 = 3" (since := "Today"), simp ← high]
abbrev test7 := test6

#guard_msgs in
theorem test8 : 1 + 1 = 2 := rfl

namespace silly

/--
warning: Deprecated declarations should not have the simp attribute

Note: This linter can be disabled with `set_option linter.deprecatedSimpLemma false`
-/
#guard_msgs in
@[scoped simp, deprecated "" (since := "")]
theorem test9 : 1 + 1 = 2 := rfl

end silly

/--
warning: Deprecated declarations should not have the simp attribute

Note: This linter can be disabled with `set_option linter.deprecatedSimpLemma false`
-/
#guard_msgs in
@[local simp, deprecated "" (since := "")]
theorem test10 : 1 + 1 = 2 := rfl
