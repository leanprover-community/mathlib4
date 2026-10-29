module

public import Mathlib.Tactic.Linter.AttributeOnDeprecated

/-! Tests for the `attributeOnDeprecated` linter. -/

set_option linter.attributeOnDeprecated true

theorem bar : True := trivial

@[deprecated bar (since := "2026-01-01")] theorem foo : True := trivial

@[deprecated "No replacement." (since := "2026-01-01")] theorem noReplacement : True := trivial

namespace N

@[deprecated bar (since := "2026-01-01")] theorem baz : True := trivial

theorem newQux : True := trivial

@[deprecated newQux (since := "2026-01-01")] theorem oldInN : True := trivial

end N

@[deprecated N.newQux (since := "2026-01-01")] theorem oldQux : True := trivial

-- Attributes on non-deprecated declarations are fine.
#guard_msgs in
attribute [simp] bar

-- Attributes added together with the deprecation are fine.
#guard_msgs in
@[simp, deprecated bar (since := "2026-01-01")] theorem inlineDeprecated : True := trivial

-- `attribute [deprecated ...]` is what makes the declaration deprecated.
theorem laterDeprecated : True := trivial

#guard_msgs in
attribute [deprecated bar (since := "2026-01-01")] laterDeprecated

/--
warning: `foo` has been deprecated in favor of `bar`: this `attribute` command will break when `foo` is removed.
Consider adding the attribute directly to the declaration of `foo`, applying it to `bar` instead, or removing it.

Hint: Replace the deprecated name:
  f̵o̵o̵b̲a̲r̲

Note: This linter can be disabled with `set_option linter.attributeOnDeprecated false`
-/
#guard_msgs in
attribute [simp] foo

/--
warning: `noReplacement` has been deprecated: this `attribute` command will break when `noReplacement` is removed.
Consider adding the attribute directly to the declaration of `noReplacement` or removing it.

Note: This linter can be disabled with `set_option linter.attributeOnDeprecated false`
-/
#guard_msgs in
attribute [simp] noReplacement

-- Only the deprecated targets are flagged.
/--
warning: `foo` has been deprecated in favor of `bar`: this `attribute` command will break when `foo` is removed.
Consider adding the attribute directly to the declaration of `foo`, applying it to `bar` instead, or removing it.

Hint: Replace the deprecated name:
  f̵o̵o̵b̲a̲r̲

Note: This linter can be disabled with `set_option linter.attributeOnDeprecated false`
-/
#guard_msgs in
attribute [-simp] bar foo

/--
warning: `foo` has been deprecated in favor of `bar`: this `attribute` command will break when `foo` is removed.
Consider adding the attribute directly to the declaration of `foo`, applying it to `bar` instead, or removing it.

Hint: Replace the deprecated name:
  f̵o̵o̵b̲a̲r̲

Note: This linter can be disabled with `set_option linter.attributeOnDeprecated false`
-/
#guard_msgs in
attribute [local simp] foo in
example : True := trivial

-- Only the targets of the `attribute` command are inspected, not the command after `in`.
#guard_msgs in
attribute [local simp] bar in
set_option linter.deprecated false in
example : True := foo

-- The suggested replacement is a name that resolves at the `attribute` command.
/--
warning: `oldQux` has been deprecated in favor of `N.newQux`: this `attribute` command will break when `oldQux` is removed.
Consider adding the attribute directly to the declaration of `oldQux`, applying it to `N.newQux` instead, or removing it.

Hint: Replace the deprecated name:
  o̵l̵d̵N̲.̲n̲e̲w̲Qux

Note: This linter can be disabled with `set_option linter.attributeOnDeprecated false`
-/
#guard_msgs in
attribute [simp] oldQux

-- The targets are resolved in the scope of the `attribute` command.
/--
warning: `baz` has been deprecated in favor of `bar`: this `attribute` command will break when `baz` is removed.
Consider adding the attribute directly to the declaration of `baz`, applying it to `bar` instead, or removing it.

Hint: Replace the deprecated name:
  baz̵r̲

Note: This linter can be disabled with `set_option linter.attributeOnDeprecated false`
-/
#guard_msgs in
open N in
attribute [simp] baz

namespace N

/--
warning: `baz` has been deprecated in favor of `bar`: this `attribute` command will break when `baz` is removed.
Consider adding the attribute directly to the declaration of `baz`, applying it to `bar` instead, or removing it.

Hint: Replace the deprecated name:
  baz̵r̲

Note: This linter can be disabled with `set_option linter.attributeOnDeprecated false`
-/
#guard_msgs in
attribute [simp] baz

-- The suggested replacement is fully qualified if and only if the deprecated name is.
/--
warning: `oldInN` has been deprecated in favor of `newQux`: this `attribute` command will break when `oldInN` is removed.
Consider adding the attribute directly to the declaration of `oldInN`, applying it to `newQux` instead, or removing it.

Hint: Replace the deprecated name:
  o̵l̵d̵I̵n̵N̵n̲e̲w̲Q̲u̲x̲

Note: This linter can be disabled with `set_option linter.attributeOnDeprecated false`
-/
#guard_msgs in
attribute [simp] oldInN

/--
warning: `oldInN` has been deprecated in favor of `newQux`: this `attribute` command will break when `oldInN` is removed.
Consider adding the attribute directly to the declaration of `oldInN`, applying it to `newQux` instead, or removing it.

Hint: Replace the deprecated name:
  N̵.̵o̵l̵d̵I̵n̵N̵N̲.̲n̲e̲w̲Q̲u̲x̲

Note: This linter can be disabled with `set_option linter.attributeOnDeprecated false`
-/
#guard_msgs in
attribute [simp] N.oldInN

end N

#guard_msgs in
set_option linter.attributeOnDeprecated false in
attribute [simp] foo
