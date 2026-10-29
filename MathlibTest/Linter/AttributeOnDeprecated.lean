module

public import Mathlib.Tactic.Linter.AttributeOnDeprecated

/-! Tests for the `attributeOnDeprecated` linter. -/

set_option linter.attributeOnDeprecated true

theorem bar : True := trivial

@[deprecated bar (since := "2026-01-01")] theorem foo : True := trivial

@[deprecated "No replacement." (since := "2026-01-01")] theorem noReplacement : True := trivial

namespace N

@[deprecated bar (since := "2026-01-01")] theorem baz : True := trivial

end N

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
warning: `foo` is deprecated: this `attribute` command will break when `foo` is removed.
Consider adding the attribute directly to the declaration of `foo`, applying it to the replacement `bar`, or removing it.

Note: This linter can be disabled with `set_option linter.attributeOnDeprecated false`
-/
#guard_msgs in
attribute [simp] foo

/--
warning: `noReplacement` is deprecated: this `attribute` command will break when `noReplacement` is removed.
Consider adding the attribute directly to the declaration of `noReplacement` or removing it.

Note: This linter can be disabled with `set_option linter.attributeOnDeprecated false`
-/
#guard_msgs in
attribute [simp] noReplacement

-- Only the deprecated targets are flagged.
/--
warning: `foo` is deprecated: this `attribute` command will break when `foo` is removed.
Consider adding the attribute directly to the declaration of `foo`, applying it to the replacement `bar`, or removing it.

Note: This linter can be disabled with `set_option linter.attributeOnDeprecated false`
-/
#guard_msgs in
attribute [-simp] bar foo

/--
warning: `foo` is deprecated: this `attribute` command will break when `foo` is removed.
Consider adding the attribute directly to the declaration of `foo`, applying it to the replacement `bar`, or removing it.

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

-- The targets are resolved in the scope of the `attribute` command.
/--
warning: `N.baz` is deprecated: this `attribute` command will break when `N.baz` is removed.
Consider adding the attribute directly to the declaration of `N.baz`, applying it to the replacement `bar`, or removing it.

Note: This linter can be disabled with `set_option linter.attributeOnDeprecated false`
-/
#guard_msgs in
open N in
attribute [simp] baz

namespace N

/--
warning: `baz` is deprecated: this `attribute` command will break when `baz` is removed.
Consider adding the attribute directly to the declaration of `baz`, applying it to the replacement `bar`, or removing it.

Note: This linter can be disabled with `set_option linter.attributeOnDeprecated false`
-/
#guard_msgs in
attribute [simp] baz

end N

#guard_msgs in
set_option linter.attributeOnDeprecated false in
attribute [simp] foo
