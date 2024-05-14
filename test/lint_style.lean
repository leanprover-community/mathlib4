import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Common

/-! Tests for the style linter rewrite. -/

set_option pp.all true
set_option autoImplicit true in
lemma foo : True := trivial
