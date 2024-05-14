import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Common

/-! Tests for the style linter rewrite. -/

set_option pp.all true
set_option pp.all false
set_option pp.raw.maxDepth 32
set_option trace.profiler.output "foo"

set_option autoImplicit true in
lemma foo : True := trivial
