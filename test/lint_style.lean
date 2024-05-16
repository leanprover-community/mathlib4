import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Common

/-! Tests for the style linter rewrite. -/

-- All types of option: boolean, numeric and string-valued.
-- top-level, with in, as terms and tactics (or so)

set_option pp.all true
set_option pp.all false
set_option pp.raw.maxDepth 32
set_option trace.profiler.output "foo"

-- This does not apply to all options: TODO
set_option autoImplicit true -- should not error!

-- -- TODO: why does this not work?
-- set_option linter.setOption false in
-- /--
-- Forbidden set_option pp.all; please remove
-- note: this linter can be disabled with `set_option linter.setOption false`
-- -/
-- #guard_msgs in
lemma foo : True := by
  set_option pp.all true in
  trivial

set_option pp.all false
set_option pp.raw.maxDepth 32
set_option trace.profiler.output "foo"

set_option autoImplicit true in
lemma foo' : True := trivial
