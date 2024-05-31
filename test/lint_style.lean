import Mathlib.Tactic.StyleLinters
import Mathlib.Tactic.Common

/-! Tests for all the style linters. -/

/-! Tests for the `setOption` linter -/
section setOption

set_option linter.setOption false -- TODO: enable, once the guard message bug is fixed

-- All types of options are supported: boolean, numeric and string-valued.
-- On the top level, i.e. as commands.

-- TODO: why does this guard_msg fail? how to suppress the output?
-- /--
-- Forbidden set_option `pp.all`; please remove
-- note: this linter can be disabled with `set_option
-- linter.setOption false`
-- -/
-- #guard_msgs in
set_option pp.all true
set_option pp.all false
set_option pp.raw.maxDepth 32
set_option trace.profiler.output "foo"

-- This does not lint on arbitrary options.
set_option autoImplicit false

-- We also cover set_option tactics.

-- -- TODO: why does this not work?
-- set_option linter.setOption false in
-- /--
-- Forbidden set_option pp.all; please remove
-- note: this linter can be disabled with `set_option linter.setOption false`
-- -/
-- #guard_msgs in
lemma tactic : True := by
  set_option pp.all true in
  trivial

lemma tactic2 : True := by
  set_option pp.raw.maxDepth 32 in
  trivial

lemma tactic3 : True := by
  set_option pp.all false in
  trivial

lemma tactic4 : True := by
  set_option trace.profiler.output "foo" in
  trivial

set_option autoImplicit true in
lemma foo' : True := trivial

-- TODO: add terms for the term form

end setOption
