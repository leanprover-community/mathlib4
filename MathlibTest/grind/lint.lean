import Mathlib

#adaptation_note
/--
FIXME: please investigate these lemmas, and add guard conditions as needed.
(These appeared at nightly-2025-12-13.)
--/
#grind_lint skip Path.symm_apply
#grind_lint skip Set.Icc.convexCombo_symm

-- This check verifies that `grind` annotations in Mathlib do not trigger run-away instantiations.
-- If this test fails, please modify newly introduced `grind` annotations to use the
-- `grind_pattern ... where ...` syntax to add side conditions that will prevent the run-away.
-- See https://lean-lang.org/doc/reference/latest/The--grind--tactic/E___matching/ for details.
#grind_lint check (min := 20) in module Mathlib

-- (Note: the above #grind_lint take about 20s as of 2025-11-21.
-- If it becomes too slow, we may need to split this file and lint different submodules separately,
-- to get parallelism.)
