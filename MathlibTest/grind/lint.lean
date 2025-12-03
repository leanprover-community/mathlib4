import Mathlib

-- This check verifies that `grind` annotations in Mathlib do not trigger run-away instantiations.
-- If this test fails, please modify newly introduced `grind` annotations to use the
-- `grind_pattern ... where ...` syntax to add side conditions that will prevent the run-away.
-- See https://lean-lang.org/doc/reference/latest/The--grind--tactic/E___matching/ for details.
#grind_lint check (min := 20) in module Mathlib

-- (Note: the above #grind_lint take about 20s as of 2025-11-21.
-- If it becomes too slow, we may need to split this file and lint different submodules separately,
-- to get paralellism.)
