import Mathlib.Tactic.Linter.GeOrGt
import Mathlib.Tactic.Common

/- Tests for the `ge_or_gt` linter -/

-- Doc comments are always ignored: they form a different syntax category.
-- Custom notation (e.g. `ℚ≥0`) is ignored, as the `≥` is part of a token and not a "greater or equal".

set_option linter.geOrGt false in
lemma test : 3 ≥ 2 := sorry

set_option linter.geOrGt true

-- ≥ and > under binders ("predicate binders") are also not matched
-- I don't have to do anything, as these are a different syntax kind.
lemma test2 : ∀ n ≥ 2, n = 2 := sorry

lemma test3 : ∃ n ≥ 2, n = 2 := by use 2 ; trivial

lemma test4 (h : ∃ n ≥ 2, n = 2) : True := trivial

-- the second one is linted, the first not!
lemma test5 (_h : ∀ n ≥ 42, n = 0) : True := trivial

--#guard_message in
/---/
lemma test6 (_h : ∀ n ≥ 42, n = 0) : ∃ m, m > 42 := sorry

-- TODO: this should not be linted!
def dummy (_r : ℕ → ℕ → Prop) : Bool := True
lemma foo (_hf : dummy (· ≥ ·) ) : True := trivial
-- another case in SuccPred/Basic.lean: h : `IsWellOrder α (· > ·)` should be fine
