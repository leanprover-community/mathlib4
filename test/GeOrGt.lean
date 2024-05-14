import Mathlib.Tactic.Linter.GeOrGt
import Mathlib.Tactic.Common

/-! Tests for the `ge_or_gt` linter -/

-- Doc comments are always ignored: they form a different syntax category.

-- Custom notation (e.g. `ℚ≥0`) is also ignored, as the `≥` is part of a token
-- and not a "greater or equal".
local notation "ℚ≥0" => ℕ
def fine : ℚ≥0 := 1

-- The linter can be disabled.
set_option linter.geOrGt false in
lemma test : 3 ≥ 2 := by omega

/-- warning: '≥ or > is used in an illegal position
please change the statement to use ≤ or < instead
note: this linter can be disabled with `set_option linter.geOrGt false` -/
#guard_msgs in
lemma test' : 3 ≥ 2 := by omega

-- ≥ and > under binders ("predicate binders") are not matched.
-- This applies to conclusions and hypotheses.
lemma test2 : ∀ n ≥ 2, True := fun _ _ ↦ trivial
lemma test3 : ∃ n ≥ 2, n = 2 := by use 2 ; trivial

lemma test4 (_h : ∃ n ≥ 2, n = 2) : True := trivial
lemma test5 (_h : ∀ n ≥ 42, n = 0) : True := trivial

-- The linter errors on > and ≥ in the conclusion.

/-- warning: '≥ or > is used in an illegal position
please change the statement to use ≤ or < instead
note: this linter can be disabled with `set_option linter.geOrGt false` -/
#guard_msgs in
lemma test6 (_h : ∀ n ≥ 42, n = 0) : ∃ m, m > 42 := by use 43; omega

-- We do check theorem or lemma statements.
/-- warning: '≥ or > is used in an illegal position
please change the statement to use ≤ or < instead
note: this linter can be disabled with `set_option linter.geOrGt false` -/
#guard_msgs in
lemma test7 : ∃ k : ℤ, k ≥ 100 := by use 200; omega

-- We also check hypotheses.

/-- warning: '≥ or > is used in an illegal position
please change the statement to use ≤ or < instead
note: this linter can be disabled with `set_option linter.geOrGt false` -/
#guard_msgs in
lemma test8 (h : ∀ n : ℤ, n > 100) : ∃ k : ℤ, k > 100 := ⟨200, h 200⟩

/-- warning: '≥ or > is used in an illegal position
please change the statement to use ≤ or < instead
note: this linter can be disabled with `set_option linter.geOrGt false` -/
#guard_msgs in
lemma test8' (h : ∀ n : ℤ, n ≥ 100) : ∃ k : ℤ, k ≥ 100 := ⟨200, h 200⟩

-- Exclude ≥ as a comparator/unapplied relation; this should not be linted!
def dummy (_r : ℕ → ℕ → Prop) : Bool := True
lemma foo (_hf : dummy (· ≥ ·) ) : True := trivial
lemma foo' (_hf : dummy (· > ·) ) : True := trivial

-- We also check types of definitions.

/--
warning: '≥ or > is used in an illegal position
please change the statement to use ≤ or < instead
note: this linter can be disabled with `set_option linter.geOrGt false`
-/
#guard_msgs in
def stupid : 4 > 2 := Nat.lt_of_sub_eq_succ rfl

-- We do lint the bodies of proofs: we deemed the trade-off acceptable, for now.

/--
warning: '≥ or > is used in an illegal position
please change the statement to use ≤ or < instead
note: this linter can be disabled with `set_option linter.geOrGt false`
-/
#guard_msgs in
lemma proof1 : True := by
  have : 42 > 0 := Nat.zero_lt_succ 41
  trivial

/--
warning: '≥ or > is used in an illegal position
please change the statement to use ≤ or < instead
note: this linter can be disabled with `set_option linter.geOrGt false`
-/
#guard_msgs in
lemma proof2 : 42 > 0 := by
  have _hm (m : ℕ) : m ≥ 0 := by omega
  -- Meta blocks like `if ...` are also allowed.
  show 42 > 0
  omega

/--
warning: '≥ or > is used in an illegal position
please change the statement to use ≤ or < instead
note: this linter can be disabled with `set_option linter.geOrGt false`
-/
#guard_msgs in
lemma proof3 {m n : ℕ} : True := by
  by_cases _h : m ≥ n
  repeat trivial

-- We do check the bodies of definitions... no tests since this file is long enough.
