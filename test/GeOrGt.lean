import Mathlib.Tactic.Linter.GeOrGt
import Mathlib.Tactic.Common

/-! Tests for the `ge_or_gt` linter -/

-- Doc comments are always ignored: they form a different syntax category.

-- Custom notation (e.g. `ℚ≥0`) is also ignored, as the `≥` is part of a token
-- and not a "greater or equal".
--local notation3 "𝕜≥0" => ℕ
--lemma fine : ℚ≥0 := 1

set_option linter.geOrGt false in
lemma test : 3 ≥ 2 := sorry

-- ≥ and > under binders ("predicate binders") are also not matched
-- I don't have to do anything, as these are a different syntax kind.
lemma test2 : ∀ n ≥ 2, n = 2 := sorry

lemma test3 : ∃ n ≥ 2, n = 2 := by use 2 ; trivial

lemma test4 (_h : ∃ n ≥ 2, n = 2) : True := trivial

-- the second one is linted, the first not!
lemma test5 (_h : ∀ n ≥ 42, n = 0) : True := trivial

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
lemma test7 : ∃ k : ℤ, k > 100 := by use 200; omega

-- We also check hypotheses.

/-- warning: '≥ or > is used in an illegal position
please change the statement to use ≤ or < instead
note: this linter can be disabled with `set_option linter.geOrGt false` -/
#guard_msgs in
lemma test8 (h : ∀ n : ℤ, n > 100) : ∃ k : ℤ, k > 100 := ⟨200, h 200⟩

-- Exclude ≥ as a comparator/unapplied relation; this should not be linted!
def dummy (_r : ℕ → ℕ → Prop) : Bool := True
lemma foo (_hf : dummy (· ≥ ·) ) : True := trivial

-- Perhaps, we check types of definitions.

-- We do not lint the bodies of proofs.
lemma proof1 : True := by
  have : 42 > 0 := sorry
  trivial

lemma proof2 : 42 > 0 := by
  have hm (m : ℕ) : m > 0 := sorry
  -- Meta blocks like `if ...` are also allowed.
  show 42 > 0
  omega

lemma proof3 {m n : ℕ} : True := by
  by_cases _h : m ≥ n
  repeat trivial

-- We do not check the bodies of definitions either:
-- we would only see these when unfolding anyway.

-- TODO: this should not be linted!
def dummy2 (_r : ℕ → ℕ → Prop) : Bool := True
lemma foo2 (_hf : dummy (· ≥ ·) ) : True := trivial
-- another case in SuccPred/Basic.lean: h : `IsWellOrder α (· > ·)` should be fine

/- Looking at all of mathlib, the following are probably false positives
- most common issue: used as a comparator function, e.g. in
   SuccPred/Basic, Data/List/Chain, Data/List/Range, Data/List/Sort, Data/Fintype/Card,
   Algebra/Lie/Nilpotent, Algebra/Lie/Submodule; MeasureTheory/Function/EssSup
  or as an order, e.g. IsWellOrder, WellFounded, Directed(On)

- in Order/Field/Basic:669, have `>` in a calc proof
- in Order/Ring/Defs:885, entire proof is (line 889 similar):
  `le_of_not_gt fun ha : a > 0 => (mul_pos ha hb).not_le h`

- as a branch in meta programming, e.g. `if qa > 0 then` in in NormNum/Inv:150
other occurrences in Tactic/Ring/Basic, Tactic/Linarith/Datatypes; Data/Finset/Basic

- Tactic/Linarith/Lemmas has a bunch of `have : xxx > 0`;
... perhaps these are not ideal, but they probably shouldn't get linted
- `Data/PNat/Basic` has `have hm : (m : ℕ) > 0 := m.pos` (that is later changed)

- less clear-cut: Data/Finset/Fold (but used in proofs)
- slightly more interesting: `wellFoundedOn_iff_no_descending_seq` in Order/WellFoundedSet
-/
