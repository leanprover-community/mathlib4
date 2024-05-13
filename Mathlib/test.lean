import Mathlib.Tactic.Linter.ge_or_gt
import Mathlib.Tactic.Common

--def ets := sorry

set_option linter.geOrGt false in
lemma test : 1 ≥ 2 := sorry

set_option linter.geOrGt true

lemma test2 : ∀ n ≥ 2, n = 2 := sorry
