import Mathlib.Tactic.Linter.UnnecessarySyntax
import Batteries

set_option linter.unnecessarySyntax false

set_option linter.unnecessarySyntax true in
/--
warning: `nolint simpNF` can be removed ⟨13, 14⟩
note: this linter can be disabled with `set_option linter.unnecessarySyntax false`
-/
#guard_msgs in
-- this lemma is perfectly reasonable as a simp lemma, `nolint simpNF` is unnecessary
@[simp, nolint simpNF]
theorem imSimp : True := .intro

-- the linter ignores `attribute`
#guard_msgs in
attribute [nolint simpNF] imSimp

-- this lemma should not be labeled as `simp`
#guard_msgs in
@[simp, nolint simpNF simpVarHead]
theorem imNotSimp {n : Nat} : n = n + 0 := rfl
