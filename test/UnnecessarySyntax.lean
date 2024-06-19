import Mathlib.Tactic.Linter.UnnecessarySyntax
import Batteries

set_option linter.unnecessarySyntax false

/--
warning: `nolint simpNF` can be removed [⟨13, 8⟩, ⟨13, 21⟩]
note: this linter can be disabled with `set_option linter.unnecessarySyntax false`
-/
#guard_msgs in
set_option linter.unnecessarySyntax true in
-- this lemma is perfectly reasonable as a simp lemma, `nolint simpNF` is unnecessary
@[simp, nolint simpNF]
theorem imSimp : True := .intro

/--
warning: `simpNF` can be removed [⟨23, 8⟩, ⟨23, 14⟩, ⟨23, 27⟩, ⟨23, 33⟩]
note: this linter can be disabled with `set_option linter.unnecessarySyntax false`
-/
#guard_msgs in
-- this lemma is perfectly reasonable as a simp lemma, `nolint simpNF` is unnecessary
set_option linter.unnecessarySyntax true in
@[simp, nolint simpVarHead simpNF ]
theorem imSimpToo : True := .intro

-- the linter ignores `attribute`
#guard_msgs in
set_option linter.unnecessarySyntax true in
attribute [nolint simpNF] imSimp

-- the linter ignores `attribute`, even inside an `open ... in`
#guard_msgs in
set_option linter.unnecessarySyntax true in
open Nat in attribute [nolint simpNF] imSimp

-- this lemma should not be labeled as `simp`
#guard_msgs in
set_option linter.unnecessarySyntax true in
@[simp, nolint simpNF simpVarHead]
theorem imNotSimp {n : Nat} : n = n + 0 := rfl
