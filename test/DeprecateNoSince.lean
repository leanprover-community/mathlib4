import Mathlib.Tactic.Linter.DeprecateNoSince

set_option linter.deprecateNoSince false

/--
warning: After here, please add (since := "2024-06-14") or whatever date is appropriate `⟨11, 44⟩`
note: this linter can be disabled with `set_option linter.deprecateNoSince false`
-/
#guard_msgs in
set_option linter.deprecateNoSince true in
/-- βk𝕜⟨⟩-/@[simp, deprecated Nat "wh `Nat`"] theorem oh1 : True := .intro

/--
warning: After here, please add (since := "2024-06-14") or whatever date is appropriate `⟨19, 22⟩`
note: this linter can be disabled with `set_option linter.deprecateNoSince false`
-/
#guard_msgs in
set_option linter.deprecateNoSince true in
@[simp, deprecated Nat] theorem oh2 : True := .intro

/--
warning: After here, please add (since := "2024-06-14") or whatever date is appropriate `⟨27, 18⟩`
note: this linter can be disabled with `set_option linter.deprecateNoSince false`
-/
#guard_msgs in
set_option linter.deprecateNoSince true in
@[simp, deprecated] theorem oh3 : True := .intro
