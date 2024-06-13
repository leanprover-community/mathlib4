import Mathlib.Tactic.Linter.DeprecateNoSince

/-- βk𝕜⟨⟩-/@[simp, deprecated Nat "wh `Nat`"] theorem oh1 : True := .intro

/--
warning: After here, please add (since := "2024-06-13") or whatever date is appropriate `⟨11, 22⟩`
note: this linter can be disabled with `set_option linter.deprecateNoSince false`
-/
#guard_msgs in
@[simp, deprecated Nat] theorem oh2 : True := .intro

/--
warning: After here, please add (since := "2024-06-13") or whatever date is appropriate `⟨18, 18⟩`
note: this linter can be disabled with `set_option linter.deprecateNoSince false`
-/
#guard_msgs in
@[simp, deprecated] theorem oh3 : True := .intro
