import Mathlib.Tactic.Linter.DupOpen

set_option linter.dupOpen true

variable {a : Nat} in
/--
warning: The namespace 'Nat' is already open.
note: this linter can be disabled with `set_option linter.dupOpen false`
-/
#guard_msgs in
-- A duplicated `open` namespace is flagged.
open Nat Nat

section
-- An unused `open` is allowed.
open Nat
end
