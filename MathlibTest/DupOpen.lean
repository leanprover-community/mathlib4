import Mathlib.Tactic.Linter.DupOpen

set_option linter.dupOpen true

section
/--
warning: The namespace 'Nat' in 'Nat' is already open.
note: this linter can be disabled with `set_option linter.dupOpen false`
---
warning: The namespace 'Nat' in 'Nat' is already open.
note: this linter can be disabled with `set_option linter.dupOpen false`
-/
#guard_msgs in
-- The duplicated `open Nat` namespace is flagged.  `Int` is unused, but allowed.
open Nat Int Nat
end

section
-- An unused `open` is allowed.
open Nat
end

namespace X.Y.X

/--
warning: The namespace 'X' in 'X.Y.X' is already open.
note: this linter can be disabled with `set_option linter.dupOpen false`
---
warning: The namespace 'X' in 'X.Y.X' is already open.
note: this linter can be disabled with `set_option linter.dupOpen false`
-/
#guard_msgs in
open X Y X -- Maybe this should be allowed, but the linter flags it.

end X.Y.X
