module
import Mathlib.Tactic.Linter.Style

set_option linter.style.show true

/-
Check that logged messages appear when errors with synthetic `sorry` are thrown.

If a choice node is produced, `evalChoice` (currently) resets the state, erasing logs, and
re-throwing the produced error. And if the error contains a synthetic sorry, Lean will not log it,
trusting that the (now-erased) logged errors that preceded it are sufficient. As such, a choice
node may ultimately produce a state with no visible errors at the tactic, since the logged ones
have been erased and the thrown ones are not rendered in expectation of the logged ones appearing.

This test fails correctly now because the parser avoids producing a choice node in the first place,
via `(priority := high)`.
-/

/-- error: Unknown identifier `arbitrary_ident` -/
#guard_msgs in
example : False := by show arbitrary_ident
