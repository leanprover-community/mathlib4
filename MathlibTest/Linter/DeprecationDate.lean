import Mathlib.Tactic.Linter.DeprecationDate

/-! Tests for the `deprecationDate` linter. -/

set_option linter.style.deprecationDate true

def target : Nat := 0

-- A valid date
#guard_msgs in
@[deprecated target (since := "2024-02-29")]
def ok : Nat := 0

/--
warning: '01-12-2026' is not a valid date; `(since := ...)` must have the form `YYYY-MM-DD`.

Note: This linter can be disabled with `set_option linter.style.deprecationDate false`
-/
#guard_msgs in
@[deprecated target (since := "01-12-2026")]
def yearLast : Nat := 0

/--
warning: '2026-15-03' is not a valid date; `(since := ...)` must have the form `YYYY-MM-DD`.

Note: This linter can be disabled with `set_option linter.style.deprecationDate false`
-/
#guard_msgs in
@[deprecated target (since := "2026-15-03")]
def monthTooBig : Nat := 0

/--
warning: '2025-02-29' is not a valid date; `(since := ...)` must have the form `YYYY-MM-DD`.

Note: This linter can be disabled with `set_option linter.style.deprecationDate false`
-/
#guard_msgs in
@[deprecated target (since := "2025-02-29")]
def notALeapYear : Nat := 0

/--
warning: '2026-3-15' is not a valid date; `(since := ...)` must have the form `YYYY-MM-DD`.

Note: This linter can be disabled with `set_option linter.style.deprecationDate false`
-/
#guard_msgs in
@[deprecated target (since := "2026-3-15")]
def notPadded : Nat := 0

/--
warning: 'v4.16.0' is not a valid date; `(since := ...)` must have the form `YYYY-MM-DD`.

Note: This linter can be disabled with `set_option linter.style.deprecationDate false`
-/
#guard_msgs in
@[deprecated target (since := "v4.16.0")]
def versionString : Nat := 0

-- The linter also covers `@[deprecated_arg]`.
/--
warning: '2026-15-03' is not a valid date; `(since := ...)` must have the form `YYYY-MM-DD`.

Note: This linter can be disabled with `set_option linter.style.deprecationDate false`
-/
#guard_msgs in
@[deprecated_arg old new (since := "2026-15-03")]
def withDeprecatedArg (new : Nat) : Nat := new

-- ... and `deprecated_syntax`.
syntax (name := myOldTactic) "myOldTactic" : tactic

/--
warning: '2026-15-03' is not a valid date; `(since := ...)` must have the form `YYYY-MM-DD`.

Note: This linter can be disabled with `set_option linter.style.deprecationDate false`
-/
#guard_msgs in
deprecated_syntax myOldTactic "use something else" (since := "2026-15-03")
