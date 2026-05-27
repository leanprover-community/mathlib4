import Mathlib.Tactic.Linter.AuxLemma
import Mathlib.Init

/-!
# Tests for the `auxLemma` linter

The important tests here reference *genuinely* auto-generated declarations (`match_1`,
`_proof_1`, `_sizeOf_1`), produced by the elaborator from the definitions below. If Lean's
naming scheme for these auxiliary declarations ever changes, these tests break — which is the
point: the linter would otherwise silently stop catching anything.
-/

set_option linter.auxLemma true

-- A `match`-based definition generates an auxiliary `foo.match_1`.
def foo : Nat → Nat
  | 0 => 0
  | n + 1 => n

-- A structure with a proof field, plus an instance discharging it by tactic, generates
-- `s._proof_1`; the structure itself generates `S._sizeOf_1`.
structure S where
  n : Nat
  h : 0 < n

def s : S where
  n := 1
  h := by decide

/--
warning: `foo.match_1` refers to an auto-generated auxiliary declaration. These are not stable across refactors; consider using a different approach.

Note: This linter can be disabled with `set_option linter.auxLemma false`
-/
#guard_msgs in
example := @foo.match_1

/--
warning: `s._proof_1` refers to an auto-generated auxiliary declaration. These are not stable across refactors; consider using a different approach.

Note: This linter can be disabled with `set_option linter.auxLemma false`
-/
#guard_msgs in
example := s._proof_1

-- `_sizeOf_1` is a compiler-internal that cannot be used as a term value, so we reference it
-- with `#check` and only guard the linter warning (ignoring the `#check` info output).
/--
warning: `S._sizeOf_1` refers to an auto-generated auxiliary declaration. These are not stable across refactors; consider using a different approach.

Note: This linter can be disabled with `set_option linter.auxLemma false`
-/
#guard_msgs(warning) in
#check @S._sizeOf_1

-- No warning on ordinary references, including names that merely resemble the auxiliary
-- patterns but lack the trailing digits (e.g. `Nat.rec`, `foo`).
#guard_msgs in
example := @foo

#guard_msgs in
example := @Nat.rec

-- The linter can be turned off.
set_option linter.auxLemma false in
#guard_msgs in
example := @foo.match_1
