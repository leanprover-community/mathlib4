/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Init

/-! Tests for the linter against persistent `omit` commands. -/

set_option linter.mathlibStandardSet true

section
variable {α : Type} [Nonempty α] (h : True)
include h

/--
warning: Please use `omit ... in` to scope omitted variables to a single command.

Note: This linter can be disabled with `set_option linter.style.omit false`
-/
#guard_msgs in
omit h

/--
warning: Please use `omit ... in` to scope omitted variables to a single command.

Note: This linter can be disabled with `set_option linter.style.omit false`
-/
#guard_msgs in
omit [Nonempty α]

/--
warning: Please use `omit ... in` to scope omitted variables to a single command.

Note: This linter can be disabled with `set_option linter.style.omit false`
-/
#guard_msgs in
omit h -- Both names and multiline instance patterns are supported.
  [Nonempty α]

-- Elaborator errors should not produce an additional lint warning.
/-- error: `unknown` did not match any variables in the current scope -/
#guard_msgs in
omit unknown

-- Scoped commands, including multiline instance patterns, are allowed.
#guard_msgs in
omit h in
example : True := trivial

#guard_msgs in
omit
  [Nonempty α]
in
example : True := trivial

#guard_msgs in
omit h in
omit [Nonempty α] in
example : True := trivial

-- A scoped prefix does not hide a persistent `omit` in its body.
/--
warning: Please use `omit ... in` to scope omitted variables to a single command.

Note: This linter can be disabled with `set_option linter.style.omit false`
-/
#guard_msgs in
variable {h} in
omit [Nonempty α]

#guard_msgs in
set_option linter.style.omit false in
omit h

#guard_msgs in
variable {h} in
set_option linter.style.omit false in
omit h

-- Nested option scopes are respected, including explicitly re-enabling the linter.
/--
warning: Please use `omit ... in` to scope omitted variables to a single command.

Note: This linter can be disabled with `set_option linter.style.omit false`
-/
#guard_msgs in
set_option linter.style.omit false in
variable {h} in
set_option linter.style.omit true in
omit h

-- A syntax quotation is data, not a persistent change to section variables.
#guard_msgs in
open Lean in
example : MacroM Syntax := `(command| omit h)

-- Words in comments, strings, and fields are not commands.
#guard_msgs in
example : String := "omit h"

structure OmitField where
  «omit» : Nat

#guard_msgs in
example : OmitField where
  «omit» := 0

end
