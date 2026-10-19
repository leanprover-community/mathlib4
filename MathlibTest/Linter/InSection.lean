/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Init

/-! Tests for commands followed by `in section`. -/

set_option linter.mathlibStandardSet true

section
variable (h : True)

/--
warning: Please put `section` before the command, rather than using `... in section`.

Note: This linter can be disabled with `set_option linter.style.inSection false`
-/
#guard_msgs in
omit h in
section
end

/--
warning: Please put `section` before the command, rather than using `... in section`.

Note: This linter can be disabled with `set_option linter.style.inSection false`
-/
#guard_msgs in
include h in section
end

/--
warning: Please put `section` before the command, rather than using `... in section`.

Note: This linter can be disabled with `set_option linter.style.inSection false`
-/
#guard_msgs in
variable {h} in
section
end

/--
warning: Please put `section` before the command, rather than using `... in section`.

Note: This linter can be disabled with `set_option linter.style.inSection false`
-/
#guard_msgs in
set_option autoImplicit false in
section
end

-- The check applies to every command prefix, including opening namespaces and local syntax.
/--
warning: Please put `section` before the command, rather than using `... in section`.

Note: This linter can be disabled with `set_option linter.style.inSection false`
-/
#guard_msgs in
open Nat in
section
end

/--
warning: Please put `section` before the command, rather than using `... in section`.

Note: This linter can be disabled with `set_option linter.style.inSection false`
-/
#guard_msgs in
attribute [local simp] Nat.add_zero in
section
end

/--
warning: Please put `section` before the command, rather than using `... in section`.

Note: This linter can be disabled with `set_option linter.style.inSection false`
-/
#guard_msgs in
local notation "InSectionTrue" => True in
section
end

/--
warning: Please put `section` before the command, rather than using `... in section`.

Note: This linter can be disabled with `set_option linter.style.inSection false`
-/
#guard_msgs in
universe inSectionUniverse in
section
end

-- Comments and modifiers do not hide the section header.
/--
warning: Please put `section` before the command, rather than using `... in section`.

Note: This linter can be disabled with `set_option linter.style.inSection false`
-/
#guard_msgs in
omit h in
/- A comment between the commands. -/
noncomputable section
end

-- A chain of wrappers receives one warning, pointing at the first offending command.
/--
warning: Please put `section` before the command, rather than using `... in section`.

Note: This linter can be disabled with `set_option linter.style.inSection false`
-/
#guard_msgs in
omit h in
set_option autoImplicit false in
section
end

/--
warning: Please put `section` before the command, rather than using `... in section`.

Note: This linter can be disabled with `set_option linter.style.inSection false`
-/
#guard_msgs in
set_option autoImplicit false in
set_option pp.universes false in
section
end

-- The outermost command in a chain is reported.
/--
warning: Please put `section` before the command, rather than using `... in section`.

Note: This linter can be disabled with `set_option linter.style.inSection false`
-/
#guard_msgs in
open Nat in
omit h in
section
end

-- The linter obeys option settings anywhere in a wrapper chain.
#guard_msgs in
set_option linter.style.inSection false in
omit h in
section
end

#guard_msgs in
omit h in
set_option linter.style.inSection false in
section
end

/--
warning: Please put `section` before the command, rather than using `... in section`.

Note: This linter can be disabled with `set_option linter.style.inSection false`
-/
#guard_msgs in
set_option linter.style.inSection false in
set_option linter.style.inSection true in
section
end

-- Ordinary declaration-local commands remain allowed.
#guard_msgs in
omit h in
example : True := trivial

#guard_msgs in
include h in
example : True := h

#guard_msgs in
variable {h} in
example : True := h

#guard_msgs in
set_option autoImplicit false in
example : True := trivial

#guard_msgs in
open Nat in
example : Nat := succ 0

#guard_msgs in
attribute [local simp] Nat.add_zero in
example : True := trivial

#guard_msgs in
local notation "InSectionTrue" => True in
example : True := trivial

-- Explicit sections with commands inside them are allowed.
section
omit h
example : True := trivial
end

section
include h
example : True := h
end

section
variable {h}
example : True := h
end

section
set_option autoImplicit false
example : True := trivial
end

-- Quotations are data, rather than executed commands.
#guard_msgs in
open Lean in
example : MacroM Syntax := `(command| omit h in section)

#guard_msgs in
example : String := "set_option autoImplicit false in section"

-- Errors from elaboration suppress additional lint warnings.
/-- error: `unknown` did not match any variables in the current scope -/
#guard_msgs in
omit unknown in
section
end

end
