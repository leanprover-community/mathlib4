/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison
-/
import Lean.Elab.Command

/-!
# User commands for assert the (non-)existence of declaration or instances.

These commands are used to enforce the independence of different parts of mathlib.

## TODO

Potentially after the port reimplement the mathlib 3 linters to check that declarations asserted
about do eventually exist.

Implement `assert_instance` and `assert_no_instance`
-/

section
open Lean Elab Meta

/--
`assert_exists n` is a user command that asserts that a declaration named `n` exists
in the current import scope.

Be careful to use names (e.g. `Rat`) rather than notations (e.g. `ℚ`).
-/
elab "assert_exists " n:ident : command => do
  -- this throw an error if the user types something ambiguous or doesn't exist, otherwise succeed
  let _ ← resolveGlobalConstNoOverloadWithInfo n

/--
`assert_not_exists n` is a user command that asserts that a declaration named `n` *does not exist*
in the current import scope.

Be careful to use names (e.g. `Rat`) rather than notations (e.g. `ℚ`).

It may be used (sparingly!) in mathlib to enforce plans that certain files
are independent of each other.

If you encounter an error on an `assert_not_exists` command while developing mathlib,
it is probably because you have introduced new import dependencies to a file.

In this case, you should refactor your work
(for example by creating new files rather than adding imports to existing files).
You should *not* delete the `assert_not_exists` statement without careful discussion ahead of time.
-/
elab "assert_not_exists " n:ident : command =>
  do let [] ← try resolveGlobalConstWithInfos n catch _ => return
      | throw <| .error n m!"Declaration {n} is not allowed to be imported by this file.\n\n\
          These invariants are maintained by `assert_not_exists` statements, \
          and exist in order to ensure that \"complicated\" parts of the library \
          are not accidentally introduced as dependencies of \"simple\" parts of the library."
