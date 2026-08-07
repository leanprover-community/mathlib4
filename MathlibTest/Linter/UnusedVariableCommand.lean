/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

import Mathlib.Init
import Mathlib.Tactic.Linter.UnusedVariableCommand

/-! # Tests for the `unusedVariableCommand` linter

The linter reports `variable` binders that no declaration in their scope uses. It fires when
the scope closes: at its `end` command, or at a terminal command (`#exit`, end of file).
-/

set_option linter.unusedVariableCommand true

-- An unused binder: the linter fires at the `end` of the section.
section
variable (unusedNat : Nat)

/--
warning: variable 'unusedNat' is never used in this scope

Note: This linter can be disabled with `set_option linter.unusedVariableCommand false`
-/
#guard_msgs in
end

-- A binder that a theorem uses: no warning.
section
variable (usedNat : Nat)

theorem usedNat_eq : usedNat = usedNat := rfl

#guard_msgs in
end

-- A binder that only an `example` uses: no warning. `example` adds no declaration to the
-- environment, so the identifier occurrences in the command syntax provide the usage.
section
variable (exampleNat : Nat)

example : exampleNat = exampleNat := rfl

#guard_msgs in
end

-- A binder that a declaration includes only as a dependency: no warning. The syntax of
-- `depFin_eq` does not mention `depN`, but the leading telescope of `depFin_eq` binds it.
section
variable (depN : Nat) (depFin : Fin depN)

theorem depFin_eq : depFin = depFin := rfl

#guard_msgs in
end

-- Two binders, one used: the linter reports only the unused one.
section
variable {usedT unusedT : Type}

def idUsed (t : usedT) : usedT := t

/--
warning: variable 'unusedT' is never used in this scope

Note: This linter can be disabled with `set_option linter.unusedVariableCommand false`
-/
#guard_msgs in
end

-- Nested scopes: a declaration in the inner namespace uses the outer binder; the unused
-- inner binder gets its warning at `end Inner`.
section
variable (outerN : Nat)

namespace Inner
variable (innerUnused : Bool)

def useOuter : Nat := outerN

/--
warning: variable 'innerUnused' is never used in this scope

Note: This linter can be disabled with `set_option linter.unusedVariableCommand false`
-/
#guard_msgs in
end Inner

#guard_msgs in
end

-- A `variable (annA)` annotation update rebuilds the binder group: the linter still tracks
-- each binder once and reports each unused binder once.
section
variable {annA annB : Nat}
variable (annA)

/--
warning: variable 'annA' is never used in this scope

Note: This linter can be disabled with `set_option linter.unusedVariableCommand false`
---
warning: variable 'annB' is never used in this scope

Note: This linter can be disabled with `set_option linter.unusedVariableCommand false`
-/
#guard_msgs in
end

-- `include` is binder management, not usage: the binder stays unused.
section
variable (hTrue : True)
include hTrue

/--
warning: variable 'hTrue' is never used in this scope

Note: This linter can be disabled with `set_option linter.unusedVariableCommand false`
-/
#guard_msgs in
end

-- A terminal command reports the binders of every open scope.
section
variable (eofUnused : Nat)

/--
warning: using 'exit' to interrupt Lean
---
warning: variable 'eofUnused' is never used in this scope

Note: This linter can be disabled with `set_option linter.unusedVariableCommand false`
-/
#guard_msgs in
#exit
