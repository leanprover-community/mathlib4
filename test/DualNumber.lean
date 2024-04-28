import Mathlib.Algebra.DualNumber

open DualNumber

unsafe def testRepr (c : ℕ[ε]) (s : String) : Lean.Elab.Command.CommandElabM Unit :=
unless toString (repr c) = s do throwError "got {repr c}"

unsafe def testNestedRepr (c : (ℕ[ε])[ε]) (s : String) : Lean.Elab.Command.CommandElabM Unit :=
unless toString (repr c) = s do throwError "got {repr c}"

-- Test base dual number representation
run_cmd unsafe testRepr 0 "0 + 0*ε"
run_cmd unsafe testRepr 2 "2 + 0*ε"
run_cmd unsafe testRepr (2 + 4) "6 + 0*ε"

-- Test whether the parentheses are properly shown around a dual number when required
run_cmd unsafe testNestedRepr (2 : (ℕ[ε])[ε]) "2 + 0*ε + (0 + 0*ε)*ε"
