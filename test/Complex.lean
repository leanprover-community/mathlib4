import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.DualNumber

open DualNumber

private axiom test_sorry : ∀ {α}, α
unsafe def testRepr (c : ℂ) (s : String) : Lean.Elab.Command.CommandElabM Unit :=
unless toString (repr c) = s do throwError "got {repr c}"

unsafe def testDualNumberRepr (c : ℂ[ε]) (s : String) : Lean.Elab.Command.CommandElabM Unit :=
unless toString (repr c) = s do throwError "got {repr c}"

-- Test base complex number representation
run_cmd unsafe testRepr 0 "Real.ofCauchy (sorry /- 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ... -/) + Real.ofCauchy (sorry /- 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ... -/)*I"
run_cmd unsafe testRepr 1 "Real.ofCauchy (sorry /- 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, ... -/) + Real.ofCauchy (sorry /- 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ... -/)*I"
run_cmd unsafe testRepr 4 "Real.ofCauchy (sorry /- 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, ... -/) + Real.ofCauchy (sorry /- 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ... -/)*I"
run_cmd unsafe testRepr Complex.I "Real.ofCauchy (sorry /- 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ... -/) + Real.ofCauchy (sorry /- 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, ... -/)*I"

-- Test whether the parentheses are properly shown around a complex number when required
run_cmd unsafe testDualNumberRepr (2 : ℂ[ε]) "Real.ofCauchy (sorry /- 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, ... -/) + Real.ofCauchy (sorry /- 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ... -/)*I + (Real.ofCauchy (sorry /- 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ... -/) + Real.ofCauchy (sorry /- 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ... -/)*I)*ε"
