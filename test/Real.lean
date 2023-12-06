/-
! This file was ported from Lean 3 source file `test/real.lean`
! leanprover-community/mathlib commit d7943885503965d07ccaeb390d65fbc3f45962e6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Real.Basic

private axiom test_sorry : ∀ {α}, α
unsafe def testRepr (r : ℝ) (s : String) : Lean.Elab.Command.CommandElabM Unit :=
unless toString (repr r) = s do throwError "got {repr r}"

run_cmd unsafe testRepr 0 "Real.ofCauchy (sorry /- 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ... -/)"
run_cmd unsafe testRepr 1 "Real.ofCauchy (sorry /- 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, ... -/)"
run_cmd unsafe testRepr (37 : ℕ) "Real.ofCauchy (sorry /- 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, ... -/)"
run_cmd unsafe testRepr (2 + 3) "Real.ofCauchy (sorry /- 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, ... -/)"
run_cmd unsafe testRepr ⟨CauSeq.Completion.mk $ ⟨fun n ↦ 2^(-n:ℤ), test_sorry⟩⟩
                        "Real.ofCauchy (sorry /- 1, (1 : Rat)/2, (1 : Rat)/4, (1 : Rat)/8, (1 : Rat)/16, (1 : Rat)/32, (1 : Rat)/64, (1 : Rat)/128, (1 : Rat)/256, (1 : Rat)/512, ... -/)"
