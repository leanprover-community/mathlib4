import Mathlib.Data.Nat.Factorial.Basic

/-!
We check that ``1_000_000 !` evaluates in less than 10 seconds.
(This should be a conservative upper bound that will work on most hardware,
but still tight enough that we couldn't achieve it without binary splitting.)
-/

open Nat

/-- info: 18488884 -/
#guard_msgs in
run_elab show Lean.Elab.TermElabM Unit from do
  let start ← IO.monoNanosNow
  let result ← Lean.Elab.Term.evalTerm ℕ Lean.Nat.mkType (← `(1_000_000 ! |>.log2))
  IO.println result
  let finish ← IO.monoNanosNow
  guard (finish - start < 10_000_000_000)
