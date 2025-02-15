/-
Copyright (c) 2025 Yaël Dillies, Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Paul Lezeau
-/
import Mathlib.Data.Finset.Sort
import Mathlib.Lean.Expr.Lit
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.NormNum

/-!
# Simproc for `Int.divisorsAntidiag`
-/

open
  Qq
  Lean
    Meta
      Simp
    Elab
      Term
    Parser
      Tactic

namespace Mathlib.Tactic.Simp

-- #check Term.elabTermAndSynthesize

/-- Simproc to compute `Int.divisorsAntidiag`. -/
def divisorsAntidiag : Simproc := fun e ↦ do
  match ← inferTypeQ e with
  | ⟨1, ~q(Finset (ℤ × ℤ)), ~q(Int.divisorsAntidiag $e')⟩ =>
    let some z ← intLitQq? e' | throwError s!"{e'} is not a integer literal"
    logInfo s!"{z}"
    -- let antidiag ← unsafe evalExpr (Finset <| ℤ × ℤ) q(ℕ) e
    return .continue
    -- let S : Finset (ℤ × ℤ) := {}
    -- let _ ← (List.range (n+1)).mapM fun i =>
  -- let n := Lean.ToExpr.toExpr n
  -- let s : Q(Finset <| ℤ × ℤ) := q($(quote n))
  -- return .continue

  | _ => return .continue

simproc divisors_antidiag (Int.divisorsAntidiag _) := divisorsAntidiag

example : Int.divisorsAntidiag 10 = {(-1, -1), (1, 1)} := by
  simp

end Mathlib.Tactic.Simp
