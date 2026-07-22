/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Tactic.Echelon.Bareiss

/-!
# `norm_rank` simproc and `eval_rank` tactic (wip)

The read-off layer: matches `Matrix.rank M`, calls `reifyBareiss`, applies `rank_eq`, and
returns a `Simp.Result` rewriting the rank to a literal.
-/

public meta section

open Lean Meta Elab Mathlib.Tactic.Echelon

/-- Rewrite `Matrix.rank M` to the pivot count of its Bareiss decomposition. -/
def normalizeRank (e : Expr) : MetaM Simp.Result := do
  match_expr e with
  | Matrix.rank _ _ _ _ _ M =>
    let_expr Matrix _ _ R := ← inferType M
      | throwError "expected a matrix, got{indentExpr M}"
    let some _ ← synthInstance? (← mkAppM ``CommRing #[R])
      | throwError "expected the element type to be a commutative ring"
    let some _ ← synthInstance? (← mkAppOptM ``IsDomain #[some R, none])
      | throwError "expected the element type to be a domain"
    let decomp ← (reifyBareiss M).run'
    let pf ← mkAppM ``Bareiss.Decomposition.rank_eq #[decomp]
    let pivot ← whnf (← mkAppM ``Bareiss.Decomposition.pivot #[decomp])
    let k := mkNatLit (listLitLen pivot)
    return { expr := k, proof? := some (← mkExpectedTypeHint pf (← mkEq e k)) }
  | _ => throwError "expected `Matrix.rank _`, got{indentExpr e}"

/-- Normalize `Matrix.rank` of a closed matrix via its Bareiss decomposition. -/
simproc_decl norm_rank (Matrix.rank _) := fun e => return .done (← normalizeRank e)

/-- Reduce `Matrix.rank` of a closed matrix to a literal, then try to close the goal. -/
macro "eval_rank" : tactic => `(tactic| simp only [norm_rank] <;> try omega)

/-! ## tests (hardcoded placeholder) -/

example : (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℤ).rank = 2 := by eval_rank

example : (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℤ).rank ≤ 5 := by eval_rank

end
