/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Tactic.Echelon.Bareiss

/-!
# `norm_rank` simproc and `eval_rank` tactic

`eval_rank` closes goals of the form `Matrix.rank !![…] = k` over a commutative domain,
for matrices whose entries are numerals or `norm_num`-evaluable expressions.

`normalizeRank` matches `Matrix.rank M`, produces and elaborates a
Bareiss decomposition of `M`, applies `rank_eq`, and returns a `Simp.Result` rewriting
the rank to a literal.
-/

public meta section

open Lean Meta Elab Mathlib.Tactic.Echelon

/-- Rewrite `Matrix.rank M` to the pivot count of its Bareiss decomposition, or `none`
when `M` is not a closed `Fin`-indexed matrix literal — the commitment gate. Failures
past the gate are refusals of a committed attempt, and throw. -/
def normalizeRank (e : Expr) : MetaM (Option Simp.Result) := do
  match_expr e with
  | Matrix.rank _ _ _ _ _ M =>
    let M ← instantiateMVars M
    let some (m, n, R, entries) ← matchMatrixLit? M | return none
    let some _ ← synthInstance? (← mkAppM ``CommRing #[R])
      | throwError "expected the element type to be a commutative ring"
    let some _ ← synthInstance? (← mkAppOptM ``IsDomain #[some R, none])
      | throwError "expected the element type to be a domain"
    let decomp ← (mkBareissDecomposition M m n R entries).run'
    let pf ← mkAppM ``Bareiss.Decomposition.rank_eq #[decomp]
    let rankE ← mkAppM ``Bareiss.Decomposition.rank #[decomp]
    let some len := ((Kernel.whnf (← getEnv) (← getLCtx) rankE).toOption).bind (·.rawNatLit?)
      | throwError "the pivot count does not reduce to a literal"
    let k := mkNatLit len
    return some { expr := k, proof? := some (← mkExpectedTypeHint pf (← mkEq e k)) }
  | _ => return none

/-- The `norm_rank` simproc normalizes `Matrix.rank` of a closed matrix literal via its
Bareiss decomposition, and skips other `rank` terms. -/
simproc_decl norm_rank (Matrix.rank _) := fun e => do
  match ← normalizeRank e with
  | some r => return .done r
  | none => return .continue

/-- `eval_rank` reduces `Matrix.rank` of a closed matrix literal to a literal and tries to
close the goal. -/
elab (name := evalRank) "eval_rank" : tactic => do
  try
    Tactic.evalTactic (← `(tactic| simp only [norm_rank]))
  catch e =>
    -- distinguish simp's no-progress failure (nothing passed the commitment gate) from a
    -- committed refusal thrown by `normalizeRank`, which propagates verbatim
    if (← e.toMessageData.toString).startsWith "`simp` made no progress" then
      throwError "eval_rank: no closed `Matrix.rank` literal found in the goal"
    else
      throw e
  Tactic.evalTactic (← `(tactic| try omega))

end
