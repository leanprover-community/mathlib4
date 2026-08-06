/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Tactic.Echelon.Bareiss
public import Mathlib.Tactic.Echelon.Parsing

/-!
# `eval_rank`: rank of matrix literals by Bareiss elimination

`eval_rank` closes goals of the form `Matrix.rank !![…] = k` over a commutative domain
with kernel-decidable equality, for entries the selected computation model evaluates:
numerals and `norm_num`-evaluable expressions everywhere, plus ring-specific literals
such as the `⟨a, b⟩` pairs of `ℤ√d`. The simproc `norm_rank` rewrites such ranks inside
`simp` sets, skipping any term it cannot evaluate; its throwing variant
`norm_rank_throw` reports the failure instead, and underlies `eval_rank`.

## Main definitions

- `eval_rank`: the tactic.
- `norm_rank`: the simproc, for use in `simp` sets.
- `norm_rank_throw`: the throwing variant of `norm_rank`, used by `eval_rank`.
-/

public meta section

open Lean Meta Elab

namespace Mathlib.Tactic.Echelon

/-- Rewrite `Matrix.rank A` to the pivot count of the Bareiss decomposition of the matrix
literal `A`. -/
def normalizeRank (e A : Expr) (m n : Nat) (R : Expr) (entries : Array (Array Expr)) :
    MetaM Simp.Result := do
  let decomp ← (mkBareissDecomposition A m n R entries).run'
  let pf ← mkAppM ``Echelon.Decomposition.rank_eq #[decomp]
  -- the statement's right-hand side: the pivoted-row count of the certificate
  let cnt := (← inferType pf).appArg!
  let some len := ((Kernel.whnf (← getEnv) (← getLCtx) cnt).toOption).bind (·.rawNatLit?)
    | throwError "the pivot count does not reduce to a literal"
  let k := mkNatLit len
  return { expr := k, proof? := some (← mkExpectedTypeHint pf (← mkEq e k)) }

/-- Core of the `norm_rank` simprocs: normalize `Matrix.rank` of a closed matrix literal
via its Bareiss decomposition. Skips terms outside the method's scope; a failure of a
committed attempt throws. -/
def normRankCore : Simp.Simproc := fun e => do
  let_expr Matrix.rank _ _ _ _ _ A := e | return .continue
  let A ← instantiateMVars A
  let some (m, n, R, entries) ← matchMatrixLit? A | return .continue
  let .ok _ ← checkBareissApplicable R | return .continue
  return .done (← normalizeRank e A m n R entries)

end Mathlib.Tactic.Echelon

open Mathlib.Tactic.Echelon

/-- The `norm_rank` simproc normalizes `Matrix.rank` of a closed matrix literal via its
Bareiss decomposition. Terms it cannot evaluate — outside the method's scope or failing
evaluation — are skipped. -/
simproc_decl norm_rank (Matrix.rank _) := fun e => do
  try normRankCore e catch _ => return .continue

/-- The throwing variant of `norm_rank`: a failure of a committed attempt surfaces as an
error naming its cause. Used by `eval_rank`. -/
simproc_decl norm_rank_throw (Matrix.rank _) := fun e => normRankCore e

/-- `eval_rank` reduces `Matrix.rank` of a closed matrix literal to a literal and tries to
close the goal. -/
elab (name := evalRank) "eval_rank" : tactic => do
  let goal ← Tactic.getMainGoal
  Tactic.evalTactic (← `(tactic| simp -failIfUnchanged only [norm_rank_throw]))
  unless ← goal.isAssigned do
    /- diagnose the skip: a closed rank literal over an unsupported element type reports the
     method's rejection reason; otherwise there was no closed rank literal to work on.
      However, this causes a duplicate parsing and re-check of the error message for the ring R.
    -/
    (← instantiateMVars (← goal.getType)).forEach fun e => do
      if e.isAppOfArity ``Matrix.rank 6 then
        if let some (_, _, R, _) ← matchMatrixLit? e.appArg! then
          if let .error why ← checkBareissApplicable R then
            throwError why
    throwError "eval_rank failed to evaluate the rank of any closed matrix literal in the goal"
  Tactic.evalTactic (← `(tactic| try lia))
