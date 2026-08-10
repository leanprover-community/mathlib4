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
`simp` sets, skipping any term it cannot evaluate.

## Main definitions

- `eval_rank`: the tactic.
- `norm_rank`: the simproc, for use in `simp` sets.
-/

public meta section

open Lean Meta Elab

initialize registerTraceClass `Tactic.evalRank

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

/-- Core of the `norm_rank` simprocs. Skips terms outside the method's scope; a failure
of a committed attempt throws. -/
def normRankCore : Simp.Simproc := fun e => do
  let_expr Matrix.rank _ _ _ _ _ A := e | return .continue
  let A ← instantiateMVars A
  let some (m, n, R, entries) ← matchMatrixLit? A
    | trace[Tactic.evalRank] "not a closed matrix literal{indentExpr A}"
      return .continue
  match ← checkBareissApplicable R with
  | .ok _ => return .done (← normalizeRank e A m n R entries)
  | .error err =>
    trace[Tactic.evalRank] "{err}{indentExpr A}"
    return .continue

end Mathlib.Tactic.Echelon

open Mathlib.Tactic.Echelon

/-- The `norm_rank` simproc normalizes `Matrix.rank` of a closed matrix literal via its
Bareiss decomposition. Terms it cannot evaluate are skipped. -/
simproc_decl norm_rank (Matrix.rank _) := fun e => do
  try normRankCore e
  catch ex =>
    trace[Tactic.evalRank] "{ex.toMessageData}"
    return .continue

/-- `eval_rank` reduces `Matrix.rank` of a closed matrix literal to a literal and tries to
close the goal. Rank terms the method skips are reported under `trace.Tactic.evalRank`. -/
elab (name := evalRank) "eval_rank" : tactic => do
  let goal ← Tactic.getMainGoal
  let ctx ← Simp.mkContext (config := { failIfUnchanged := false })
    (congrTheorems := ← getSimpCongrTheorems)
  let some keys ← Simp.getSimprocDeclKeys? ``norm_rank
    | throwError "internal error: no discrimination keys registered for `norm_rank`"
  let simprocs := ({} : Simp.Simprocs).addCore keys `evalRank (post := true) (.inl normRankCore)
  match ← simpGoal goal ctx #[simprocs] with
  | (none, _) => return
  | (some (_, goal'), _) =>
    if goal' == goal then
      throwError "eval_rank made no progress.\n\
        Additional information may be available using `set_option trace.Tactic.evalRank true`."
    Tactic.replaceMainGoal [goal']
    Tactic.evalTactic (← `(tactic| try lia))
