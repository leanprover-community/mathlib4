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

This module defines the `eval_rank` tactic and the `norm_rank` simproc, which compute
the rank of a matrix literal with non-symbolic entries through an
`Echelon.Decomposition` certificate checked by the kernel.
-/

public meta section

open Lean Meta Elab Qq

namespace Mathlib.Tactic.Echelon

/-- Rewrite `Matrix.rank A` to the pivot count of the Bareiss decomposition of the matrix
literal `A`. -/
def normalizeRank (e A : Expr) (m n : Nat) (R : Expr) (entries : Array (Array Expr)) :
    MetaM Simp.Result := do
  let u ← getDecLevel R
  have α : Q(Type u) := R
  let res ← mkBareissDecomposition A m n α entries
  let pf ← mkAppM ``Echelon.Decomposition.rank_eq #[res.cert]
  let k := mkNatLit res.data.pivot.size
  return { expr := k, proof? := some (← mkExpectedTypeHint pf (← mkEq e k)) }

/-- Core of the `norm_rank` simproc. -/
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

/-- The `norm_rank` simproc evaluates the rank of matrices with non-symbolic entries.
Terms that it cannot evaluate are skipped. -/
simproc_decl norm_rank (Matrix.rank _) := fun e => do
  try normRankCore e
  catch ex =>
    trace[Tactic.evalRank] "{ex.toMessageData}"
    return .continue

/--
`eval_rank` evaluates the rank of matrices with non-symbolic entries.

The element type must be a commutative domain with kernel-decidable equality.
Terms skipped can be viewed by using `set_option trace.Tactic.evalRank true`.
-/
elab (name := evalRank) "eval_rank" : tactic => do
  try
    Tactic.evalTactic (← `(tactic| simp only [norm_rank]))
  catch _ =>
    throwError "`eval_rank` made no progress.\n\
      Additional information may be available using `set_option trace.Tactic.evalRank true`."
  Tactic.evalTactic (← `(tactic| try lia))
