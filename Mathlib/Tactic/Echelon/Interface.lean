/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Tactic.Echelon.Bareiss

public meta import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# `eval_rank`: rank of matrix literals by Bareiss elimination

`eval_rank` (and the underlying simproc `norm_rank`) closes goals of the form
`Matrix.rank !![…] = k` over a commutative domain, for matrices whose entries are
numerals or `norm_num`-evaluable expressions.
-/

public meta section

open Lean Meta Elab

namespace Mathlib.Tactic.Echelon

/- TODO: `!![…]` still elaborates to `Matrix.of` applied to `Matrix.vecCons` chains; if
#41160 switches it to the merged `Matrix.ofArray`, the parsers below need a corresponding
adaptation. -/
/-- Parse a `![a, b, …]` vector literal into its entries. -/
partial def parseVec? (e : Expr) : Option (Array Expr) :=
  go #[] e
where
  go (acc : Array Expr) (e : Expr) : Option (Array Expr) :=
    match_expr e.cleanupAnnotations with
    | Matrix.vecEmpty _ => some acc
    | Matrix.vecCons _ _ head tail => go (acc.push head) tail
    | _ => none

/-- Parse a `!![…]` matrix literal into its rows of entry expressions. -/
def parseMatrix? (M : Expr) : Option (Array (Array Expr)) :=
  match_expr M.cleanupAnnotations with
  | DFunLike.coe _ _ _ _ f v =>
    match_expr f.cleanupAnnotations with
    | Matrix.of _ _ _ => (parseVec? v).bind (·.mapM parseVec?)
    | _ => none
  | _ => none

/-- Match a closed `Fin`-indexed matrix literal: its dimensions, element type, and rows of
entries. -/
def matchMatrixLit? (M : Expr) : MetaM (Option (Nat × Nat × Expr × Array (Array Expr))) := do
  let some entries := parseMatrix? M | return none
  let_expr Matrix finM finN R := ← inferType M | return none
  let_expr Fin mE := finM.cleanupAnnotations | return none
  let_expr Fin nE := finN.cleanupAnnotations | return none
  -- the counts appear as `OfNat` numerals or as raw literals; `Expr.nat?` matches only the
  -- former
  let some m := mE.nat?.orElse fun _ => mE.rawNatLit? | return none
  let some n := nE.nat?.orElse fun _ => nE.rawNatLit? | return none
  unless entries.size == m && entries.all (·.size == n) do return none
  -- closedness: an entry with free variables (hypothesis- or let-bound) is not evaluable
  -- here; unfold or substitute such variables before calling the tactic
  unless entries.all (·.all fun e => !e.hasFVar && !e.hasExprMVar) do return none
  return some (m, n, R, entries)

/-- Match `Matrix.rank` of a matrix literal: the shape half of the commitment gate
(`checkBareissCommittal` is the applicability half); never throws. -/
def matchRankLit? (e : Expr) :
    MetaM (Option (Expr × Nat × Nat × Expr × Array (Array Expr))) := do
  match_expr e with
  | Matrix.rank _ _ _ _ _ M =>
    let M ← instantiateMVars M
    let some (m, n, R, entries) ← matchMatrixLit? M | return none
    return some (M, m, n, R, entries)
  | _ => return none

/-- Rewrite `Matrix.rank M` to the pivot count of the Bareiss decomposition of the matrix
literal `M`, as matched by `matchRankLit?`. Everything here is past the commitment gate:
failures are refusals of a committed attempt, and throw. -/
def normalizeRank (e M : Expr) (m n : Nat) (R : Expr) (entries : Array (Array Expr)) :
    MetaM Simp.Result := do
  let decomp ← (mkBareissDecomposition M m n R entries).run'
  let pf ← mkAppM ``Bareiss.Decomposition.rank_eq #[decomp]
  let rankE ← mkAppM ``Bareiss.Decomposition.rank #[decomp]
  let some len := ((Kernel.whnf (← getEnv) (← getLCtx) rankE).toOption).bind (·.rawNatLit?)
    | throwError "the pivot count does not reduce to a literal"
  let k := mkNatLit len
  return { expr := k, proof? := some (← mkExpectedTypeHint pf (← mkEq e k)) }

end Mathlib.Tactic.Echelon

open Mathlib.Tactic.Echelon

/-- The `norm_rank` simproc normalizes `Matrix.rank` of a closed matrix literal via its
Bareiss decomposition. Other `rank` terms, and element types the Bareiss method does not
apply to, are skipped. -/
simproc_decl norm_rank (Matrix.rank _) := fun e => do
  let some (M, m, n, R, entries) ← matchRankLit? e | return .continue
  let .ok _ ← checkBareissCommittal R | return .continue
  return .done (← normalizeRank e M m n R entries)

/-- `eval_rank` reduces `Matrix.rank` of a closed matrix literal to a literal and tries to
close the goal. -/
elab (name := evalRank) "eval_rank" : tactic => do
  let goal ← Tactic.getMainGoal
  Tactic.evalTactic (← `(tactic| simp -failIfUnchanged only [norm_rank]))
  unless ← goal.isAssigned do
    -- diagnose the skip: a closed rank literal over an unsupported element type reports the
    -- method's rejection reason; otherwise there was no closed rank literal to work on
    (← goal.getType).forEach fun e => do
      if e.isAppOfArity ``Matrix.rank 6 then
        if let some (_, _, _, R, _) ← matchRankLit? e then
          if let .error why ← checkBareissCommittal R then
            throwError why
    throwError "eval_rank failed to evaluate the rank of any closed matrix literal in the goal"
  Tactic.evalTactic (← `(tactic| try omega))
