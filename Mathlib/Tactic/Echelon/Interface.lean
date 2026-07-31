/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Tactic.Echelon.Bareiss

public meta import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# `norm_rank` simproc and `eval_rank` tactic

`eval_rank` closes goals of the form `Matrix.rank !![…] = k` over a commutative domain,
for matrices whose entries are numerals or `norm_num`-evaluable expressions.

`matchRankLit?` is the commitment gate: it matches `Matrix.rank` of a matrix literal and
never throws. `normalizeRank` is the committed phase: it produces and elaborates a
Bareiss decomposition of the matched matrix, applies `rank_eq`, and returns a
`Simp.Result` rewriting the rank to a literal; its failures throw.
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
entries. Commits into computation if this succeeds. -/
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
  return some (m, n, R, entries)

/-- Match `Matrix.rank` of a matrix literal: the commitment gate. Returns the matrix with
its parsed dimensions, element type, and entries, or `none` when the term does not match —
never throws. -/
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
  if (← bareissObstruction? R).isSome then return .continue
  return .done (← normalizeRank e M m n R entries)

/-- `eval_rank` reduces `Matrix.rank` of a closed matrix literal to a literal and tries to
close the goal. -/
elab (name := evalRank) "eval_rank" : tactic => do
  let goal ← Tactic.getMainGoal
  -- `-failIfUnchanged` so that a gate-wide skip is detected by goal identity below, rather
  -- than by matching `simp`'s no-progress error message; a committed refusal thrown by
  -- `normalizeRank` propagates verbatim
  Tactic.evalTactic (← `(tactic| simp -failIfUnchanged only [norm_rank]))
  if (← Tactic.getUnsolvedGoals).any (· == goal) then
    -- diagnose the skip: a rank literal over an unsupported element type reports the
    -- method's obstruction; otherwise there was no rank literal to work on
    if let some rankApp := (← goal.getType).find? (·.isAppOfArity ``Matrix.rank 6) then
      if let some (_, _, _, R, _) ← matchRankLit? rankApp then
        if let some why ← bareissObstruction? R then
          throwError why
    throwError "eval_rank: no closed `Matrix.rank` literal found in the goal"
  Tactic.evalTactic (← `(tactic| try omega))
