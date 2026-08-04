/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public meta import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Parsing matrix literals

Parsers matching `!![…]` matrix literal expressions into their dimensions, element type,
and entry expressions, for tactics evaluating functions of a concrete matrix.
-/

public meta section

open Lean Meta

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

end Mathlib.Tactic.Echelon
