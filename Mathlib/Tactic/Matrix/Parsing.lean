/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public meta import Mathlib.LinearAlgebra.Matrix.Notation -- shake: keep (!![] elaboration)
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Attr
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Tactic.Bound.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.SetLike

/-!
# Parsing matrix literals

Parsers matching `!![…]` matrix literal expressions into their dimensions, element type,
and entry expressions, for tactics evaluating functions of a concrete matrix.

TODO: `!![…]` elaborates to `Matrix.of` applied to `Matrix.vecCons` chains, which is the shape
matched here. Once it elaborates through `Matrix.ofArray` instead, adapt this parser, or remove
it if the array form can be read directly.

## Main definitions

- `matchMatrixLit?`: match a matrix literal, closed by default.
-/

public meta section

open Lean Meta

namespace Mathlib.Tactic.Matrix

/-- Match a `Fin`-indexed matrix literal: its dimensions, element type, and rows of entries;
with `closed`, only a literal without free variables or metavariables. -/
def matchMatrixLit? (A : Expr) (closed := true) :
    MetaM (Option (Nat × Nat × Expr × Array (Array Expr))) := do
  -- a literal with free variables (hypothesis- or let-bound) or metavariables is not evaluable
  -- by a tactic computing with its entries; unfold or substitute such variables before calling it
  if closed && (A.hasFVar || A.hasMVar) then return none
  let_expr Matrix finM finN R := ← inferType A | return none
  let_expr Fin mE := finM | return none
  let_expr Fin nE := finN | return none
  let some m ← getNatValue? mE | return none
  let some n ← getNatValue? nE | return none
  let_expr DFunLike.coe _ _ _ _ f v := A | return none
  let_expr Matrix.of _ _ _ := f | return none
  let (rows, _, _) ← Matrix.matchVecConsPrefix mE v
  unless rows.length == m do return none
  let entries ← rows.toArray.mapM fun row => do
    let (es, _, _) ← Matrix.matchVecConsPrefix nE row
    return es.toArray
  unless entries.all (·.size == n) do return none
  return some (m, n, R, entries)

end Mathlib.Tactic.Matrix
