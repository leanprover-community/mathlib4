/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.LinearAlgebra.Matrix.Echelon.Bareiss.Defs

/-!
# Reification engine for the Bareiss decomposition tactic (wip)

-/

public meta section

open Lean Meta Elab

namespace Mathlib.Tactic.Echelon

partial def vecLit (α : Expr) (entries : Array Expr) : MetaM Expr := do
  let mut acc ← mkAppOptM ``Matrix.vecEmpty #[some α]
  for e in entries.reverse do
    acc ← mkAppM ``Matrix.vecCons #[e, acc]
  return acc

def matrixLitExpr (R : Expr) (rows : Array (Array Expr)) : MetaM Expr := do
  let numRows := rows.size
  let numCols := if 0 < rows.size then rows[0]!.size else 0
  let finN ← mkAppM ``Fin #[mkNatLit numCols]
  let outer ← vecLit (← mkArrow finN R) (← rows.mapM (vecLit R))
  let finM ← mkAppM ``Fin #[mkNatLit numRows]
  -- `Matrix.of` is an `Equiv`, so apply it through `DFunLike.coe`.
  mkAppM ``DFunLike.coe #[← mkAppOptM ``Matrix.of #[some finM, some finN, some R], outer]

def pivotLitExpr (numCols : Nat) (idxs : Array Nat) : MetaM Expr := do
  let finN ← mkAppM ``Fin #[mkNatLit numCols]
  let elems ← idxs.mapM fun k => mkAppOptM ``OfNat.ofNat #[some finN, some (mkNatLit k), none]
  mkListLit finN elems.toList

partial def parseVec? (e : Expr) : Option (Array Expr) :=
  go #[] e
where
  go (acc : Array Expr) (e : Expr) : Option (Array Expr) :=
    match_expr e.consumeMData with
    | Matrix.vecEmpty _ => some acc
    | Matrix.vecCons _ _ head tail => go (acc.push head) tail
    | _ => none

partial def listLitLen (e : Expr) : Nat :=
  match_expr e.consumeMData with
  | List.cons _ _ tail => 1 + listLitLen tail
  | _ => 0

def parseMatrix (M : Expr) : MetaM (Array (Array Expr)) := do
  let mut e := M.consumeMData
  for _ in [0:8] do
    match_expr e with
    | DFunLike.coe _ _ _ _ f v =>
      match_expr f.consumeMData with
      | Matrix.of _ _ _ =>
        let some rows := parseVec? v | throwError "expected a matrix literal"
        return ← rows.mapM fun r => do
          let some entries := parseVec? r | throwError "expected a matrix literal"
          return entries
      | _ => pure ()
    | _ => pure ()
    match ← unfoldDefinition? e with
    | some e' => e := e'.consumeMData
    | none => break
  throwError "expected a matrix literal, got{indentExpr M}"

/- TODO: PLACEHOLDER -/
def produceBareiss (_entries : Array (Array Expr)) : MetaM (Expr × Expr × Expr) := do
  let R := mkConst ``Int
  let i (n : Int) : Expr := toExpr n
  let L ← matrixLitExpr R #[#[i 1, i 0], #[i (-3), i 1]]
  let σ ← mkAppM ``Equiv.refl #[← mkAppM ``Fin #[mkNatLit 2]]
  let pivot ← pivotLitExpr 2 #[0, 1]
  return (L, σ, pivot)

def reifyBareiss (M : Expr) : TermElabM Expr := do
  let (L, σ, pivot) ← produceBareiss (← parseMatrix M)
  let stx ← `((⟨$(← Term.exprToSyntax L), $(← Term.exprToSyntax σ), $(← Term.exprToSyntax pivot),
                by decide, by decide, by decide⟩ :
              Bareiss.Decomposition $(← Term.exprToSyntax M)))
  let e ← Term.elabTermEnsuringType stx none
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

end Mathlib.Tactic.Echelon

end
