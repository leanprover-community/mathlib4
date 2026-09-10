/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Tactic.Matrix.MulExpand
public import Mathlib.Tactic.Matrix.OfLists  -- shake: keep (referenced by name)
public import Mathlib.Tactic.Matrix.Parsing
public import Mathlib.Tactic.NormNum.Basic  -- shake: keep (`+`/`*` extensions run by `norm_matmul`)

/-!
# The `norm_matmul` simproc

`norm_matmul` rewrites a product of matrix literals to the literal of the product, with the
entries computed by `norm_num`.

## Implementation notes

The product is rewritten on the row lists of the factors, and the equation between the `!![…]`
literals follows from the one between their `ofLists` forms by a single definitional hint.

Note that the simp lemmas unfolding `vecCons` compete with this simproc due to how `!![]` is
currently elaborated, so the simproc should be used by `simp only`.
-/

public meta section

open Lean Meta Qq

initialize registerTraceClass `Tactic.norm_matmul

namespace Mathlib.Tactic.Matrix

/-- The rows of a list literal `[[a₀₀, a₀₁, …], …]`. -/
def rowsOfLit? (e : Expr) : Option (List (List Expr)) := do
  let (_, rows) ← e.listLit?
  rows.mapM fun row => (·.2) <$> row.listLit?

/-- Core of the `norm_matmul` simproc. -/
def normMatMulCore : Simp.Simproc := fun e => do
  let_expr HMul.hMul _ _ _ _ A B := e | return .continue
  let some (l, m, R, rowsA) ← matchMatrixLit? A
    | trace[Tactic.norm_matmul] "not a closed matrix literal{indentExpr A}"
      return .continue
  let some (_, n, _, rowsB) ← matchMatrixLit? B
    | trace[Tactic.norm_matmul] "not a closed matrix literal{indentExpr B}"
      return .continue
  let u ← getDecLevel R
  have α : Q(Type u) := R
  have e : Q(Matrix (Fin $l) (Fin $n) $α) := e
  let rowsA : List (List Q($α)) := rowsA.toList.map Array.toList
  let rowsB : List (List Q($α)) := rowsB.toList.map Array.toList
  have zα : Q(Zero $α) := ← synthInstanceQ q(Zero $α)
  have aα : Q(Add $α) := ← synthInstanceQ q(Add $α)
  have mα : Q(Mul $α) := ← synthInstanceQ q(Mul $α)
  let r := proveMul zα aα mα l m n rowsA rowsB
  let s ← Mathlib.Meta.NormNum.deriveSimp (← readThe Simp.Context) false r.expr
  let some rows := rowsOfLit? s.expr
    | throwError "expected a list literal of rows{indentExpr s.expr}"
  let rows := rows.toArray.map List.toArray
  let C := Matrix.mkLiteralQ (α := α) (m := l) (n := n) (.of fun i j => (rows[i]!)[j]!)
  let pf ← mkEqTrans
    (← mkEqSymm (← mkAppM ``ofLists_mul #[toExpr l, toExpr m, toExpr n, r.A, r.B]))
    (← mkCongrArg (← mkAppOptM ``ofLists #[α, none, toExpr l, toExpr n])
      (← mkEqTrans r.proof (← s.getProof)))
  -- `pf` is stated on `ofLists` forms; the hint holds because `ofLists` on a row-list literal
  -- unfolds to exactly the `Matrix.of`/`vecCons` term of the `!![…]` literal, so the kernel
  -- settles it by reduction at both ends
  return .done { expr := C, proof? := some (mkExpectedPropHint pf q($e = $C)) }

end Mathlib.Tactic.Matrix

open Mathlib.Tactic.Matrix

/-- The `norm_matmul` simproc rewrites a product of matrix literals with non-symbolic entries
to the literal of the product, with the entries computed by `norm_num`. Terms that it cannot
evaluate are skipped, and can be viewed by using `set_option trace.Tactic.norm_matmul true`. -/
simproc_decl norm_matmul ((_ * _ : Matrix (Fin _) (Fin _) _)) := fun e => do
  try normMatMulCore e
  catch ex =>
    trace[Tactic.norm_matmul] "{ex.toMessageData}"
    return .continue
