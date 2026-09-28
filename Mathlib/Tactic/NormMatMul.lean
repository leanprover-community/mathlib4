/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Tactic.Matrix.MulExpand
public import Mathlib.Tactic.Matrix.OfLists
public import Mathlib.Tactic.Matrix.Parsing
public import Mathlib.Tactic.NormNum.Basic  -- shake: keep (`+`/`*` extensions run by `norm_matmul`)
public meta import Mathlib.Tactic.Matrix.MulExpand

/-!
# The `norm_matmul` simproc

`norm_matmul` rewrites a product of matrix literals to the literal of the product, with the
entries normalised by `norm_num` if possible.

## Implementation notes

The product is rewritten on the row lists of the factors, and the equation between the `!![…]`
literals follows from the one between their `ofLists` forms by a single definitional hint.

Note that there are simp lemmas rewriting a product of `vecCons`, which compete with this
simproc due to how `!![]` is currently elaborated, so the simproc should be used by
`simp only`.
-/

public meta section

open Lean Meta Qq

initialize registerTraceClass `Tactic.norm_matmul

namespace Mathlib.Tactic.Matrix

/-- Core of the `norm_matmul` simproc. -/
def normMatMulCore : Simp.Simproc := fun e => do
  let_expr HMul.hMul _ _ _ _ A B := e | return .continue
  let some (l, m, R, rowsA) ← matchMatrixLit? A (closed := false)
    | trace[Tactic.norm_matmul] "not a matrix literal{indentExpr A}"
      return .continue
  -- use the `m` and `R` from parsing `A` above
  let some (_, n, _, rowsB) ← matchMatrixLit? B (closed := false)
    | trace[Tactic.norm_matmul] "not a matrix literal{indentExpr B}"
      return .continue
  let u ← getDecLevel R
  have α : Q(Type u) := R
  have e : Q(Matrix (Fin $l) (Fin $n) $α) := e
  let rowsA : List (List Q($α)) := rowsA.toList.map Array.toList
  let rowsB : List (List Q($α)) := rowsB.toList.map Array.toList
  let zα : Q(Zero $α) ← synthInstanceQ q(Zero $α)
  let aα : Q(Add $α) ← synthInstanceQ q(Add $α)
  let mα : Q(Mul $α) ← synthInstanceQ q(Mul $α)
  let r := proveMul zα aα mα l m n rowsA rowsB
  let rows := (r.rows.map List.toArray).toArray
  have C : Q(Matrix (Fin $l) (Fin $n) $α) :=
    Matrix.mkLiteralQ (α := α) (m := l) (n := n) (.of fun i j => (rows[i]!)[j]!)
  have pf : Q($e = $C) := mkExpectedPropHint (← mkAppM ``ofLists_mul #[r.proof]) q($e = $C)
  let res ← Mathlib.Meta.NormNum.deriveSimp (← readThe Simp.Context) (useSimp := false) (e := C)
  return .done { expr := res.expr, proof? := some (← mkEqTrans pf (← res.getProof)) }

end Mathlib.Tactic.Matrix

open Mathlib.Tactic.Matrix

/-- Rewrite a product of matrix literals to the literal of the product, with the entries
normalised by `norm_num` if possible. -/
simproc_decl norm_matmul ((_ * _ : Matrix (Fin _) (Fin _) _)) := normMatMulCore
