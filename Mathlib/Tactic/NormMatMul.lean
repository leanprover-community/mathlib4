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
  have zα : Q(Zero $α) := ← synthInstanceQ q(Zero $α)
  have aα : Q(Add $α) := ← synthInstanceQ q(Add $α)
  have mα : Q(Mul $α) := ← synthInstanceQ q(Mul $α)
  let r := proveMul zα aα mα l m n rowsA rowsB
  let ctx ← readThe Simp.Context
  let cells ← r.rows.mapM (·.mapM fun a => do
    let s ← Mathlib.Meta.NormNum.deriveSimp ctx (useSimp := false) (e := a)
    have b : Q($α) := s.expr
    return (⟨a, b, ← s.getProof⟩ : (a : Q($α)) × (b : Q($α)) × Q($a = $b)))
  let ⟨_, _, hV⟩ := mkListCongr (α := q(List $α)) <| cells.map fun row => mkListCongr row
  let entries := cells.toArray.map fun row => row.toArray.map (·.2.1)
  let C := Matrix.mkLiteralQ (α := α) (m := l) (n := n) (.of fun i j => (entries[i]!)[j]!)
  let pf ← mkEqTrans
    (← mkEqSymm (← mkAppM ``ofLists_mul #[toExpr l, toExpr m, toExpr n, r.A, r.B]))
    (← mkCongrArg (← mkAppOptM ``ofLists #[α, none, toExpr l, toExpr n])
      (← mkEqTrans r.proof hV))
  -- `ofLists` on the row lists unfolds to the `!![…]` literals
  return .done { expr := C, proof? := some (mkExpectedPropHint pf q($e = $C)) }

end Mathlib.Tactic.Matrix

open Mathlib.Tactic.Matrix

simproc_decl norm_matmul ((_ * _ : Matrix (Fin _) (Fin _) _)) := fun e => do
  try normMatMulCore e
  catch ex =>
    trace[Tactic.norm_matmul] "{ex.toMessageData}"
    return .continue
