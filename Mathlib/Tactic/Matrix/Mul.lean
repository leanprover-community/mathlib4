/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Data.Matrix.ListMatrix
public import Mathlib.Tactic.Matrix.Parsing
public import Mathlib.Tactic.NormNum.Core

/-!
# `norm_matmul`: products of matrix literals

This module defines the `norm_matmul` simproc, which rewrites a product of matrix literals to
the literal of the product through `Matrix.ofLists_mul`, with the entries computed by
`norm_num`.
-/

public meta section

open Lean Meta Qq

initialize registerTraceClass `Tactic.normMatMul

namespace Mathlib.Tactic.Matrix

/-- A finisher rewrites an expression to a normal form: a scalar to its value, or a
proposition to `True` or `False`. -/
abbrev Finisher := Expr → MetaM Simp.Result

/-- The unfolding of a dot product of literals `l₁ = [a₀, …]`, `l₂ = [b₀, …]` to the fold
`a₀ * b₀ + (a₁ * b₁ + (… + 0))`, proved by the equations of `List.dotProduct`. -/
structure DotProductChain {u : Level} (α : Q(Type u)) (_z : Q(Zero $α)) (_add : Q(Add $α))
    (_mul : Q(Mul $α)) where
  /-- The length, as the equations leave it: `(… + 1) + 1`. -/
  n : Q(ℕ)
  /-- The first list. -/
  l₁ : Q(List $α)
  /-- The second list. -/
  l₂ : Q(List $α)
  /-- The fold. -/
  fold : Q($α)
  /-- The unfolding. -/
  proof : Q(List.dotProduct $n $l₁ $l₂ = $fold)

/-- Build the `DotProductChain` of the entries `as` and `bs`. -/
def mkDotProductChain {u : Level} {α : Q(Type u)} (_z : Q(Zero $α)) (_add : Q(Add $α))
    (_mul : Q(Mul $α)) : List Q($α) → List Q($α) → DotProductChain α _z _add _mul
  | a :: as, b :: bs =>
    -- the classes are taken as arguments so that every quotation references the one instance
    -- term the caller synthesised, rather than rebuilding a projection path in every cell
    let ⟨n, l₁, l₂, fold, h⟩ := mkDotProductChain _z _add _mul as bs
    ⟨q($n + 1), q($a :: $l₁), q($b :: $l₂), q($a * $b + $fold),
      q((List.dotProduct_succ_cons_cons $n $a $b $l₁ $l₂).trans
        (congrArg (fun x => $a * $b + x) $h))⟩
  | _, _ => ⟨q(0), q([]), q([]), q(0), q(List.dotProduct_zero [] [])⟩

/-- Prove `[a₀, …] = [b₀, …]` from proofs of `aᵢ = bᵢ`. -/
def mkListCongr (α : Expr) (hs : Array Expr) : MetaM Expr := do
  let u ← getDecLevel α
  hs.foldrM (init := ← mkEqRefl (mkApp (mkConst ``List.nil [u]) α)) fun h acc => do
    mkCongr (← mkCongrArg (mkApp (mkConst ``List.cons [u]) α) h) acc

/-- Prove `e = C`, where `e` is the product of the matrix literals with rows `rowsA` and
`rowsB` over `α`, and `C` is the literal of the product with entries normalized by `finish`. -/
def proveMul {u : Level} (finish : Finisher) (e : Expr) (l m n : ℕ) (α : Q(Type u))
    (rowsA rowsB : Array (Array Expr)) : MetaM Simp.Result := do
  let _inst ← synthInstanceQ q(NonUnitalNonAssocSemiring $α)
  -- derived from the semiring rather than synthesised afresh, so that the cells carry the
  -- instance paths `Matrix.ofLists_mul` instantiates `ListMatrix.mul` with
  let _z : Q(Zero $α) := q(MulZeroClass.toZero)
  let _add : Q(Add $α) := q(Distrib.toAdd)
  let _mul : Q(Mul $α) := q(Distrib.toMul)
  have mQ : Q(ℕ) := mkRawNatLit m
  let cols : Array (Array Expr) :=
    Array.ofFn (n := n) fun j => Array.ofFn (n := m) fun i => (rowsB[i]!)[j]!
  let results ← Array.ofFnM (n := l) fun i => Array.ofFnM (n := n) fun j => do
    let ⟨_, l₁, l₂, fold, h⟩ := mkDotProductChain _z _add _mul rowsA[i]!.toList cols[j]!.toList
    -- the cell of `ListMatrix.mul`, with the length as the literal `m`
    have dot : Q($α) := q(List.dotProduct $mQ $l₁ $l₂)
    have hDot : Q($dot = $fold) := ← mkExpectedTypeHint h q($dot = $fold)
    let r ← finish fold
    have v : Q($α) := r.expr
    have hFold : Q($fold = $v) := ← r.getProof
    return (v, q(($hDot).trans $hFold))
  let entries := results.map (·.map (·.1))
  -- a cell's proof is stated on `List.dotProduct`, so the product's unfolding is compared to
  -- it by the kernel head to head; stated on the fold, the kernel would unfold `+` first and
  -- then only evaluation of the arithmetic could close the comparison
  let hAll ← mkListCongr q(List $α) (← results.mapM fun row => mkListCongr α (row.map (·.2)))
  let mkLists (rows : Array (Array Expr)) : MetaM Q(List (List $α)) := do
    mkListLit q(List $α) (← rows.toList.mapM (mkListLit α ·.toList))
  have A : Q(List (List $α)) := ← mkLists rowsA
  have B : Q(List (List $α)) := ← mkLists rowsB
  let C : Q(Matrix (Fin $l) (Fin $n) $α) :=
    Matrix.mkLiteralQ (α := α) (m := l) (n := n) (.of fun i j => (entries[i]!)[j]!)
  let hmul := q((Matrix.ofLists_mul $l $m $n $A $B).symm)
  let hC ← mkCongrArg q(Matrix.ofLists (α := $α) $l $n) hAll
  let pf ← mkEqTrans hmul hC
  -- `pf` is stated on `Matrix.ofLists` forms; the hint to `e = C` holds because `ofLists` on
  -- a row-list literal unfolds to exactly the `Matrix.of`/`vecCons` term of the `!![…]`
  -- literal, so the kernel settles it by reduction
  return { expr := C, proof? := some (← mkExpectedTypeHint pf (← mkEq e C)) }

/-- Core of the `norm_matmul` simproc with the given finisher. The factors are simplified first,
so that a product of products is evaluated inside-out before the simp lemmas on `vecCons`
products apply. -/
def normMatMulCore (finish : Finisher) : Simp.Simproc := fun e => do
  let_expr HMul.hMul _ _ _ _ A B := e | return .continue
  let rA ← Simp.simp A
  let rB ← Simp.simp B
  let some (l, m, R, rowsA) ← matchMatrixLit? rA.expr
    | trace[Tactic.normMatMul] "not a closed matrix literal{indentExpr rA.expr}"
      return .continue
  let some (_, n, _, rowsB) ← matchMatrixLit? rB.expr
    | trace[Tactic.normMatMul] "not a closed matrix literal{indentExpr rB.expr}"
      return .continue
  let rAB ← Simp.mkCongr (← Simp.mkCongr { expr := e.appFn!.appFn! } rA) rB
  let u ← getDecLevel R
  return .visit (← rAB.mkEqTrans (← proveMul (u := u) finish rAB.expr l m n R rowsA rowsB))

end Mathlib.Tactic.Matrix

open Mathlib.Tactic.Matrix

/-- The `norm_matmul` simproc rewrites a product of matrix literals with non-symbolic entries
to the literal of the product, with the entries computed by `norm_num`. Use it as
`simp [↓ norm_matmul]`: as a pre-procedure it takes precedence over the simp lemmas unfolding
products of `vecCons` rows, and `norm_num` ignores simprocs given as arguments. Terms that it
cannot evaluate are skipped, and can be viewed by using `set_option trace.Tactic.normMatMul true`.
-/
simproc_decl norm_matmul ((_ * _ : Matrix (Fin _) (Fin _) _)) := fun e => do
  try normMatMulCore (Mathlib.Meta.NormNum.eval ·) e
  catch ex =>
    trace[Tactic.normMatMul] "{ex.toMessageData}"
    return .continue
