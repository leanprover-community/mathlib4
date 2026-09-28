/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Batteries.Logic  -- shake: keep (Qq dependency)
public import Mathlib.Init
public import Qq

public meta import Mathlib.Tactic.Matrix.ListMatrix
public meta import Mathlib.Util.Qq

/-!
# Expansion of products of list matrices

`proveMul` rewrites `ListMatrix.mul l m n A B` for list literals `A` and `B` to a literal
whose entries are the sums of products of the entries, with the proof constructed manually
instead of asking the kernel to perform reduction.

The entries are obtained by unfolding equations of `ListMatrix.dotProduct` one term at a time,
instead of leaving the unfolding to the kernel, which can trigger evaluation of arithmetic
prematurely.
-/

public meta section

open Lean Meta Qq

namespace Mathlib.Tactic.Matrix

-- The classes are parameters so that every quotation references the one instance term the
-- caller synthesised, rather than rebuilding a projection path in every cell.
variable {u : Level} {α : Q(Type u)} (zα : Q(Zero $α)) (aα : Q(Add $α)) (mα : Q(Mul $α))

/-- Construct a proof term that `[a₀, …] = [b₀, …]` in `List α` from proofs of `aᵢ = bᵢ`.
`MVarId.congrN` also works, but is much slower to elaborate. -/
def mkListCongr :
    List ((a : Q($α)) × (b : Q($α)) × Q($a = $b)) →
      (l₁ : Q(List $α)) × (l₂ : Q(List $α)) × Q($l₁ = $l₂)
  | [] => ⟨q([]), q([]), q(rfl)⟩
  | ⟨a, b, h⟩ :: es =>
    let ⟨l₁, l₂, hl⟩ := mkListCongr es
    ⟨q($a :: $l₁), q($b :: $l₂), q(congrArg₂ List.cons $h $hl)⟩

/-- A dot product of two lists of entries, `ListMatrix.dotProduct n l₁ l₂ = expr`, with its
proof. -/
structure DotProductEq where
  /-- The number of terms. -/
  n : Q(Nat)
  /-- The first list. -/
  l₁ : Q(List $α)
  /-- The second list. -/
  l₂ : Q(List $α)
  /-- The right-hand side. -/
  expr : Q($α)
  /-- The proof. -/
  proof : Q(ListMatrix.dotProduct $n $l₁ $l₂ = $expr)

/-- The dot product of the first `m` entries of the list literals `l₁` and `l₂`,
`ListMatrix.dotProduct m l₁ l₂ = fold`, with `m` a numeral and `fold` the sum of the products
`a₀ * b₀ + (a₁ * b₁ + (… + 0))`, unfolded by the equations of `ListMatrix.dotProduct`.
The function takes the pre-built `Expr` for list literals instead of taking the list of entry
literals and build it here, to avoid reconstructing the expressions multiple times. -/
def proveDotProduct (m : Nat) (l₁ l₂ : Q(List $α)) : DotProductEq zα aα mα :=
  let ⟨_, _, _, fold, h⟩ := go m l₁ l₂
  let mQ : Q(Nat) := q($m)
  ⟨mQ, l₁, l₂, fold, mkExpectedPropHint h q(ListMatrix.dotProduct $mQ $l₁ $l₂ = $fold)⟩
where
  /-- The chain of the equations, whose `n` is the successor tower `((0 + 1) + 1) + …` they
  build, one `+ 1` per term rather than a numeral. -/
  go : Nat → Q(List $α) → Q(List $α) → DotProductEq zα aα mα
    | 0, l₁, l₂ => ⟨q(0), l₁, l₂, q(0), q(ListMatrix.dotProduct_zero $l₁ $l₂)⟩
    | n + 1, l₁, l₂ =>
      -- avoid using the ~q() match here as that is almost 10x slower
      match_expr l₁ with
      | List.cons _ a l₁' =>
        match_expr l₂ with
        | List.cons _ b l₂' =>
          let a : Q($α) := a
          let b : Q($α) := b
          let l₁' : Q(List $α) := l₁'
          let l₂' : Q(List $α) := l₂'
          let ⟨nQ, _, _, fold, h⟩ := go n l₁' l₂'
          let nQ' : Q(Nat) := q($nQ + 1)
          let expr : Q($α) := q($a * $b + $fold)
          -- Qq cannot see the relationship between the matched arguments here since we avoid
          -- using Qq's matching, so an `Expr` annotation is used to bypass the check.
          let pf : Q(ListMatrix.dotProduct $nQ' $l₁ $l₂ = $expr) :=
            (q(ListMatrix.dotProduct_add_one_cons_cons $a $b $h) : Expr)
          ⟨nQ', l₁, l₂, expr, pf⟩
        | _ => ⟨q(0), l₁, l₂, q(0), q(ListMatrix.dotProduct_zero $l₁ $l₂)⟩
      | _ => ⟨q(0), l₁, l₂, q(0), q(ListMatrix.dotProduct_zero $l₁ $l₂)⟩

/-- The expansion of the product `ListMatrix.mul l m n A B` of two list literals with the
associated proof term. The input matrices are put as fields of the structure to avoid
over-long dependent type signatures downstream. -/
structure MulEq (l m n : Nat) where
  /-- The list literal of the first factor. -/
  A : Q(List (List $α))
  /-- The list literal of the second factor. -/
  B : Q(List (List $α))
  /-- The rows of the product, each entry the sum of the products of the entries. -/
  rows : List (List Q($α))
  /-- The list literal of `rows`. -/
  expr : Q(List (List $α))
  /-- The proof. -/
  proof : Q(ListMatrix.mul $l $m $n $A $B = $expr)

/-- Rewrite `ListMatrix.mul l m n A B` to the literal whose entries are the sums of products of
the entries.
`listA`/`listB` are the rows of the `l × m` and `m × n` matrix respectively.
The rows are not checked against `l`, `m` and `n`. -/
def proveMul (l m n : Nat) (listA listB : List (List Q($α))) : MulEq zα aα mα l m n :=
  let Bt := let : Zero Q($α) := ⟨default⟩; ListMatrix.transpose n listB
  -- Each row and column literal is built once and named by every cell that uses it, and `A` is
  -- the literal of the row literals, so the kernel meets one object per row and per column.
  let rowLits : List Q(List $α) := listA.map mkListLitQ
  let colLits : List Q(List $α) := Bt.map mkListLitQ
  let mulEntryEqs := rowLits.map fun row => colLits.map fun col =>
    proveDotProduct zα aα mα m row col
  let ⟨_, C, hC⟩ := mkListCongr (α := q(List $α)) <| mulEntryEqs.map fun row =>
    mkListCongr <| row.map fun d =>
      ⟨q(ListMatrix.dotProduct $(d.n) $(d.l₁) $(d.l₂)), d.expr, d.proof⟩
  let A := mkListLitQ (α := q(List $α)) rowLits
  let B := mkListLitQ (α := q(List $α)) (listB.map mkListLitQ)
  { A, B,
    rows := mulEntryEqs.map (·.map (·.expr)),
    expr := C,
    proof := mkExpectedPropHint hC q(ListMatrix.mul $l $m $n $A $B = $C) }

end Mathlib.Tactic.Matrix
