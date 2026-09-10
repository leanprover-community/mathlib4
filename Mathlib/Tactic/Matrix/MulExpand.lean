/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Batteries.Logic  -- shake: keep (Qq dependency)
public import Mathlib.Util.Qq

public meta import Mathlib.Tactic.Matrix.ListMatrix

/-!
# Expansion of products of list matrices

`proveMul` rewrites `ListMatrix.mul l m n A B` for list literals `A` and `B` to the a literal
whose entries are the sums of products of the entries, with the proof constructed manually
instead of asking kernel to perform reduction.

The entries are obtained by unfolding equations of `ListMatrix.dotProduct` one term at a time,
instead of leaving the unfolding to the kernel, which can trigger evaluation of arithmetic
prematurely.
-/

public meta section

open Lean Meta Qq

namespace Mathlib.Tactic.Matrix

/-- Construct a proof term that `[a₀, …] = [b₀, …]` in `List α` from proofs of `aᵢ = bᵢ`.
`MVarId.congrN` also works, but is much slower to elaborate. -/
def mkListCongr {u : Level} {α : Q(Type u)} :
    List ((a : Q($α)) × (b : Q($α)) × Q($a = $b)) →
      (l₁ : Q(List $α)) × (l₂ : Q(List $α)) × Q($l₁ = $l₂)
  | [] => ⟨q([]), q([]), q(rfl)⟩
  | ⟨a, b, h⟩ :: es =>
    let ⟨l₁, l₂, hl⟩ := mkListCongr es
    ⟨q($a :: $l₁), q($b :: $l₂), q(congrArg₂ List.cons $h $hl)⟩

/-- The list literal `[a₀, …]` of the entries `as`. -/
def mkListLitQ {u : Level} {α : Q(Type u)} : List Q($α) → Q(List $α)
  | [] => q([])
  | a :: as => q($a :: $(mkListLitQ as))

section

-- the classes are parameters so that every quotation references the one instance term the
-- caller synthesised, rather than rebuilding a projection path in every cell
variable {u : Level} {α : Q(Type u)} (zα : Q(Zero $α)) (aα : Q(Add $α)) (mα : Q(Mul $α))

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

/-- The dot product of the `m` entries `as` and `bs`, `ListMatrix.dotProduct m l₁ l₂ = fold`, with
`m` a numeral and `fold` the sum of the products `a₀ * b₀ + (a₁ * b₁ + (… + 0))`, unfolded by
the equations of `ListMatrix.dotProduct`. -/
def proveDotProduct (m : Nat) (as bs : List Q($α)) : DotProductEq zα aα mα :=
  let ⟨_, l₁, l₂, fold, h⟩ := go as bs
  have mQ : Q(Nat) := q($m)
  ⟨mQ, l₁, l₂, fold, mkExpectedPropHint h q(ListMatrix.dotProduct $mQ $l₁ $l₂ = $fold)⟩
where
  /-- The chain of the equations, whose `n` is the successor tower `((0 + 1) + 1) + …` they
  build, one `+ 1` per term rather than a numeral. -/
  go : List Q($α) → List Q($α) → DotProductEq zα aα mα
    | a :: as, b :: bs =>
      let ⟨n, l₁, l₂, fold, h⟩ := go as bs
      ⟨q($n + 1), q($a :: $l₁), q($b :: $l₂), q($a * $b + $fold),
        q(ListMatrix.dotProduct_succ_cons_cons $a $b $h)⟩
    | _, _ => ⟨q(0), q([]), q([]), q(0), q(ListMatrix.dotProduct_zero [] [])⟩

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
  /-- The list literal of `rows` as built by `mkListLitQ`. -/
  expr : Q(List (List $α))
  /-- The proof. -/
  proof : Q(ListMatrix.mul $l $m $n $A $B = $expr)

/-- Rewrite `ListMatrix.mul l m n A B`, for `A` the list literal of the `l` rows `listA` of `m`
entries and `B` that of the `m` rows `listB` of `n` entries over `α`, to the literal whose entries
are the sums of products of the entries. The rows are not checked against `l`, `m` and `n`. -/
def proveMul (l m n : Nat) (listA listB : List (List Q($α))) : MulEq zα aα mα l m n :=
  let Bt := letI : Zero Q($α) := ⟨q(0)⟩; ListMatrix.transpose n listB
  let mulEntryEqs := listA.map fun row => Bt.map fun col => proveDotProduct zα aα mα m row col
  let ⟨_, C, hC⟩ := mkListCongr (α := q(List $α)) <| mulEntryEqs.map fun row =>
    mkListCongr <| row.map fun d =>
      ⟨q(ListMatrix.dotProduct $(d.n) $(d.l₁) $(d.l₂)), d.expr, d.proof⟩
  let A := mkListLitQ (α := q(List $α)) (listA.map mkListLitQ)
  let B := mkListLitQ (α := q(List $α)) (listB.map mkListLitQ)
  { A, B,
    rows := mulEntryEqs.map (·.map (·.expr)),
    expr := C,
    proof := mkExpectedPropHint hC q(ListMatrix.mul $l $m $n $A $B = $C) }

end

end Mathlib.Tactic.Matrix
