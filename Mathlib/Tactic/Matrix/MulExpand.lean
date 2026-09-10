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

`proveMul` rewrites `ListMatrix.mul l m n A B` for list literals `A` and `B` to the literal
whose entries are the sums of products of the entries, with the proof for other tactics to
consume in `MetaM`.

## Implementation notes

The entries are stated as sums of products by applying the unfolding equations of
`ListMatrix.dotProduct` one term at a time, instead of leaving the unfolding to the kernel, which
can trigger evaluation of arithmetic.
-/

public meta section

open Lean Meta Qq

namespace Mathlib.Tactic.Matrix

section

-- the classes are parameters so that every quotation references the one instance term the
-- caller synthesised, rather than rebuilding a projection path in every cell
variable {u : Level} {α : Q(Type u)} (zα : Q(Zero $α)) (aα : Q(Add $α)) (mα : Q(Mul $α))

/-- A dot product of two lists of entries, `ListMatrix.dotProduct n l₁ l₂ = result`, with its
proof. -/
structure DotProductEq where
  /-- The number of terms. -/
  n : Q(ℕ)
  /-- The first list. -/
  l₁ : Q(List $α)
  /-- The second list. -/
  l₂ : Q(List $α)
  /-- The right-hand side. -/
  result : Q($α)
  /-- The proof. -/
  proof : Q(ListMatrix.dotProduct $n $l₁ $l₂ = $result)

/-- The unfolding of the dot product of the entries `as` and `bs` to the fold
`a₀ * b₀ + (a₁ * b₁ + (… + 0))`, by the equations of `ListMatrix.dotProduct`; its `n` is the
successor tower `((0 + 1) + 1) + …` the equations build, one `+ 1` per term rather than a
numeral. -/
def mkDotProductChain : List Q($α) → List Q($α) → DotProductEq zα aα mα
  | a :: as, b :: bs =>
    let ⟨n, l₁, l₂, fold, h⟩ := mkDotProductChain as bs
    ⟨q($n + 1), q($a :: $l₁), q($b :: $l₂), q($a * $b + $fold),
      q(ListMatrix.dotProduct_succ_cons_cons $a $b $h)⟩
  | _, _ => ⟨q(0), q([]), q([]), q(0), q(ListMatrix.dotProduct_zero [] [])⟩

/-- The dot product of the `m` entries `as` and `bs`, `ListMatrix.dotProduct m l₁ l₂ = fold`, with
`m` a numeral and `fold` the sum of the products. -/
def proveDotProduct (m : ℕ) (as bs : List Q($α)) : DotProductEq zα aα mα :=
  let ⟨_, l₁, l₂, fold, h⟩ := mkDotProductChain zα aα mα as bs
  have mQ : Q(ℕ) := q($m)
  -- restate the chain's successor tower as the numeral `m`: Qq cannot check the two equal, the
  -- kernel does by literal arithmetic
  ⟨mQ, l₁, l₂, fold, mkExpectedPropHint h q(ListMatrix.dotProduct $mQ $l₁ $l₂ = $fold)⟩

end

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

/-- The expansion of the product `ListMatrix.mul l m n A B` of two list literals with the
associated proof term. The input matrices are put as fields of the structure to avoid
over-long dependent type signatures. -/
structure MulEq {u : Level} {α : Q(Type u)} (zα : Q(Zero $α)) (aα : Q(Add $α)) (mα : Q(Mul $α))
    (l m n : ℕ) where
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

/-- Rewrite `ListMatrix.mul l m n listA listB`, for `listA` the list literal of the `l` rows `A`
of `m` entries and `listB` that of the `m` rows `B` of `n` entries over `α`, to the literal whose
entries are the sums of products of the entries. -/
def proveMul {u : Level} {α : Q(Type u)} (zα : Q(Zero $α)) (aα : Q(Add $α)) (mα : Q(Mul $α))
    (l m n : ℕ) (A B : List (List Q($α))) : MulEq zα aα mα l m n :=
  -- transpose of B
  let Bt := letI : Zero Q($α) := ⟨q(0)⟩; ListMatrix.transpose n B
  let mulEntryEqs := A.map fun row => Bt.map fun col => proveDotProduct zα aα mα m row col
  let ⟨_, C, hC⟩ := mkListCongr (α := q(List $α)) <| mulEntryEqs.map fun row =>
    mkListCongr <| row.map fun d =>
      ⟨q(ListMatrix.dotProduct $(d.n) $(d.l₁) $(d.l₂)), d.result, d.proof⟩
  let listA := mkListLitQ (α := q(List $α)) (A.map mkListLitQ)
  let listB := mkListLitQ (α := q(List $α)) (B.map mkListLitQ)
  -- `hC` is stated on the dot products of the rows and columns, to which `ListMatrix.mul` on the
  -- literals unfolds, so the kernel settles the hint by reduction
  { A := listA,
    B := listB,
    rows := mulEntryEqs.map (·.map (·.result)),
    expr := C,
    proof := mkExpectedPropHint hC q(ListMatrix.mul $l $m $n $listA $listB = $C) }

end Mathlib.Tactic.Matrix
