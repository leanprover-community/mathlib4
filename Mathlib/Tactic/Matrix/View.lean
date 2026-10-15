/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Tactic.Matrix.OfLists  -- shake: keep (Qq dependency)
public import Mathlib.Tactic.Matrix.Parsing
public import Mathlib.Util.Qq

/-!
# Views of matrix terms

`MatrixView` is an alternative inductive type of matrices, whose constructors build a matrix from
the rows of a list literal or from a function of its indices. `MatrixView.toMatrix` interprets a
view as a `Matrix` term, and `MatrixView.proof` produces the `rfl` proof term at the right type.
`MatrixView.parse?` parses a view from a given `Matrix` expression.
-/

public meta section

open Lean Meta Qq

namespace Mathlib.Tactic.Matrix

/-- An alternative construction of the matrix `M`. For each constructor, `toMatrix` builds from its
source an `m × n` matrix defeq to `M`. The proof term is omitted from this type (so `M` is unused
in it) to avoid asking Qq to resolve dependent types. -/
inductive MatrixView {u : Level} {α : Q(Type u)} (m n : Nat)
    (M : Q(Matrix (Fin $m) (Fin $n) $α)) where
  /-- The matrix built by `ofLists` from the list literal `lit`. -/
  | literal (lit : Q(List (List $α)))
  /-- The matrix built by `Matrix.of` from the function `f`. -/
  | functional (f : Q(Fin $m → Fin $n → $α))

/-- Interpret a `view` as an `m × n` matrix. The body is exposed so that a consumer's
quotations see `toMatrix` of a constructor reduce to its matrix. -/
@[expose] def MatrixView.toMatrix {u : Level} {α : Q(Type u)} {m n : Nat}
    {M : Q(Matrix (Fin $m) (Fin $n) $α)} (zα : Q(Zero $α)) (view : MatrixView m n M) :
    Q(Matrix (Fin $m) (Fin $n) $α) :=
  match view with
  | .literal lit => q(ofLists $m $n $lit)
  | .functional f => q(Matrix.of $f)

/-- The `rfl` proof of `M = view.toMatrix zα` as a type hint that the kernel checks. -/
def MatrixView.proof {u : Level} {α : Q(Type u)} {m n : Nat} {M : Q(Matrix (Fin $m) (Fin $n) $α)}
    (zα : Q(Zero $α)) (view : MatrixView m n M) : Q($M = $(view.toMatrix zα)) :=
  mkExpectedPropHint q(Eq.refl $M) q($M = $(view.toMatrix zα))

/-- The view of `M` when its index types are `Fin m` and `Fin n` for numerals `m` and `n`, with `M`
restated at those types, or `none` otherwise. It is the literal view when `M` is a `!![…]` literal,
and the functional view of `M` otherwise. With `closed` (the default), only a literal without free
variables or metavariables gets the literal view. -/
def MatrixView.parse? {u : Level} {α : Q(Type u)} {finM finN : Q(Type)}
    (M : Q(Matrix $finM $finN $α)) (closed : Bool := true) :
    MetaM (Option ((m n : Nat) × (M' : Q(Matrix (Fin $m) (Fin $n) $α)) × MatrixView m n M')) := do
  let_expr Fin mE := finM | return none
  let_expr Fin nE := finN | return none
  let (some m, some n) := (← getNatValue? mE, ← getNatValue? nE) | return none
  let M : Q(Matrix (Fin $m) (Fin $n) $α) := M
  let some (_, _, _, entries) ← matchMatrixLit? M closed
    | let f : Q(Fin $m → Fin $n → $α) := M
      return some ⟨m, n, M, .functional f⟩
  let rows : List (List Q($α)) := entries.toList.map Array.toList
  return some ⟨m, n, M, .literal (mkListLitQ (α := q(List $α)) (rows.map mkListLitQ))⟩

end Mathlib.Tactic.Matrix
