/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.Data.Matrix.Reflection

/-!
# Simprocs for matrices

In this file we provide a simproc and a "rw proc" for transpose of explicit matrices.

Existing theorems are `Matrix.cons_transpose` and a simproc `Matrix.cons_val`, but this simproc
and rw proc aim to do it in one step to optimise the proof term and intermediate goal sizes.
-/

open Matrix
open Lean Expr Meta Simp Simproc Tactic Qq

namespace Qq

/-- Decompose a vector expression into a vector of expressions.

Partial inverse of `PiFin.mkLiteralQ` in `Mathlib/Data/Fin/VecNotation.lean`.

E.g. `q(![a, b, c])` becomes `![q(a), q(b), q(c)]`. -/
def piFinLit? {u : Level} {n : ℕ} {R : Q(Type u)} (e : Q(Fin $n → $R)) :
    MetaM (Option (Fin n → Q($R))) := do
  match n with
  | 0 =>
    let ~q(![]) := e | return .none
    return .some ![]
  | _+1 =>
    let ~q(vecCons $h $et) := e | return .none
    let .some t ← piFinLit? et | return .none
    return .some (vecCons h t)

/-- Decompose a "double vector" expression, i.e. `Fin m → Fin n → R`, into a double vector of
expressions.

Partial inverse of two applications of `PiFin.mkLiteralQ` in `Mathlib/Data/Fin/VecNotation.lean`.

E.g. `q(![![a, b], ![c, d]])` becomes `![![q(a), q(b)], ![q(c), q(d)]]`. -/
def piFinPiFinLit? {u : Level} {m n : ℕ} {R : Q(Type u)} (e : Q(Fin $m → Fin $n → $R)) :
    MetaM (Option (Fin m → Fin n → Q($R))) := do
  match m with
  | 0 =>
    let ~q(![]) := e | return .none
    return .some ![]
  | _+1 =>
    let ~q(vecCons $h $et) := e | return .none
    let .some h ← piFinLit? h | return .none
    let .some t ← piFinPiFinLit? et | return .none
    return .some (vecCons h t)

/-- Decompose a matrix expression into a matrix of expressions.

Partial inverse of `Matrix.mkLiteralQ` in `Mathlib/Data/Matrix/Notation.lean`.

E.g. `q(!![a, b; c, d])` becomes `!![q(a), q(b); q(c), q(d)]`. -/
def matrixLit? {u : Level} {m n : ℕ} {R : Q(Type u)} (eM : Q(Matrix (Fin $m) (Fin $n) $R)) :
    MetaM (Option (Matrix (Fin m) (Fin n) Q($R))) := do
  let ~q(of $eM) := eM | return .none
  let .some M ← piFinPiFinLit? eM | return .none
  return of M

/-- Converts `f a₀ a₁ a₂` to `fun a₀ a₁ a₂ ↦ f a₀ a₁ a₂`.

This assumes they are all explicit variables with the same type.

This does not substitute the variables with their de Bruijn indices. To do so, call
`Lean.Expr.abstract` on the result of this function. -/
def mkLambdas (names : Array Name) (type : Expr) (body : Expr) : Expr :=
  names.foldr (fun n b' ↦ .lam n type b' .default) body

namespace mkTranspose

/-! # Building custom transpose theorems

In this section we build theorems for the transpose of explicit matrices.

- `proof` is the proof of a theorem of the form `!![a, b, c; d, e, f]ᵀ = !![a, d; b, e; c, f]`,
  given a matrix of expressions.
- `thm` is the proof of the above theorem but with forall quantifiers on those variables.
-/

variable {u : Level} {α : Q(Type u)} {m n : ℕ}

/-- The left-hand side of the desired theorem, e.g. `!![a, b, c; d, e, f]ᵀ`. -/
def lhs (M : Matrix (Fin m) (Fin n) Q($α)) :
    Q(Matrix (Fin $n) (Fin $m) $α) :=
  q($(mkLiteralQ M)ᵀ)

/-- The right-hand side of the desired theorem, e.g. `!![a, d; b, e; c, f]`. -/
def rhs (M : Matrix (Fin m) (Fin n) Q($α)) :
    Q(Matrix (Fin $n) (Fin $m) $α) :=
  q($(mkLiteralQ Mᵀ))

/-- Given a matrix of expressions `M`, construct the proposition saying `q(M)ᵀ = q(Mᵀ)`. For
example, `!![a, b, c; d, e, f]ᵀ = !![a, d; b, e; c, f]`. -/
def prop (M : Matrix (Fin m) (Fin n) Q($α)) :
    Q(Prop) :=
  q($(lhs M) = $(rhs M))

/-- A partial proof that is defeq to the desired theorem, but whose inferred type will not be the
desired type yet. For example, the inferred type will be
`!![a, b, c; d, e, f]ᵀ = !![a, b, c; d, e, f]ᵀ.etaExpand`, and the right-hand side of this will be
defeq to `!![a, d; b, e; c, f]`. -/
def proof' (M : Matrix (Fin m) (Fin n) Q($α)) :
    Q($(lhs M) = $(lhs M).etaExpand) :=
  q((etaExpand_eq _).symm)

/-- Given a matrix of expressions, construct a proof of `q(M)ᵀ = q(Mᵀ)`. -/
def proof {u : Level} {α : Q(Type u)} {m n : ℕ} (M : Matrix (Fin m) (Fin n) Q($α)) :
    Q($(lhs M) = $(rhs M)) :=
  -- We want to output a term with an expected type, and in a monad one would typically use
  -- `Lean.Meta.mkExpectedTypeHint`, which actually outputs `@id expectedType e`, so we emulate
  -- this outside a monadic context by building the `@id` ourselves.
  .app q(@id.{0} $(prop M)) (proof' M)

/-- Prove a statement of the form
```lean
theorem Matrix.transpose₂₃ {α : Type*} (a₀₀ a₀₁ a₀₂ a₁₀ a₁₁ a₁₂ : α) :
    !![a₀₀, a₀₁, a₀₂; a₁₀, a₁₁, a₁₂]ᵀ = !![a₀₀, a₁₀; a₀₁, a₁₁; a₀₂, a₁₂] :=
  id (etaExpand_eq _).symm
```
-/
def thm (u : Level) (m n : Nat) : Q(Prop) :=
  have α : Q(Type u) := .fvar ⟨.anonymous⟩
  have nameE (i j : Nat) : Q($α) := .fvar ⟨.num (.num .anonymous i) j⟩
  have namesA : Array Name := .ofFn fun t : Fin (m * n) ↦ s!"r{t/n}c{t%n}".toName
  have argsA : Array Q($α) := .ofFn fun t : Fin (m * n) ↦ nameE (t/n) (t%n)
  have M : Matrix (Fin m) (Fin n) Q($α) := of fun i j ↦ nameE i j
  have pf' := proof M
  have pf_α := mkLambdas namesA q($α) (pf'.abstract argsA)
  .lam `α q(Type u) (pf_α.abstract #[α]) .implicit

end mkTranspose

end Qq

open Elab Tactic

/-- A custom theorem for reducing transpose of explicit matrices. For example, `transpose_of% 2 3`
is the theorem saying `!![a, b, c; d, e, f]ᵀ = !![a, d; b, e; c, f]`. Usage:

```lean
example : !![1, 2, 3; 4, 5, 6]ᵀ = !![1, 4; 2, 5; 3, 6] := by
  rw [transpose_of% 2 3]
``` -/
elab:max (name := transpose_tac_elab)
    "transpose_of% " mStx:num nStx:num : term => do
  let u ← Lean.Meta.mkFreshLevelMVar
  return mkTranspose.thm u mStx.getNat nStx.getNat

-- Here we use the convention that `e{name}` is the expression for `{name}`, e.g. `eMT` is the
-- expression corresponding to the transpose of the matrix `M`.
/-- A simproc for terms of the form `Matrix.transpose (Matrix.of _)`. Usage:

```lean
example : !![1, 2, 3; 4, 5, 6]ᵀ = !![1, 4; 2, 5; 3, 6] := by
  simp
```
-/
simproc matrix_transpose (Matrix.transpose (Matrix.of _)) := .ofQ fun u α eMT ↦ do
  let .succ _ := u | return .continue
  let ~q(@Matrix (Fin $en) (Fin $em) $R) := α | return .continue
  let ~q(transpose $eM) := eMT | return .continue
  let .some m := em.nat? | return .continue
  let .some n := en.nat? | return .continue
  let .some M ← matrixLit? (m := m) (n := n) (R := R) eM | return .continue
  have rhs : Q(Matrix (Fin $en) (Fin $em) $R) := mkTranspose.rhs M
  have pf : Q($eMT = ($eMT).etaExpand) := mkTranspose.proof' M
  have : $rhs =Q ($eMT).etaExpand := ⟨⟩
  return .visit <| .mk q($rhs) <| .some q($pf)

/-- Auxiliary tactic to generate the rw-proc `transpose_of`. -/
elab "transpose_tac_aux" : tactic => Lean.Elab.Tactic.liftMetaFinishingTactic fun mid ↦ do
  have h := mvar mid
  let ⟨0, ~q(($lhs : Matrix (Fin $em) (Fin $en) $α)ᵀ = $rhs), h⟩ := ← inferTypeQ h
    | throwError "Could not infer type for the transpose tactic"
  let .some m := em.nat?
    | throwError "Matrix is not of a known height"
  let .some n := en.nat?
    | throwError "Matrix is not of a known width"
  let .some M ← matrixLit? (m := m) (n := n) (R := α) lhs
    | throwError "Could not parse matrix from LHS"
  have new_rhs : Q(Matrix (Fin $en) (Fin $em) $α) := mkTranspose.rhs M
  commitIfNoEx do
    let .defEq _ := ← isDefEqQ q($rhs) q($new_rhs)
      | throwError "Could not assign RHS"
    h.mvarId!.assignIfDefEq (mkTranspose.proof M)

/-- A "magic" theorem to compute the transpose of explicit matrices. Usage:

```lean
example : !![1, 2, 3; 4, 5, 6]ᵀ = !![1, 4; 2, 5; 3, 6] := by
  rw [transpose_of]
```
-/
theorem transpose_of {α : Type*} {m n : ℕ} {M : Matrix (Fin m) (Fin n) α}
    {N : Matrix (Fin n) (Fin m) α} (h : Mᵀ = N := by transpose_tac_aux) :
  Mᵀ = N := h
