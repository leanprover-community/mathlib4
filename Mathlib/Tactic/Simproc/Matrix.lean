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
open Lean Meta Simp Simproc Tactic Qq

attribute [-simp] cons_transpose

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

/-- Given a matrix of expressions `M`, construct the proposition saying `q(M)ᵀ = q(Mᵀ)`. -/
def mkTransposeProp {u : Level} {α : Q(Type u)} {m n : ℕ} (M : Matrix (Fin m) (Fin n) Q($α)) :
    Q(Prop) :=
  q($(mkLiteralQ M)ᵀ = $(mkLiteralQ Mᵀ))

/-- Given a matrix of expressions, construct a proof of `q(M)ᵀ = q(Mᵀ)`. -/
def mkTransposeProof {u : Level} {α : Q(Type u)} {m n : ℕ} (M : Matrix (Fin m) (Fin n) Q($α)) :
    Quoted (mkTransposeProp M) :=
  -- we want `$lhs = $rhs`, but our proof is `pf' : $lhs = $rhs'`, where we know that `$rhs'` will
  -- be defeq to `$rhs`, therefore we construct the proof `@id ($lhs = $rhs) pf' : $lhs = $rhs`.
  -- This proof cannot be `q()` quoted because it won't compile in compilation time, it will only
  -- make sense in runtime.
  have pf' := q((etaExpand_eq $(mkLiteralQ M)ᵀ).symm)
  mkApp2 (.const ``id [.zero]) (mkTransposeProp M) pf'

/-- Prove a statement of the form
```lean
theorem Matrix.transpose₂₃ {α : Type*} (a₀₀ a₀₁ a₀₂ a₁₀ a₁₁ a₁₂ : α) :
    !![a₀₀, a₀₁, a₀₂; a₁₀, a₁₁, a₁₂]ᵀ = !![a₀₀, a₁₀; a₀₁, a₁₁; a₀₂, a₁₂] :=
  (etaExpand_eq _).symm
```
-/
def mkTransposeTheorem (u : Level) (m n : Nat) : Q(Prop) :=
  have α : Q(Type u) := .fvar ⟨.anonymous⟩
  have nameE (i j : Nat) : Q($α) := .fvar ⟨.num (.num .anonymous i) j⟩
  have namesA : Array Name := .ofFn fun t : Fin (m * n) ↦ s!"r{t/n}c{t%n}".toName
  have argsA : Array Q($α) := .ofFn fun t : Fin (m * n) ↦ nameE (t/n) (t%n)
  have M : Matrix (Fin m) (Fin n) Q($α) := of fun i j ↦ nameE i j
  have pf' := mkTransposeProof M
  have pf_α := mkLambdas namesA q($α) (pf'.abstract argsA)
  .lam `α q(Type u) (pf_α.abstract #[α]) .implicit

end Qq

open Elab Tactic

/-- A custom theorem for reducing transpose of explicit matrices. For example, `transpose_of% 2 3`
is the theorem saying `!![a, b, c; d, e, f]ᵀ = !![a, d; b, e; c, f]`. Usage:

```lean
example : (!![1, 2, 3; 4, 5, 6]ᵀ : Matrix (Fin (2+1)) (Fin 2) ℤ) = !![1, 4; 2, 5; 3, 6] := by
  rw [transpose_of% 2 3]
``` -/
elab:max (name := transpose_tac_elab)
    "transpose_of% " mStx:num nStx:num : term => do
  let u ← Lean.Meta.mkFreshLevelMVar
  return mkTransposeTheorem u mStx.getNat nStx.getNat

example (u : Matrix (Fin 2) (Fin 3) ℤ) (v : Matrix (Fin 3) (Fin 2) ℤ)
    (hu : u = !![1, 2, 3; 4, 5, 6]) (hv : v = !![1, 4; 2, 5; 3, 6]) :
    uᵀ = v := by
  rw [hu, transpose_of% 2 3, hv]

-- Here we use the convention that `e{name}` is the expression for `{name}`, e.g. `eMT` is the
-- expression corresponding to the transpose of the matrix `M`.
/-- A simproc for terms of the form `Matrix.transpose (Matrix.of _)`. Usage:

```lean
example : (!![1, 2, 3; 4, 5, 6]ᵀ : Matrix (Fin (2+1)) (Fin 2) ℤ) = !![1, 4; 2, 5; 3, 6] := by
  simp
```
-/
simproc matrix_transpose (Matrix.transpose (Matrix.of _)) := .ofQ fun u α eMT ↦ do
  let .succ _ := u | return .continue
  let ~q(@Matrix (Fin (OfNat.ofNat $en)) (Fin (OfNat.ofNat $em)) $R) := α | return .continue
  let ~q(transpose $eM) := eMT | return .continue
  let .some M ← matrixLit? (m := em.natLit!) (n := en.natLit!) (R := R) eM | return .continue
  let h := mkTransposeProof M
  let ⟨0, ~q($lhs = $rhs), h⟩ ← inferTypeQ h | return .continue
  return .visit { expr := rhs, proof? := .some h }

example (u : Matrix (Fin 2) (Fin 3) ℤ) (v : Matrix (Fin 3) (Fin 2) ℤ)
    (hu : u = !![1, 2, 3; 4, 5, 6]) (hv : v = !![1, 4; 2, 5; 3, 6]) :
    uᵀ = v := by
  rw [hu]
  simp only [matrix_transpose]
  rw [hv]
