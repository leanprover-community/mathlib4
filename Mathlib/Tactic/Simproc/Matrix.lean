/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.Data.Matrix.Reflection

/-!
# Simprocs for matrices

In this file we provide a simproc for transpose of explicit matrices.
-/

open Matrix
open Lean Meta Simp Simproc Tactic Qq

attribute [-simp] cons_transpose

namespace Qq

/-- Decompose a vector expression into a vector of expressions. -/
def piFinLit! {u : Level} {n : ℕ} {R : Q(Type u)} (e : Q(Fin $n → $R)) :
    MetaM (Option (Fin n → Q($R))) := do
  match n with
  | 0 => return .some ![]
  | _+1 =>
    let ~q(vecCons $eh? $et?) := e | return .none
    let .some et ← piFinLit! et? | return .none
    return .some (vecCons eh? et)

/-- Decompose a "double vector" expression, i.e. `Fin m → Fin n → R`, into a double vector of
expressions. -/
def piFinPiFinLit! {u : Level} {m n : ℕ} {R : Q(Type u)} (e : Q(Fin $m → Fin $n → $R)) :
    MetaM (Option (Fin m → Fin n → Q($R))) := do
  match m with
  | 0 => return .some ![]
  | _+1 =>
    let ~q(vecCons $eh? $et?) := e | return .none
    let .some eh ← piFinLit! eh? | return .none
    let .some et ← piFinPiFinLit! et? | return .none
    return .some (vecCons eh et)

/-- Decompose a matrix expression into a matrix of expressions. -/
def matrixLit! {u : Level} {m n : ℕ} {R : Q(Type u)} (M : Q(Matrix (Fin $m) (Fin $n) $R)) :
    MetaM (Option (Matrix (Fin m) (Fin n) Q($R))) := do
  let ~q(of $M) := M | return .none
  let .some e ← piFinPiFinLit! M | return .none
  return of e

/-- Construct a vector expression from a vector of expressions. -/
def mkPiFinLit {u : Level} {n : ℕ} {R : Q(Type u)} (e : Fin n → Q($R)) :
    Q(Fin $n → $R) :=
  match n with
  | 0 => q(![])
  | _+1 => q(vecCons $(e 0) $(mkPiFinLit (e ∘ Fin.succ)))

/-- Construct a double vector expression from a double vector of expressions. -/
def mkPiFinPiFinLit {u : Level} {m n : ℕ} {R : Q(Type u)} (e : Fin m → Fin n → Q($R)) :
    Q(Fin $m → Fin $n → $R) :=
  match m with
  | 0 => q(![])
  | _+1 => q(vecCons $(mkPiFinLit (e 0)) $(mkPiFinPiFinLit (e ∘ Fin.succ)))

/-- Construct a matrix expression from a matrix of expressions. -/
def mkMatrixLit {u : Level} {m n : ℕ} {R : Q(Type u)} (M : Matrix (Fin m) (Fin n) Q($R)) :
    Q(Matrix (Fin $m) (Fin $n) $R) :=
  q(of $(mkPiFinPiFinLit M))

end Qq

-- Here we adopt the convention that `eM` refers to the matrix expression, and `M` refers to the
-- matrix of expressions.
/-- A simproc for terms of the form `Matrix.diagonal ![a₀, a₁, ⋯]`. -/
simproc matrix_diagonal (Matrix.diagonal _) := .ofQ fun u α eM ↦ do
  let .succ _ := u | return .continue
  let ~q(Matrix (Fin (OfNat.ofNat $ek)) (Fin (OfNat.ofNat $ek)) $R) := α | return .continue
  let ~q(@diagonal _ _ _ $zR $ev) := eM | return .continue
  let .some v ← piFinLit! (n := ek.natLit!) (R := R) ev | return .continue
  let _ : Zero Q($R) := ⟨q(0)⟩
  return .visit { expr := mkMatrixLit (diagonal v), proof? := .some q(Eq.symm (etaExpand_eq $eM)) }

example : (diagonal ![37, -1] : Matrix (Fin 2) (Fin 2) ℤ) = !![37, 0; 0, -1] := by
  simp

/-
# TODO: Simplify the examples below

The examples below can be simplified using the appropriate lemmas for diagonal matrices, after using
another (yet to be written) simproc to expand the constant vectors (e.g. `37 : Fin 2 → α` expands to
`![37, 37]`).

example {α : Type*} [Zero α] :
    (0 : Matrix (Fin 2) (Fin 2) α) = !![0, 0; 0, 0] := by
  simp [← diagonal_zero]

example {α : Type*} [Zero α] [One α] :
    (1 : Matrix (Fin 2) (Fin 2) α) = !![1, 0; 0, 1] := by
  simp [← diagonal_one]

example {α : Type*} [Zero α] [NatCast α] :
    (37 : Matrix (Fin 2) (Fin 2) α) = !![37, 0; 0, 37] := by
  simp [← diagonal_ofNat]

example {α : Type*} [Zero α] [NatCast α] (n : ℕ) :
    (n : Matrix (Fin 2) (Fin 2) α) = !![(n : α), 0; 0, n] := by
  simp [← diagonal_natCast]

example (n : ℤ) : (n : Matrix (Fin 2) (Fin 2) ℤ) = !![n, 0; 0, n] := by
  simp [← diagonal_intCast]
-/
