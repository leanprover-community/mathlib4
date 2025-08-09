/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.Data.Matrix.Reflection
import Mathlib.Tactic.HaveI

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

/-- A simproc for terms of the form `Matrix.transpose (Matrix.of _)`. -/
simproc matrix_transpose (Matrix.transpose (Matrix.of _)) := .ofQ fun u α MT? ↦ do
  let .succ _ := u | return .continue
  let ~q(@Matrix (Fin (OfNat.ofNat $n?)) (Fin (OfNat.ofNat $m?)) $R) := α | return .continue
  let ~q(transpose $M?) := MT? | return .continue
  let m := m?.natLit!
  let n := n?.natLit!
  let .some M ← matrixLit! (m := m) (n := n) (R := R) M? | return .continue
  return .visit { expr := mkMatrixLit (Mᵀ), proof? := .some q(Eq.symm (etaExpand_eq $MT?)) }

example : (!![1, 2, 3; 4, 5, 6]ᵀ : Matrix (Fin (2+1)) (Fin 2) ℤ) = !![1, 4; 2, 5; 3, 6] := by
  simp
