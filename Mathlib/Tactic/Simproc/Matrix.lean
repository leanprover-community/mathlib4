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

/-- A simproc for terms of the form `Matrix.diagonal _`. -/
simproc matrix_diagonal (Matrix.diagonal _) := .ofQ fun u α M? ↦ do
  -- trace[debug] m!"{M?}"
  -- haveI' : $α =Q Matrix (Fin (OfNat.ofNat $k?)) (Fin (OfNat.ofNat $k?)) $R := ⟨⟩
  -- let .some _ ← trySynthInstanceQ q(Zero ($R)) | return .continue
  -- match M? with
  let .succ _ := u | return .continue
  let ~q(@Matrix (Fin (OfNat.ofNat $k?)) (Fin (OfNat.ofNat $k?)) $R) := α | return .continue
  trace[debug] m!"{R}, {α}, {M?}, {k?}"
  let ~q(@diagonal (Fin (OfNat.ofNat $k?)) $R $dF $zR $v) := M? | return .continue
  return .continue
  -- | _ => return .continue
  -- let ~q(diagonal $v) := M? | return .continue
  -- let ~q(@Nat.cast (Matrix (Fin $k) (Fin $k) $R) (@instNatCastOfZero $_ $R $_ $_ $inst) $n) := M? | return .continue
  -- return .continue
  -- let ~q(transpose $M?) := MT? | return .continue
  -- let m := m?.natLit!
  -- let n := n?.natLit!
  -- let .some M ← matrixLit! (m := m) (n := n) (R := R) M? | return .continue
  -- return .visit { expr := mkMatrixLit (Mᵀ), proof? := .some q(Eq.symm (etaExpand_eq $MT?)) }

set_option trace.debug true

example (n : ℤ) : (diagonal ![37, -1] : Matrix (Fin 2) (Fin 2) ℤ) = !![37, 0; 0, -1] := by
  simp

example {α : Type*} [Zero α] :
    (0 : Matrix (Fin 2) (Fin 2) α) = !![0, 0; 0, 0] := by
  simp

example {α : Type*} [Zero α] [One α] :
    (1 : Matrix (Fin 2) (Fin 2) α) = !![1, 0; 0, 1] := by
  simp

example {α : Type*} [Zero α] [NatCast α] :
    (37 : Matrix (Fin 2) (Fin 2) α) = !![37, 0; 0, 37] := by
  simp

example {α : Type*} [Zero α] [NatCast α] (n : ℕ) :
    (n : Matrix (Fin 2) (Fin 2) α) = !![(n : α), 0; 0, n] := by
  simp

example (n : ℤ) : (n : Matrix (Fin 2) (Fin 2) ℤ) = !![-3, 0; 0, -3] := by
  simp
