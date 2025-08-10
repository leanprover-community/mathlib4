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

/-- Decompose a vector expression into a vector of expressions. -/
def piFinLit? {u : Level} {n : ℕ} {R : Q(Type u)} (e : Q(Fin $n → $R)) :
    MetaM (Option (Fin n → Q($R))) := do
  match n with
  | 0 => return .some ![]
  | _+1 =>
    let ~q(vecCons $eh? $et?) := e | return .none
    let .some et ← piFinLit? et? | return .none
    return .some (vecCons eh? et)

/-- Decompose a "double vector" expression, i.e. `Fin m → Fin n → R`, into a double vector of
expressions. -/
def piFinPiFinLit? {u : Level} {m n : ℕ} {R : Q(Type u)} (e : Q(Fin $m → Fin $n → $R)) :
    MetaM (Option (Fin m → Fin n → Q($R))) := do
  match m with
  | 0 => return .some ![]
  | _+1 =>
    let ~q(vecCons $eh? $et?) := e | return .none
    let .some eh ← piFinLit? eh? | return .none
    let .some et ← piFinPiFinLit? et? | return .none
    return .some (vecCons eh et)

/-- Decompose a matrix expression into a matrix of expressions. -/
def matrixLit? {u : Level} {m n : ℕ} {R : Q(Type u)} (M : Q(Matrix (Fin $m) (Fin $n) $R)) :
    MetaM (Option (Matrix (Fin m) (Fin n) Q($R))) := do
  let ~q(of $M) := M | return .none
  let .some e ← piFinPiFinLit? M | return .none
  return of e

/-- Given a matrix of expressions, construct a proof of `(mkLiteralQ M)ᵀ = mkLiteralQ (Mᵀ)`. -/
def mkTransposeProof {u : Level} {α : Q(Type u)} {m n : ℕ} (M : Matrix (Fin m) (Fin n) Q($α)) :
    (P : Q(Prop)) × Q($P) :=
  ⟨q($(mkLiteralQ M)ᵀ = $(mkLiteralQ Mᵀ)),
  cast (by rfl) q((etaExpand_eq $(mkLiteralQ M)ᵀ).symm)⟩

/-- Prove a statement of the form
```
theorem Matrix.transpose₂₃ {α : Type*} (a₀₀ a₀₁ a₀₂ a₁₀ a₁₁ a₁₂ : α) :
    !![a₀₀, a₀₁, a₀₂; a₁₀, a₁₁, a₁₂]ᵀ = !![a₀₀, a₁₀; a₀₁, a₁₁; a₀₂, a₁₂] :=
  (etaExpand_eq _).symm
```
Returns the type of this statement and its proof. -/
def mkTransposeProp (u : Level) (m n : ℕ) : (P : Q(Prop)) × Q($P) :=
  let α : Q(Type u) := Expr.fvar ⟨`α⟩
  let varName (i : Fin m) (j : Fin n) : Name :=
    ("a_" ++ i.val.repr ++ "_" ++ j.val.repr).toName
  let var (i : Fin m) (j : Fin n) : Q($α) :=
    .fvar ⟨varName i j⟩
  let ⟨P', pf'⟩ := mkTransposeProof (of var)
  let argsE : List Expr :=
    [α] ++ (List.finRange m).flatMap fun i : Fin m ↦ List.ofFn fun j : Fin n ↦ by exact var i j
  let argsD : List LocalDecl :=
    [.cdecl 0 ⟨`α⟩ `α (.sort u.succ) .implicit .default] ++
    (List.finRange m).flatMap fun i : Fin m ↦ List.ofFn fun j : Fin n ↦
      .cdecl (finProdFinEquiv (i, j) + 1) ⟨varName i j⟩ (varName i j) α .default .default
  ⟨Closure.mkForall argsD.toArray (P'.abstract argsE.toArray),
  Closure.mkLambda argsD.toArray (pf'.abstract argsE.toArray)⟩

end Qq

open Elab Tactic

/-- A custom theorem for reducing transpose of explicit matrices. For example, `transpose_of% 2 3`
is the theorem saying `!![a, b, c; d, e, f]ᵀ = !![a, d; b, e; c, f]`. Usage:

```lean
example : (!![1, 2, 3; 4, 5, 6]ᵀ : Matrix (Fin (2+1)) (Fin 2) ℤ) = !![1, 4; 2, 5; 3, 6] := by
  rw [transpose_of% 2 3]
``` -/
elab:max (name := transpose_tac_elab)
    "transpose_of% " mStx:term:max nStx:term:max : term => do
  let u ← Lean.Meta.mkFreshLevelMVar
  let m : Q(Nat) ← Term.elabTermEnsuringType mStx (mkConst ``Nat)
  let n : Q(Nat) ← Term.elabTermEnsuringType nStx (mkConst ``Nat)
  let some m ← (evalNat m).run
    | throwErrorAt mStx "Expecting a natural number, have{indentD m}"
  let some n ← (evalNat n).run
    | throwErrorAt nStx "Expecting a natural number, have{indentD n}"
  let ⟨P, h⟩ := mkTransposeProp u m n
  let .some h ← checkTypeQ h P | throwError m!"Wrong proof generated for {m}, {n}."
  mkExpectedTypeHint h P

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
  let ⟨P, h⟩ := mkTransposeProof M
  let ~q($lhs = $rhs) := P | return .continue
  return .visit { expr := rhs, proof? := .some h }

example (u : Matrix (Fin 2) (Fin 3) ℤ) (v : Matrix (Fin 3) (Fin 2) ℤ)
    (hu : u = !![1, 2, 3; 4, 5, 6]) (hv : v = !![1, 4; 2, 5; 3, 6]) :
    uᵀ = v := by
  rw [hu]
  simp only [matrix_transpose]
  rw [hv]
