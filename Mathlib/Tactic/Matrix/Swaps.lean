/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public meta import Qq
public import Mathlib.Data.Fin.Tuple.Reflection  -- shake: keep (Qq dependency)
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.LinearAlgebra.Matrix.Defs  -- shake: keep (Qq dependency)


/-!
# Permutations from lists of swaps

This file defines the permutations of a list of swaps and provides tactic utilities to certify row
permutations of matrix literals corresponding to those swaps.

## Main definitions

- `permOfSwaps`: the permutation `swap a₀ b₀ * swap a₁ b₁ * ⋯` of a list of swaps, with its sign
  `intCast_sign_permOfSwaps`.
- `mkSwapsLitQ`: build the list literal of the swaps.
- `certifyPermSign`, certify the sign of the permutation of swaps.
- `certifyPermEq`: certify the row arrangement `A.submatrix σ id = Aσ` of a matrix literal.
-/

public section

namespace Mathlib.Tactic.Matrix

/-- The permutation `swap a₀ b₀ * swap a₁ b₁ * ⋯` of the swaps in `l`. -/
@[expose] def permOfSwaps {m : Type*} [DecidableEq m] (l : List (m × m)) : Equiv.Perm m :=
  (l.map fun p ↦ Equiv.swap p.1 p.2).foldl (· * ·) 1

theorem intCast_sign_permOfSwaps {α : Type*} [Ring α] {m : Type*} [DecidableEq m] [Fintype m]
    {l : List (m × m)} {k : ℕ} (hl : l.all fun p ↦ p.1 != p.2) (hk : l.length = k) :
    ((Equiv.Perm.sign (permOfSwaps l) : ℤ) : α) = (-1) ^ k := by
  rw [permOfSwaps, ← List.prod_eq_foldl, Equiv.Perm.sign_prod_list_swap]
  · simp [hk]
  · grind [Equiv.Perm.IsSwap]

meta section

open Lean Meta Qq

/-- Build the list literal of the recorded swaps, the argument of `permOfSwaps`. -/
def mkSwapsLitQ (m : Nat) (swaps : Array (Nat × Nat)) : MetaM Q(List (Fin $m × Fin $m)) := do
  let pairs ← swaps.toList.mapM fun (a, b) ↦ do
    let aQ : Q(Fin $m) ← mkFinLitQ m a
    let bQ : Q(Fin $m) ← mkFinLitQ m b
    return q(($aQ, $bQ))
  return mkListLitQ pairs

/-- Compute the sign of the permutation of the `k` swaps `swaps` with the corresponding proof. The
swaps must be between distinct rows, which an elimination guarantees. -/
def certifyPermSign {u : Level} {α : Q(Type u)} (rα : Q(CommRing $α)) {m : Nat}
    (swaps : Q(List (Fin $m × Fin $m))) (k : Nat) :
    (s : Q($α)) × Q(((Equiv.Perm.sign (permOfSwaps $swaps) : Int) : $α) = $s) :=
  let hl : Q(($swaps).all (fun p ↦ p.1 != p.2) = true) := (q(Eq.refl true) : Expr)
  let hk : Q(($swaps).length = $k) := (q(Eq.refl $k) : Expr)
  ⟨q((-1) ^ $k), q(intCast_sign_permOfSwaps $hl $hk)⟩

/-- Prove the row arrangement `A.submatrix σ id = Aσ`. -/
def certifyPermEq {u : Level} {m n : Nat} {α : Q(Type u)} (A : Q(Matrix (Fin $m) (Fin $n) $α))
    (Aσ : Q(Matrix (Fin $m) (Fin $n) $α)) (σ : Q(Equiv.Perm (Fin $m))) :
    Q(($A).submatrix $σ id = $Aσ) :=
  mkExpectedPropHint
    q(congrArg (fun f ↦ Matrix.of f) (FinVec.etaExpand_eq (fun i ↦ $A ($σ i))).symm)
    q(($A).submatrix $σ id = $Aσ)

end

end Mathlib.Tactic.Matrix
