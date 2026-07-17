/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Function.Iterate

/-!

# A division-free determinant algorithm

This file defines `birdDet`and `Spec.birdDet`, implementations of an
division-free algorithm for computing determinants. The algorithm runs in O(n^4)
for an n-by-n matrix.

This determinant algorithm comes from
[Richard S. Bird, *A simple division-free algorithm for computing determinants*][bird2011].

## Main definitions

- `BirdDet.birdDet`: The entrypoint for the determinant calculation.
- `BirdDet.get`: matrix entry lookup.
- `BirdDet.sumFrom`: The sum `f lo + ... + f (n - 1)`.
- `BirdDet.stepEntry`: One scalar recurrence step.
- `BirdDet.Spec.birdDet`: An implementation of Bird's algorithm using `Matrix`.

## Main lemmas

The lemmas in this file are unfolding equations.

-/

public section

namespace BirdDet

variable {R : Type*} [CommRing R]

/--
`get n A i j` returns the (i, j)th entry of the `n × n` matrix whose entries are
stored in `A` in row-major order.

The function does not check the matrix index bounds.
-/
protected def get (n : ℕ) (A : Array R) (i j : ℕ) : R :=
  A.getD (n * i + j) 0

/-- Sum `f lo + ... + f (n - 1)`. Returns zero when `n <= lo`. -/
protected def sumFrom (n lo : ℕ) (f : ℕ → R) : R :=
  if lo < n then f lo + BirdDet.sumFrom n (lo + 1) f else 0

/--
One entry of one scalar Bird recurrence step.

Bird's paper defines a matrix recursion for an `n × n` matrix `A`:

```
F_0 = A
F_{t+1} = μ(F_t) * A
```

where `μ(F_t)` is obtained from `F_t` by replacing each diagonal entry
`F_t k k` with the negative sum of the diagonal entries below it, setting the
entries in the lower triangular part to 0, and leaving all other entries
unchanged:

```
μ(F_t) =
  0                                   if i >= j
  - ∑ k from i+1 to n-1, F_t k k      if i = j
  F_t i j                             if i < j
```

If we write out the entry-wise matrix multiplication `F_{t+1} i j = (μ(F_t) * A) i j`
we obtain:

```
F_{t+1} i j =
  - (∑ k from i+1 to n-1, F_t k k) * (A i j)
  + ∑ k from i+1 to n-1, (F_t i k) * (A k j)
```
-/
def stepEntry (n : ℕ) (A : Array R) (F : ℕ → ℕ → R) (i j : ℕ) : R :=
  -(BirdDet.sumFrom n (i + 1) fun k => F k k) * BirdDet.get n A i j +
    BirdDet.sumFrom n (i + 1) fun k => F i k * BirdDet.get n A k j

/--
`birdDet n A` computes the determinant of the `n × n` matrix whose entries are
stored in `A` in row-major order.
-/
def birdDet (n : ℕ) (A : Array R) : R :=
  match n with
  | 0 => 1
  | k + 1 => (-1 : R) ^ k * (stepEntry n A)^[k] (BirdDet.get n A) 0 0

/- Unfolding lemmas -/

/-- Unfold a row-major matrix entry lookup. -/
theorem get_eq (n : ℕ) (A : Array R) (i j : ℕ) :
    BirdDet.get n A i j = A.getD (n * i + j) 0 := by
  rfl

theorem sumFrom_step (n lo : ℕ) (f : ℕ → R) (h : lo < n) :
    BirdDet.sumFrom n lo f = f lo + BirdDet.sumFrom n (lo + 1) f := by
  rw [BirdDet.sumFrom]
  simp [h]

theorem sumFrom_stop (n lo : ℕ) (f : ℕ → R) (h : ¬ lo < n) :
    BirdDet.sumFrom n lo f = 0 := by
  rw [BirdDet.sumFrom]
  simp [h]

/-- Induction following the recursive structure of `sumFrom`. -/
@[elab_as_elim]
theorem sumFrom_induct (n : ℕ) (motive : ℕ → Prop)
    (step : ∀ lo, lo < n → motive (lo + 1) → motive lo)
    (stop : ∀ lo, ¬lo < n → motive lo) (lo : ℕ) : motive lo :=
  BirdDet.sumFrom.induct n motive step stop lo

/-- Unfold one scalar Bird recurrence step to the entry-wise formula. -/
theorem stepEntry_eq (n : ℕ) (A : Array R) (F : ℕ → ℕ → R) (i j : ℕ) :
    stepEntry n A F i j =
      -(BirdDet.sumFrom n (i + 1) fun k => F k k) * BirdDet.get n A i j
        + BirdDet.sumFrom n (i + 1) fun k => F i k * BirdDet.get n A k j := by
  rfl

theorem birdDet_zero (A : Array R) : birdDet 0 A = 1 := by
  rfl

/-- Unfold `birdDet` at a successor dimension. -/
theorem birdDet_succ (k : ℕ) (A : Array R) :
    birdDet (k + 1) A =
      (-1 : R) ^ k * (stepEntry (k + 1) A)^[k] (BirdDet.get (k + 1) A) 0 0 :=
  by rw [birdDet]

theorem birdDet_eq (n k : ℕ) (A : Array R) (hn : n = k + 1) :
    birdDet n A = (-1 : R) ^ k * (stepEntry n A)^[k] (BirdDet.get n A) 0 0 := by
  subst hn
  exact birdDet_succ k A

namespace Spec

open scoped BigOperators

/-- One entry of one Matrix/Fin Bird recurrence step. -/
def stepEntry {n : ℕ} (A F : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  .of fun i j ↦ (-∑ k ∈ Finset.Ioi i, F k k) * A i j +
    ∑ k ∈ Finset.Ioi i, F i k * A k j

/-- A version of the Bird determinant algorithm that is stated in terms of `Matrix`. -/
def birdDet {n : ℕ} (A : Matrix (Fin n) (Fin n) R) : R :=
  match n with
  | 0 => 1
  | k + 1 => (-1 : R) ^ k * (stepEntry A)^[k] A 0 0

theorem stepEntry_eq {n : ℕ} (A F : Matrix (Fin n) (Fin n) R) :
    stepEntry A F =
      .of fun i j ↦ (-∑ k ∈ Finset.Ioi i, F k k) * A i j
        + ∑ k ∈ Finset.Ioi i, F i k * A k j := by
  rfl

@[simp] theorem birdDetSpec_zero (A : Matrix (Fin 0) (Fin 0) R) :
    birdDet A = 1 := by
  rfl

theorem birdDetSpec_succ {k : ℕ} (A : Matrix (Fin (k + 1)) (Fin (k + 1)) R) :
    birdDet A = (-1 : R) ^ k * (stepEntry A)^[k] A 0 0 := by
  rw [birdDet]

end Spec

end BirdDet

end
