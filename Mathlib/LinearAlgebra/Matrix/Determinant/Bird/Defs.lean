/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs

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
- `BirdDet.diagSum`, `BirdDet.diagTerm`, `BirdDet.tailSum`,
  `BirdDet.stepEntry`: Named pieces of one scalar recurrence step.
- `BirdDet.iter`: The internal scalar recurrence for Bird's algorithm.
- `BirdDet.Spec.iterMatrix`: The Matrix recurrence starting from the matrix entries.
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
The diagonal tail sum used in the scalar Bird recurrence at row `i`.

This is the sum of the diagonal entries of `F` strictly below row `i`.
-/
def diagSum (n : ℕ) (F : ℕ → ℕ → R) (i : ℕ) : R :=
  BirdDet.sumFrom n (i + 1) fun k => F k k

/-- The diagonal contribution to one scalar Bird recurrence step. -/
def diagTerm (n : ℕ) (A : Array R) (F : ℕ → ℕ → R) (i j : ℕ) : R :=
  -(diagSum n F i) * BirdDet.get n A i j

/-- The upper-tail contribution to one scalar Bird recurrence step. -/
def tailSum (n : ℕ) (A : Array R) (F : ℕ → ℕ → R) (i j : ℕ) : R :=
  BirdDet.sumFrom n (i + 1) fun k => F i k * BirdDet.get n A k j

/-- One entry of one scalar Bird recurrence step. -/
def stepEntry (n : ℕ) (A : Array R) (F : ℕ → ℕ → R) (i j : ℕ) : R :=
  diagTerm n A F i j + tailSum n A F i j

/--
# Scalar recurrence for Bird's algorithm.

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
protected def iter (n : ℕ) (A : Array R) (t : ℕ) (F : ℕ → ℕ → R) :
    ℕ → ℕ → R :=
  match t with
  | 0 => F
  | t + 1 => fun i j => stepEntry n A (BirdDet.iter n A t F) i j

/--
`birdDet n A` computes the determinant of the `n × n` matrix whose entries are
stored in `A` in row-major order.
-/
def birdDet (n : ℕ) (A : Array R) : R :=
  match n with
  | 0 => 1
  | k + 1 => (-1 : R) ^ k * BirdDet.iter n A k (BirdDet.get n A) 0 0

/- Unfolding lemmas -/

/-- Unfold a row-major matrix entry lookup. -/
theorem get_eq (n : ℕ) (A : Array R) (i j : ℕ) :
    BirdDet.get n A i j = A.getD (n * i + j) 0 :=
  BirdDet.get.eq_1 n A i j

theorem sumFrom_step (n lo : ℕ) (f : ℕ → R) (h : lo < n) :
    BirdDet.sumFrom n lo f = f lo + BirdDet.sumFrom n (lo + 1) f := by
  rw [BirdDet.sumFrom.eq_1]
  simp [h]

theorem sumFrom_stop (n lo : ℕ) (f : ℕ → R) (h : ¬ lo < n) :
    BirdDet.sumFrom n lo f = 0 := by
  rw [BirdDet.sumFrom.eq_1]
  simp [h]

/-- Induction following the recursive structure of `sumFrom`. -/
@[elab_as_elim]
theorem sumFrom_induct (n : ℕ) (motive : ℕ → Prop)
    (step : ∀ lo, lo < n → motive (lo + 1) → motive lo)
    (stop : ∀ lo, ¬lo < n → motive lo) (lo : ℕ) : motive lo :=
  BirdDet.sumFrom.induct n motive step stop lo

/-- Unfold `diagSum` to the corresponding `sumFrom`. -/
theorem diagSum_eq (n : ℕ) (F : ℕ → ℕ → R) (i : ℕ) :
    diagSum n F i = BirdDet.sumFrom n (i + 1) fun k => F k k :=
  BirdDet.diagSum.eq_1 n F i

/-- Unfold `diagTerm` to its scalar formula. -/
theorem diagTerm_eq (n : ℕ) (A : Array R) (F : ℕ → ℕ → R) (i j : ℕ) :
    diagTerm n A F i j =
      -(BirdDet.sumFrom n (i + 1) fun k => F k k) * BirdDet.get n A i j := by
  rw [BirdDet.diagTerm.eq_1, diagSum_eq]

/-- Unfold `tailSum` to the corresponding `sumFrom`. -/
theorem tailSum_eq (n : ℕ) (A : Array R) (F : ℕ → ℕ → R) (i j : ℕ) :
    tailSum n A F i j =
      BirdDet.sumFrom n (i + 1) fun k => F i k * BirdDet.get n A k j :=
  BirdDet.tailSum.eq_1 n A F i j

/-- Unfold one scalar Bird recurrence step to the entry-wise formula. -/
theorem stepEntry_eq (n : ℕ) (A : Array R) (F : ℕ → ℕ → R) (i j : ℕ) :
    stepEntry n A F i j =
      -(BirdDet.sumFrom n (i + 1) fun k => F k k) * BirdDet.get n A i j
        + BirdDet.sumFrom n (i + 1) fun k => F i k * BirdDet.get n A k j := by
  rw [BirdDet.stepEntry.eq_1, diagTerm_eq, tailSum_eq]

theorem iter_zero (n : ℕ) (A : Array R) (F : ℕ → ℕ → R) (i j : ℕ) :
    BirdDet.iter n A 0 F i j = F i j := by
  rw [BirdDet.iter.eq_1]

theorem iter_succ (n : ℕ) (A : Array R) (t : ℕ) (F : ℕ → ℕ → R) (i j : ℕ) :
    BirdDet.iter n A (t + 1) F i j =
      stepEntry n A (BirdDet.iter n A t F) i j := by
  rw [BirdDet.iter.eq_2]

theorem birdDet_zero (A : Array R) : birdDet 0 A = 1 :=
  BirdDet.birdDet.eq_1 A

/-- Unfold `birdDet` at a successor dimension. -/
theorem birdDet_succ (k : ℕ) (A : Array R) :
    birdDet (k + 1) A =
      (-1 : R) ^ k * BirdDet.iter (k + 1) A k (BirdDet.get (k + 1) A) 0 0 :=
  BirdDet.birdDet.eq_2 A k

theorem birdDet_eq (n k : ℕ) (A : Array R) (hn : n = k + 1) :
    birdDet n A = (-1 : R) ^ k * BirdDet.iter n A k (BirdDet.get n A) 0 0 := by
  subst hn
  exact birdDet_succ k A

namespace Spec

open scoped BigOperators

/-- The diagonal tail sum used in the Matrix/Fin specification. -/
def diagSum {n : ℕ} (F : Matrix (Fin n) (Fin n) R) (i : Fin n) : R :=
  ∑ k : Fin n, if i < k then F k k else 0

/-- The diagonal contribution to one Matrix/Fin Bird recurrence step. -/
def diagTerm {n : ℕ}
    (A F : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  .of fun i j => -(diagSum F i) * A i j

/-- The upper-tail contribution to one Matrix/Fin Bird recurrence step. -/
def tailSum {n : ℕ}
    (A F : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  .of fun i j => ∑ k : Fin n, if i < k then F i k * A k j else 0

/-- One entry of one Matrix/Fin Bird recurrence step. -/
def stepEntry {n : ℕ}
    (A F : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  diagTerm A F + tailSum A F

/-- Iterate the Bird recurrence step `stepEntry A` a total of `p` times, starting
from the matrix `F`. -/
def iterEntry {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) :
    ℕ → Matrix (Fin n) (Fin n) R → Matrix (Fin n) (Fin n) R
  | 0, F => F
  | p + 1, F => fun i j => stepEntry A (iterEntry A p F) i j

/--
`iterMatrix A p i j` is Bird's `x^(p)_{ij}`: the `(i, j)` entry after starting
the Bird recurrence from the matrix `A` itself.
-/
def iterMatrix {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R)
    (p : ℕ) : Matrix (Fin n) (Fin n) R :=
  iterEntry A p A

/-- A version of the Bird determinant algorithm that is stated in terms of `Matrix`. -/
def birdDet {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) : R :=
  match n with
  | 0 => 1
  | k + 1 => (-1 : R) ^ k * iterEntry A k A 0 0

/-- Unfold the diagonal tail sum in the matrix specification. -/
theorem diagSum_eq {n : ℕ} (F : Matrix (Fin n) (Fin n) R) (i : Fin n) :
    diagSum F i = ∑ k : Fin n, if i < k then F k k else 0 :=
  BirdDet.Spec.diagSum.eq_1 F i

theorem stepEntry_eq {n : ℕ}
    (A F : Matrix (Fin n) (Fin n) R)
    (i j : Fin n) :
    stepEntry A F i j =
      (-∑ k : Fin n, if i < k then F k k else 0) * A i j
        + ∑ k : Fin n, if i < k then F i k * A k j else 0 := by
  rw [BirdDet.Spec.stepEntry.eq_1, BirdDet.Spec.diagTerm.eq_1,
    BirdDet.Spec.tailSum.eq_1]
  simp only [Matrix.add_apply, Matrix.of_apply, diagSum_eq]

theorem iterEntry_zero {n : ℕ}
    (A F : Matrix (Fin n) (Fin n) R) :
    iterEntry A 0 F = F :=
  BirdDet.Spec.iterEntry.eq_1 A F

theorem iterEntry_succ {n p : ℕ}
    (A F : Matrix (Fin n) (Fin n) R) :
    iterEntry A (p + 1) F =
      fun i j => stepEntry A (iterEntry A p F) i j :=
  BirdDet.Spec.iterEntry.eq_2 A F p

theorem iterMatrix_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R)
    (i j : Fin n) :
    iterMatrix A 0 i j = A i j := by
  rw [BirdDet.Spec.iterMatrix.eq_1, iterEntry_zero]

theorem iterMatrix_succ {n p : ℕ}
    (A : Matrix (Fin n) (Fin n) R) :
    iterMatrix A (p + 1) =
      fun i j => stepEntry A (iterMatrix A p) i j := by
  rw [BirdDet.Spec.iterMatrix.eq_1, iterEntry_succ, BirdDet.Spec.iterMatrix.eq_1]

/-- Unfold one entry of the matrix recurrence at a successor step. -/
theorem iterMatrix_succ_apply {n p : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    iterMatrix A (p + 1) i j = stepEntry A (iterMatrix A p) i j := by
  rw [iterMatrix_succ]

theorem birdDetSpec_zero
    (A : Matrix (Fin 0) (Fin 0) R) :
    birdDet A = 1 :=
  BirdDet.Spec.birdDet.eq_1 A

theorem birdDetSpec_succ {k : ℕ}
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) R) :
    birdDet A =
      (-1 : R) ^ k * iterEntry A k A 0 0 :=
  BirdDet.Spec.birdDet.eq_2 k A

theorem birdDetSpec_succ_iterMatrix {k : ℕ}
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) R) :
    birdDet A =
      (-1 : R) ^ k * iterMatrix A k 0 0 := by
  rw [birdDetSpec_succ, BirdDet.Spec.iterMatrix.eq_1]

end Spec

end BirdDet

end
