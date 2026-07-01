/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Mathlib.Algebra.Ring.Defs

/-!

# A division-free determinant algorithm

This file defines `birdDet`, an implementation of an division-free algorithm for
computing determinants. The algorithm runs in O(n^4) for an n-by-n matrix.

This determinant algorithm comes from:

Title:  A simple division-free algorithm for computing determinants.
Author: Richard S. Bird
URL:    https://doi.org/10.1016/j.ipl.2011.08.006

## Main definitions

- `BirdDet.birdDet`: The entrypoint for the determinant calculation.
- `BirdDet.get`: matrix entry lookup.
- `BirdDet.sumFrom`: The sum `f lo + ... + f (n - 1)`.
- `BirdDet.iter`: The internal scalar recurrence for Bird's algorithm.

## Main lemmas

The lemmas in this file are unfolding equations.

-/

@[expose] public section

namespace BirdDet

variable
  {R : Type*}
  [CommRing R]

/--
`get n A i j` returns the (i, j)th entry of the `n × n` matrix whose entries are
stored in `A` in row-major order.

The function does not check the matrix index bounds.
-/
def get (n : Nat) (A : Array R) (i j : Nat) : R :=
  A.getD (i * n + j) 0

/-- Sum `f lo + ... + f (n - 1)`. Returns zero when `n <= lo`. -/
def sumFrom (n lo : Nat) (f : Nat → R) : R :=
  if lo < n then f lo + sumFrom n (lo + 1) f else 0

/--
# Scalar formula for one recurrence step.

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
def iter (n : Nat) (A : Array R) (t : Nat) (F : Nat → Nat → R) : Nat → Nat → R :=
  match t with
  | 0 => F
  | t + 1 => fun i j =>
    -(sumFrom n (i + 1) fun k => iter n A t F k k) * get n A i j
    + sumFrom n (i + 1) fun k => iter n A t F i k * get n A k j

/--
`birdDet n A` computes the determinant of the `n × n` matrix whose entries are
stored in `A` in row-major order.
-/
def birdDet (n : Nat) (A : Array R) : R :=
  match n with
  | 0 => 1
  | k + 1 => (-1 : R) ^ k * iter n A k (get n A) 0 0

/- Unfolding lemmas -/

theorem sumFrom_step (n lo : Nat) (f : Nat → R) (h : lo < n) :
    sumFrom n lo f = f lo + sumFrom n (lo + 1) f := by
      rw [sumFrom]
      simp [h]

theorem sumFrom_stop (n lo : Nat) (f : Nat → R) (h : ¬ lo < n) :
    sumFrom n lo f = 0 := by
      rw [sumFrom]
      simp [h]

theorem iter_zero (n : Nat) (A : Array R) (F : Nat → Nat → R) (i j : Nat) :
    iter n A 0 F i j = F i j := rfl

theorem iter_succ (n : Nat) (A : Array R) (t : Nat) (F : Nat → Nat → R) (i j : Nat) :
    iter n A (t + 1) F i j =
    -(sumFrom n (i + 1) fun k => iter n A t F k k) * get n A i j
    + sumFrom n (i + 1) fun k => iter n A t F i k * get n A k j := rfl

theorem birdDet_zero (A : Array R) : birdDet 0 A = 1 := rfl

theorem birdDet_eq (n k : Nat) (A : Array R) (hn : n = k + 1) :
    birdDet n A = (-1 : R) ^ k * iter n A k (get n A) 0 0 := by
      subst hn
      rfl

end BirdDet

end
