/-
Copyright (c) 2025 Jonathan Reich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Reich
-/
module

public import Mathlib.Algebra.Lie.CartanMatrix
public import Mathlib.Data.Fin.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Cartan matrices for classical Lie algebras

This file extends `Mathlib.Algebra.Lie.CartanMatrix` with Cartan matrices for the classical
infinite families of simple Lie algebras: types A, B, C, and D.

## Main definitions

* `CartanMatrix.A` : The Cartan matrix of type Aₙ₋₁ (rank n-1, corresponding to sl(n))
* `CartanMatrix.B` : The Cartan matrix of type Bₙ (rank n, corresponding to so(2n+1))
* `CartanMatrix.C` : The Cartan matrix of type Cₙ (rank n, corresponding to sp(2n))
* `CartanMatrix.D` : The Cartan matrix of type Dₙ (rank n, corresponding to so(2n), requires n ≥ 4)

## Implementation notes

The Cartan matrices are defined as functions `Fin n → Fin n → ℤ` and then converted to
`Matrix (Fin n) (Fin n) ℤ` using `Matrix.of`. This allows for a clean definition that
works for any `n : ℕ`.

## References

* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*](bourbaki1968) plates I -- IV
* [J. Humphreys, *Introduction to Lie Algebras and Representation Theory*] Chapter 11

## Tags

cartan matrix, classical lie algebra, dynkin diagram
-/

@[expose] public section

namespace CartanMatrix

open Matrix

/-- The Cartan matrix of type Aₙ₋₁ (rank n-1, corresponding to sl(n)).

The Dynkin diagram is:
```
o --- o --- o --- ... --- o
1     2     3           n-1
```

For `n ≥ 2`, this gives the standard tridiagonal Cartan matrix with 2 on diagonal
and -1 on the super/sub-diagonals.
-/
def A (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j =>
    if i = j then 2
    else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1
    else 0

/-- The Cartan matrix of type Bₙ (rank n, corresponding to so(2n+1)).

The Dynkin diagram is:
```
o --- o --- o --- ... --- o ==>= o
1     2     3           n-1      n
```

The double arrow points toward the short root (last node).
-/
def B (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j =>
    if i = j then 2
    else if i.val + 1 = j.val then
      if j.val = n - 1 then -2 else -1  -- A_{n-1, n} = -2 (1-indexed)
    else if j.val + 1 = i.val then -1
    else 0

/-- The Cartan matrix of type Cₙ (rank n, corresponding to sp(2n)).

The Dynkin diagram is:
```
o --- o --- o --- ... --- o =<== o
1     2     3           n-1      n
```

The double arrow points toward the long root (second-to-last node).
-/
def C (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j =>
    if i = j then 2
    else if i.val + 1 = j.val then -1
    else if j.val + 1 = i.val then
      if i.val = n - 1 then -2 else -1  -- A_{n, n-1} = -2 (1-indexed)
    else 0

/-- The Cartan matrix of type Dₙ (rank n, corresponding to so(2n)).

The Dynkin diagram is:
```
                    o n-1
                   /
o --- o --- ... --- o
1     2           n-2 \
                       o n
```

This requires `n ≥ 4` for a proper D-type. For smaller n, the matrix still computes
but should be considered degenerate.
-/
def D (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j =>
    if i = j then 2
    -- Standard chain connections (1 to n-3)
    else if i.val + 1 = j.val ∧ j.val < n - 2 then -1
    else if j.val + 1 = i.val ∧ i.val < n - 2 then -1
    -- Branching: node n-3 connects to both n-2 and n-1
    else if i.val = n - 3 ∧ (j.val = n - 2 ∨ j.val = n - 1) then -1
    else if j.val = n - 3 ∧ (i.val = n - 2 ∨ i.val = n - 1) then -1
    else 0

section Properties

variable (n : ℕ)

/-- Diagonal entries of type A Cartan matrix are 2. -/
theorem A_diag (i : Fin n) : A n i i = 2 := by
  simp [A, Matrix.of_apply]

/-- Diagonal entries of type B Cartan matrix are 2. -/
theorem B_diag (i : Fin n) : B n i i = 2 := by
  simp [B, Matrix.of_apply]

/-- Diagonal entries of type C Cartan matrix are 2. -/
theorem C_diag (i : Fin n) : C n i i = 2 := by
  simp [C, Matrix.of_apply]

/-- Diagonal entries of type D Cartan matrix are 2. -/
theorem D_diag (i : Fin n) : D n i i = 2 := by
  simp [D, Matrix.of_apply]

/-- Type A₁ Cartan matrix is just [2]. -/
theorem A_one : A 1 = !![2] := by
  ext i j
  fin_cases i; fin_cases j; simp [A, Matrix.of_apply]

/-- Type A₂ Cartan matrix. -/
theorem A_two : A 2 = !![2, -1; -1, 2] := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [A, Matrix.of_apply]

/-- Type A₃ Cartan matrix. -/
theorem A_three : A 3 = !![2, -1, 0; -1, 2, -1; 0, -1, 2] := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [A, Matrix.of_apply]

/-- Off-diagonal entries of type A Cartan matrix are non-positive. -/
theorem A_off_diag_nonpos (i j : Fin n) (h : i ≠ j) : A n i j ≤ 0 := by
  simp only [A, Matrix.of_apply]
  split_ifs <;> omega

/-- Off-diagonal entries of type B Cartan matrix are non-positive. -/
theorem B_off_diag_nonpos (i j : Fin n) (h : i ≠ j) : B n i j ≤ 0 := by
  simp only [B, Matrix.of_apply]
  split_ifs <;> omega

/-- Off-diagonal entries of type C Cartan matrix are non-positive. -/
theorem C_off_diag_nonpos (i j : Fin n) (h : i ≠ j) : C n i j ≤ 0 := by
  simp only [C, Matrix.of_apply]
  split_ifs <;> omega

/-- Off-diagonal entries of type D Cartan matrix are non-positive. -/
theorem D_off_diag_nonpos (i j : Fin n) (h : i ≠ j) : D n i j ≤ 0 := by
  simp only [D, Matrix.of_apply]
  split_ifs <;> omega

end Properties

section LieAlgebras

variable (R : Type*) [CommRing R]

/-- The Lie algebra of type Aₙ₋₁, isomorphic to sl(n). -/
abbrev aₙ (n : ℕ) [_hn : NeZero n] :=
  (A n).ToLieAlgebra R

/-- The Lie algebra of type Bₙ, isomorphic to so(2n+1). -/
abbrev bₙ (n : ℕ) [_hn : NeZero n] :=
  (B n).ToLieAlgebra R

/-- The Lie algebra of type Cₙ, isomorphic to sp(2n). -/
abbrev cₙ (n : ℕ) [_hn : NeZero n] :=
  (C n).ToLieAlgebra R

/-- The Lie algebra of type Dₙ, isomorphic to so(2n). Requires n ≥ 4 for non-degenerate behavior. -/
abbrev dₙ (n : ℕ) [_hn : NeZero n] :=
  (D n).ToLieAlgebra R

end LieAlgebras

end CartanMatrix
