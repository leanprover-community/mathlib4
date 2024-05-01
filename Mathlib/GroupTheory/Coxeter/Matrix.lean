/-
Copyright (c) 2024 Newell Jensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Newell Jensen
-/
import Mathlib.GroupTheory.Coxeter.Basic


/-!
# Coexeter matrices

This file defines some standard Coxeter matrices.

## Main definitions

* `CoxeterMatrix.Aₙ` : Coxeter matrix for the symmetry group of the regular n-simplex.
* `CoxeterMatrix.Bₙ` : Coxeter matrix for the symmetry group of the regular n-hypercube
  and its dual, the regular n-orthoplex (or n-cross-polytope).
* `CoxeterMatrix.Dₙ` : Coxeter matrix for the symmetry group of the n-demicube.
* `CoxeterMatrix.I₂ₘ` : Coxeter matrix for the symmetry group of the regular (m + 2)-gon.
* `CoxeterMatrix.E₆` : Coxeter matrix for the symmetry group of the E₆ root polytope.
* `CoxeterMatrix.E₇` : Coxeter matrix for the symmetry group of the E₇ root polytope.
* `CoxeterMatrix.E₈` : Coxeter matrix for the symmetry group of the E₈ root polytope.
* `CoxeterMatrix.F₄` : Coxeter matrix for the symmetry group of the regular 4-polytope,
  the 24-cell.
* `CoxeterMatrix.G₂` : Coxeter matrix for the symmetry group of the regular hexagon.
* `CoxeterMatrix.H₃` : Coxeter matrix for the symmetry group of the regular dodecahedron
  and icosahedron.
* `CoxeterMatrix.H₄` : Coxeter matrix for the symmetry group of the regular 4-polytopes,
  the 120-cell and 600-cell.

-/

namespace CoxeterMatrix

open Matrix

variable (n : ℕ)

/-- The Coxeter matrix of family A(n).

The corresponding Coxeter-Dynkin diagram is:
```
    o --- o --- o ⬝ ⬝ ⬝ ⬝ o --- o
```
-/
abbrev Aₙ : Matrix (Fin n) (Fin n) ℕ :=
  Matrix.of fun i j : Fin n =>
    if i = j then 1
      else (if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then 3 else 2)

theorem AₙIsCoxeter : IsCoxeter (Aₙ n) where
  symmetric := by
    simp [Matrix.IsSymm]; aesop

/-- The Coxeter matrix of family Bₙ.

The corresponding Coxeter-Dynkin diagram is:
```
       4
    o --- o --- o ⬝ ⬝ ⬝ ⬝ o --- o
```
-/
abbrev Bₙ : Matrix (Fin n) (Fin n) ℕ :=
  Matrix.of fun i j : Fin n =>
    if i = j then 1
      else (if i = n - 1 ∧ j = n - 2 ∨ j = n - 1 ∧ i = n - 2 then 4
        else (if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then 3 else 2))

theorem BₙIsCoxeter : IsCoxeter (Bₙ n) where
  symmetric := by simp [Matrix.IsSymm]; aesop

/-- The Coxeter matrix of family Dₙ.

The corresponding Coxeter-Dynkin diagram is:
```
    o
     \
      o --- o ⬝ ⬝ ⬝ ⬝ o --- o
     /
    o
```
-/
abbrev Dₙ : Matrix (Fin n) (Fin n) ℕ :=
  Matrix.of fun i j : Fin n =>
    if i = j then 1
      else (if i = n - 1 ∧ j = n - 3 ∨ j = n - 1 ∧ i = n - 3 then 3
        else (if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then 3 else 2))

theorem DₙIsCoxeter : IsCoxeter (Dₙ n) where
  symmetric := by simp [Matrix.IsSymm]; aesop

/-- The Coxeter matrix of m-indexed family I₂(m).

The corresponding Coxeter-Dynkin diagram is:
```
     m + 2
    o --- o
```
-/
abbrev I₂ₘ (m : ℕ) : Matrix (Fin 2) (Fin 2) ℕ :=
  Matrix.of fun i j => if i = j then 1 else m + 2

theorem I₂ₘIsCoxeter (m : ℕ) : IsCoxeter (I₂ₘ m) where
  symmetric := by simp [Matrix.IsSymm]; aesop

/-- The Coxeter matrix of system E₆.

The corresponding Coxeter-Dynkin diagram is:
```
                o
                |
    o --- o --- o --- o --- o
```
-/
def E₆ : Matrix (Fin 6) (Fin 6) ℕ :=
  !![1, 2, 3, 2, 2, 2;
     2, 1, 2, 3, 2, 2;
     3, 2, 1, 3, 2, 2;
     2, 3, 3, 1, 3, 2;
     2, 2, 2, 3, 1, 3;
     2, 2, 2, 2, 3, 1]

theorem E₆IsCoxeter : IsCoxeter E₆ := by decide

/-- The Coxeter matrix of system E₇.

The corresponding Coxeter-Dynkin diagram is:
```
                o
                |
    o --- o --- o --- o --- o --- o
```
-/
def E₇ : Matrix (Fin 7) (Fin 7) ℕ :=
  !![1, 2, 3, 2, 2, 2, 2;
     2, 1, 2, 3, 2, 2, 2;
     3, 2, 1, 3, 2, 2, 2;
     2, 3, 3, 1, 3, 2, 2;
     2, 2, 2, 3, 1, 3, 2;
     2, 2, 2, 2, 3, 1, 3;
     2, 2, 2, 2, 2, 3, 1]

theorem E₇IsCoxeter : IsCoxeter E₇ := by decide

/-- The Coxeter matrix of system E₈.

The corresponding Coxeter-Dynkin diagram is:
```
                o
                |
    o --- o --- o --- o --- o --- o --- o
```
-/
def E₈ : Matrix (Fin 8) (Fin 8) ℕ :=
  !![1, 2, 3, 2, 2, 2, 2, 2;
     2, 1, 2, 3, 2, 2, 2, 2;
     3, 2, 1, 3, 2, 2, 2, 2;
     2, 3, 3, 1, 3, 2, 2, 2;
     2, 2, 2, 3, 1, 3, 2, 2;
     2, 2, 2, 2, 3, 1, 3, 2;
     2, 2, 2, 2, 2, 3, 1, 3;
     2, 2, 2, 2, 2, 2, 3, 1]

theorem E₈IsCoxeter : IsCoxeter E₈ := by decide

/-- The Coxeter matrix of system F₄.

The corresponding Coxeter-Dynkin diagram is:
```
             4
    o --- o --- o --- o
```
-/
def F₄ : Matrix (Fin 4) (Fin 4) ℕ :=
  !![1, 3, 2, 2;
     3, 1, 4, 2;
     2, 4, 1, 3;
     2, 2, 3, 1]

theorem F₄IsCoxeter : IsCoxeter F₄ := by decide

/-- The Coxeter matrix of system G₂.

The corresponding Coxeter-Dynkin diagram is:
```
       6
    o --- o
```
-/
def G₂ : Matrix (Fin 2) (Fin 2) ℕ :=
  !![1, 6;
     6, 1]

theorem G₂IsCoxeter : IsCoxeter G₂ := by decide

/-- The Coxeter matrix of system H₃.

The corresponding Coxeter-Dynkin diagram is:
```
       5
    o --- o --- o
```
-/
def H₃ : Matrix (Fin 3) (Fin 3) ℕ :=
  !![1, 3, 2;
     3, 1, 5;
     2, 5, 1]

theorem H₃IsCoxeter : IsCoxeter H₃ := by decide

/-- The Coxeter matrix of system H₄.

The corresponding Coxeter-Dynkin diagram is:
```
       5
    o --- o --- o --- o
```
-/
def H₄ : Matrix (Fin 4) (Fin 4) ℕ :=
  !![1, 3, 2, 2;
     3, 1, 3, 2;
     2, 3, 1, 5;
     2, 2, 5, 1]

theorem H₄IsCoxeter : IsCoxeter H₄ := by decide

end CoxeterMatrix
