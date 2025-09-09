/-
Copyright (c) 2024 Newell Jensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Newell Jensen, Mitchell Lee
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Coxeter matrices

Let us say that a matrix (possibly an infinite matrix) is a *Coxeter matrix* (`CoxeterMatrix`) if
its entries are natural numbers, it is symmetric, its diagonal entries are equal to 1, and its
off-diagonal entries are not equal to 1. In this file, we define Coxeter matrices and provide some
ways of constructing them.

We also define the Coxeter matrices `CoxeterMatrix.Aₙ` (`n : ℕ`), `CoxeterMatrix.Bₙ` (`n : ℕ`),
`CoxeterMatrix.Dₙ` (`n : ℕ`), `CoxeterMatrix.I₂ₘ` (`m : ℕ`), `CoxeterMatrix.E₆`, `CoxeterMatrix.E₇`,
`CoxeterMatrix.E₈`, `CoxeterMatrix.F₄`, `CoxeterMatrix.G₂`, `CoxeterMatrix.H₃`, and
`CoxeterMatrix.H₄`. Up to reindexing, these are exactly the Coxeter matrices whose corresponding
Coxeter group (`CoxeterMatrix.coxeterGroup`) is finite and irreducible, although we do not prove
that in this file.

## Implementation details

In some texts on Coxeter groups, each entry $M_{i,i'}$ of a Coxeter matrix can be either a
positive integer or $\infty$. In our treatment of Coxeter matrices, we use the value $0$ instead of
$\infty$. This will turn out to have some fortunate consequences when defining the Coxeter group of
a Coxeter matrix and the standard geometric representation of a Coxeter group.

## Main definitions

* `CoxeterMatrix` : The type of symmetric matrices of natural numbers, with rows and columns
  indexed by a type `B`, whose diagonal entries are equal to 1 and whose off-diagonal entries are
  not equal to 1.
* `CoxeterMatrix.reindex` : Reindexes a Coxeter matrix by a bijection on the index type.
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

## References

* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*](bourbaki1968) chapter IV
  pages 4--5, 13--15

* [J. Baez, *Coxeter and Dynkin Diagrams*](https://math.ucr.edu/home/baez/twf_dynkin.pdf)

-/

/-- A *Coxeter matrix* is a symmetric matrix of natural numbers whose diagonal entries are equal to
1 and whose off-diagonal entries are not equal to 1. -/
@[ext]
structure CoxeterMatrix (B : Type*) where
  /-- The underlying matrix of the Coxeter matrix. -/
  M : Matrix B B ℕ
  isSymm : M.IsSymm := by decide
  diagonal i : M i i = 1 := by decide
  off_diagonal i i' : i ≠ i' → M i i' ≠ 1 := by decide

namespace CoxeterMatrix

variable {B : Type*}

/-- A Coxeter matrix can be coerced to a matrix. -/
instance : CoeFun (CoxeterMatrix B) fun _ ↦ (Matrix B B ℕ) := ⟨M⟩

variable {B' : Type*} (e : B ≃ B') (M : CoxeterMatrix B)

attribute [simp] diagonal

theorem symmetric (i i' : B) : M i i' = M i' i := M.isSymm.apply i' i

/-- The Coxeter matrix formed by reindexing via the bijection `e : B ≃ B'`. -/
protected def reindex : CoxeterMatrix B' where
  M := Matrix.reindex e e M
  isSymm := M.isSymm.submatrix _
  diagonal i := M.diagonal (e.symm i)
  off_diagonal i i' h := M.off_diagonal (e.symm i) (e.symm i') (e.symm.injective.ne h)

theorem reindex_apply (i i' : B') : M.reindex e i i' = M (e.symm i) (e.symm i') := rfl

variable (n : ℕ)

/-- The Coxeter matrix of type Aₙ.

The corresponding Coxeter-Dynkin diagram is:
```
    o --- o --- o ⬝ ⬝ ⬝ ⬝ o --- o
```
-/
def Aₙ : CoxeterMatrix (Fin n) where
  M := Matrix.of fun i j : Fin n ↦
    if i = j then 1
      else (if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then 3 else 2)
  isSymm := by unfold Matrix.IsSymm; aesop
  diagonal := by simp
  off_diagonal := by aesop

/-- The Coxeter matrix of type Bₙ.

The corresponding Coxeter-Dynkin diagram is:
```
       4
    o --- o --- o ⬝ ⬝ ⬝ ⬝ o --- o
```
-/
def Bₙ : CoxeterMatrix (Fin n) where
  M := Matrix.of fun i j : Fin n ↦
    if i = j then 1
      else (if i = n - 1 ∧ j = n - 2 ∨ j = n - 1 ∧ i = n - 2 then 4
        else (if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then 3 else 2))
  isSymm := by unfold Matrix.IsSymm; aesop
  diagonal := by simp
  off_diagonal := by aesop

/-- The Coxeter matrix of type Dₙ.

The corresponding Coxeter-Dynkin diagram is:
```
    o
     \
      o --- o ⬝ ⬝ ⬝ ⬝ o --- o
     /
    o
```
-/
def Dₙ : CoxeterMatrix (Fin n) where
  M := Matrix.of fun i j : Fin n ↦
    if i = j then 1
      else (if i = n - 1 ∧ j = n - 3 ∨ j = n - 1 ∧ i = n - 3 then 3
        else (if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then 3 else 2))
  isSymm := by unfold Matrix.IsSymm; aesop
  diagonal := by simp
  off_diagonal := by aesop

/-- The Coxeter matrix of type I₂(m).

The corresponding Coxeter-Dynkin diagram is:
```
     m + 2
    o --- o
```
-/
def I₂ₘ (m : ℕ) : CoxeterMatrix (Fin 2) where
  M := Matrix.of fun i j => if i = j then 1 else m + 2
  isSymm := by unfold Matrix.IsSymm; aesop
  diagonal := by simp
  off_diagonal := by simp

/-- The Coxeter matrix of type E₆.

The corresponding Coxeter-Dynkin diagram is:
```
                o
                |
    o --- o --- o --- o --- o
```
-/
def E₆ : CoxeterMatrix (Fin 6) where
  M := !![1, 2, 3, 2, 2, 2;
          2, 1, 2, 3, 2, 2;
          3, 2, 1, 3, 2, 2;
          2, 3, 3, 1, 3, 2;
          2, 2, 2, 3, 1, 3;
          2, 2, 2, 2, 3, 1]

/-- The Coxeter matrix of type E₇.

The corresponding Coxeter-Dynkin diagram is:
```
                o
                |
    o --- o --- o --- o --- o --- o
```
-/
def E₇ : CoxeterMatrix (Fin 7) where
  M := !![1, 2, 3, 2, 2, 2, 2;
          2, 1, 2, 3, 2, 2, 2;
          3, 2, 1, 3, 2, 2, 2;
          2, 3, 3, 1, 3, 2, 2;
          2, 2, 2, 3, 1, 3, 2;
          2, 2, 2, 2, 3, 1, 3;
          2, 2, 2, 2, 2, 3, 1]

/-- The Coxeter matrix of type E₈.

The corresponding Coxeter-Dynkin diagram is:
```
                o
                |
    o --- o --- o --- o --- o --- o --- o
```
-/
def E₈ : CoxeterMatrix (Fin 8) where
  M := !![1, 2, 3, 2, 2, 2, 2, 2;
          2, 1, 2, 3, 2, 2, 2, 2;
          3, 2, 1, 3, 2, 2, 2, 2;
          2, 3, 3, 1, 3, 2, 2, 2;
          2, 2, 2, 3, 1, 3, 2, 2;
          2, 2, 2, 2, 3, 1, 3, 2;
          2, 2, 2, 2, 2, 3, 1, 3;
          2, 2, 2, 2, 2, 2, 3, 1]

/-- The Coxeter matrix of type F₄.

The corresponding Coxeter-Dynkin diagram is:
```
             4
    o --- o --- o --- o
```
-/
def F₄ : CoxeterMatrix (Fin 4) where
  M := !![1, 3, 2, 2;
          3, 1, 4, 2;
          2, 4, 1, 3;
          2, 2, 3, 1]

/-- The Coxeter matrix of type G₂.

The corresponding Coxeter-Dynkin diagram is:
```
       6
    o --- o
```
-/
def G₂ : CoxeterMatrix (Fin 2) where
  M := !![1, 6;
          6, 1]

/-- The Coxeter matrix of type H₃.

The corresponding Coxeter-Dynkin diagram is:
```
       5
    o --- o --- o
```
-/
def H₃ : CoxeterMatrix (Fin 3) where
  M := !![1, 3, 2;
          3, 1, 5;
          2, 5, 1]

/-- The Coxeter matrix of type H₄.

The corresponding Coxeter-Dynkin diagram is:
```
       5
    o --- o --- o --- o
```
-/
def H₄ : CoxeterMatrix (Fin 4) where
  M := !![1, 3, 2, 2;
          3, 1, 3, 2;
          2, 3, 1, 5;
          2, 2, 5, 1]

end CoxeterMatrix
