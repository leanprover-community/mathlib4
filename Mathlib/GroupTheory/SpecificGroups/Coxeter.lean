/-
Copyright (c) 2023 Newell Jensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Newell Jensen
-/
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Coxeter Systems

This file defines Coxeter systems.

It introduces a type class `IsCoxeterGroup` for groups that are isomorphic to a group
presentation corresponding to a Coxeter matrix which is registered in a Coxeter system.

The finite Coxeter groups are classified as the four infinite families:

* Aₙ, Bₙ, Dₙ, I₂ₘ

And the six exceptional systems:

* E₆, E₇, E₈, F₄, H₃, H₄

## Main definitions

* `Matrix.IsCoxeter` : A matrix `IsCoxeter` if it is a symmetric matrix with diagonal entries
  equal to one and off-diagonal entries distinct from one.
* `Matrix.CoxeterGroup` : The group presentation corresponding to a Coxeter matrix.
* `CoxeterSystem` : A structure recording the isomorphism between a group `W` and the group
  presentation corresponding to a Coxeter matrix, i.e. `Matrix.CoxeterGroup B M`.
* `IsCoxeterGroup` : A group is a Coxeter group if it is registered in a Coxeter System.

## References

* https://en.wikipedia.org/wiki/Coxeter_group

* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*](bourbaki1968) chapter IV
  pages 13--15

## Tags

coxeter system, coxeter group
-/

noncomputable section

variable {B : Type*} [DecidableEq B]

variable (M : Matrix B B ℕ)

/-- A matrix `IsCoxeter` if it is a symmetric matrix with diagonal entries equal to one
and off-diagonal entries distinct from one. -/
class Matrix.IsCoxeter (M : Matrix B B ℕ) : Prop where
  symmetric : M.IsSymm := by aesop
  diagonal : ∀ i : B, M i i = 1 := by aesop
  off_diagonal : ∀ i j : B, i ≠ j → M i j ≠ 1 := by aesop

namespace CoxeterGroup

namespace Relations

/-- The relation terms corresponding to a Coxeter matrix. -/
def ofMatrix : B × B → FreeGroup B :=
  Function.uncurry fun i j =>
    (FreeGroup.of i * FreeGroup.of j) ^ M i j

/-- The relations corresponding to a Coxeter matrix. -/
def toSet : Set (FreeGroup B) :=
  Set.range <| ofMatrix M

end Relations

end CoxeterGroup

/-- The group presentation corresponding to a Coxeter matrix.

Note that it is defined for any matrix of natural numbers. Its value for non-Coxeter
matrices should be regarded as junk. `IsCoxeterGroup` checks that the matrix `IsCoxeter`. -/
abbrev Matrix.CoxeterGroup := PresentedGroup <| CoxeterGroup.Relations.toSet M

/-- A Coxeter System `CoxeterSystem W` is a structure recording the isomorphism between
a group `W` and the group presentation corresponding to a Coxeter matrix. Equivalently, this can
be seen as a list of generators of `W` parameterized by the underlying type of `M`, which
satisfy the relations of the Coxeter matrix `M`. -/
structure CoxeterSystem (W : Type*) [Group W] where
  /-- `CoxeterSystem.ofRepr` constructs a Coxeter system given an equivalence with the group
  presentation corresponding to a Coxeter matrix `M`. -/
  ofRepr ::
    /-- `repr` is the isomorphism between the group `W` and the group presentation
    corresponding to a Coxeter matrix `M`. -/
    repr : Matrix.CoxeterGroup M ≃* W

/-- A group is a Coxeter group if it is registered in a Coxeter System. -/
class IsCoxeterGroup (W : Type*) [Group W] : Prop where
  nonempty_system : ∃ (M : Matrix B B ℕ), M.IsCoxeter ∧ Nonempty (CoxeterSystem M W)

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
    if i == j then 1
      else (if i == n - 1 ∨ j == n - 1 then 2 else 3)

instance AₙIsCoxeter : IsCoxeter (Aₙ n) where

/-- The Coxeter matrix of family Bₙ.

The corresponding Coxeter-Dynkin diagram is:
```
       4
    o --- o --- o ⬝ ⬝ ⬝ ⬝ o --- o
```
-/
abbrev Bₙ [NeZero n] : Matrix (Fin n) (Fin n) ℕ :=
  Matrix.of fun i j : Fin n =>
    if i == j then 1
      else (if i == 1 ∨ j == 1 then 4
        else (if i == n - 1 ∨ j == n - 1 then 2 else 3))

instance BₙIsCoxeter [NeZero n] : IsCoxeter (Bₙ n) where

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
abbrev Dₙ [NeZero n] : Matrix (Fin n) (Fin n) ℕ :=
  Matrix.of fun i j : Fin n =>
    if i == j then 1
      else (if i == 1 ∨ j == 1 then 4
        else (if i == n - 1 ∨ j == n - 1 then 2 else 3))

instance DₙIsCoxeter [NeZero n] : IsCoxeter (Dₙ n) where

/-- The Coxeter matrix of m-indexed family I₂(m).

The corresponding Coxeter-Dynkin diagram is:
```
     m + 2
    o --- o
```
-/
abbrev I₂ₘ (m : ℕ) : Matrix (Fin 2) (Fin 2) ℕ :=
  Matrix.of fun i j => if i == j then 1 else m + 2

instance I₂ₘIsCoxeter (m : ℕ) : IsCoxeter (I₂ₘ m) where

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

instance E₆IsCoxeter : IsCoxeter E₆ where
  symmetric := by simp [Matrix.IsSymm]
  diagonal := by decide
  off_diagonal := by decide

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

instance E₇IsCoxeter : IsCoxeter E₇ where
  symmetric := by simp [Matrix.IsSymm]
  diagonal := by decide
  off_diagonal := by decide

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

instance E₈IsCoxeter : IsCoxeter E₈ where
  symmetric := by simp [Matrix.IsSymm]
  diagonal := by decide
  off_diagonal := by decide

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

instance F₄IsCoxeter : IsCoxeter F₄ where
  symmetric := by simp [Matrix.IsSymm]
  diagonal := by decide
  off_diagonal := by decide

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

instance G₂IsCoxeter : IsCoxeter G₂ where
  symmetric := by simp [Matrix.IsSymm]
  diagonal := by decide
  off_diagonal := by decide

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

instance H₃IsCoxeter : IsCoxeter H₃ where
  symmetric := by simp [Matrix.IsSymm]
  diagonal := by decide
  off_diagonal := by decide

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

instance H₄IsCoxeter : IsCoxeter H₄ where
  symmetric := by simp [Matrix.IsSymm]
  diagonal := by decide
  off_diagonal := by decide

end CoxeterMatrix
