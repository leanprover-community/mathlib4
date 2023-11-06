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

* `Matrix.IsCoxeter` : A matrix `IsCoxeter` if it is a symmetric matrix with ones on
  the diagonal and off-diagonal elements are greater than or equal to two.
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

variable (M : Matrix B B ℕ∞)

variable (B)

/-- A matrix `IsCoxeter` if it is a symmetric matrix with ones on the diagonal
and off-diagonal elements are greater than or equal to two. -/
class Matrix.IsCoxeter (M : Matrix B B ℕ∞) : Prop where
  symmetric : M.IsSymm
  diagonal : ∀ i j : B, i = j → M i j = 1
  off_diagonal : ∀ i j : B, i ≠ j → 2 ≤ M i j

namespace CoxeterGroup

variable {B}

namespace Relations

/-- The relation terms corresponding to a Coxeter matrix. -/
def ofMatrix : B × B → FreeGroup B :=
  Function.uncurry fun i j =>
    (FreeGroup.of i * FreeGroup.of j) ^ orderOf (M i j)

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
    repr : Matrix.CoxeterGroup B M ≃* W

/-- A group is a Coxeter group if it is registered in a Coxeter System. -/
class IsCoxeterGroup (W : Type*) [Group W] : Prop where
  nonempty_system : ∃ (M : Matrix B B ℕ∞), M.IsCoxeter ∧ Nonempty (CoxeterSystem B M W)

namespace CoxeterMatrix

variable {m n : ℕ}

/-- The Coxeter matrix of family Aₙ.

The corresponding Coxeter-Dynkin diagram is:
```
    o --- o --- o ⬝ ⬝ ⬝ ⬝ o --- o
```
-/
def AₙAux : (Fin n) → (Fin n) → ℕ∞ :=
  fun i j =>
    if i == j then 1
      else (if i == n - 1 ∨ j == n - 1 then 2 else 3)

def Aₙ : Matrix (Fin n) (Fin n) ℕ∞ :=
  Matrix.of AₙAux

theorem AₙIsCoxeter : Aₙ.IsCoxeter (Fin n) where
  symmetric := by
    unfold Aₙ AₙAux
    aesop
  diagonal := by
    unfold Aₙ AₙAux
    aesop
  off_diagonal := by
    unfold Aₙ AₙAux
    aesop

/-- The Coxeter matrix of family Bₙ.

The corresponding Coxeter-Dynkin diagram is:
```
       4
    o --- o --- o ⬝ ⬝ ⬝ ⬝ o --- o
```
-/
def BₙAux [NeZero n] : (Fin n) → (Fin n) → ℕ∞ :=
  fun i j =>
    if i == j then 1
      else (if i == (1 : Fin n) ∨ (j == (1 : Fin n)) then 4
        else (if i == n - 1 ∨ j == n - 1 then 2 else 3))

def Bₙ [NeZero n] : Matrix (Fin n) (Fin n) ℕ∞ :=
  Matrix.of BₙAux

theorem BₙIsCoxeter [NeZero n] : Bₙ.IsCoxeter (Fin n) where
  symmetric := by
    unfold Bₙ BₙAux
    aesop
  diagonal := by
    unfold Bₙ BₙAux
    aesop
  off_diagonal := by
    unfold Bₙ BₙAux
    intro _ _
    simp [Matrix.IsCoxeter]
    split_ifs <;> aesop

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
def DₙAux [NeZero n] : (Fin n) → (Fin n) → ℕ∞ :=
  fun i j =>
    if i == j then 1
      else (if i == (1 : Fin n) ∨ (j == (1 : Fin n)) then 4
        else (if i == n - 1 ∨ j == n - 1 then 2 else 3))

def Dₙ [NeZero n] : Matrix (Fin n) (Fin n) ℕ∞ :=
  Matrix.of DₙAux

theorem DₙIsCoxeter [NeZero n] : Dₙ.IsCoxeter (Fin n) where
  symmetric := by
    unfold Dₙ DₙAux
    aesop
  diagonal := by
    unfold Dₙ DₙAux
    aesop
  off_diagonal := by
    unfold Dₙ DₙAux
    intro _ _
    simp [Matrix.IsCoxeter]
    split_ifs <;> aesop

/-- The Coxeter matrix of family I₂(m).

The corresponding Coxeter-Dynkin diagram is:
```
       n
    o --- o
```
-/
def I₂ₘAux : (Fin 2) → (Fin 2) → ℕ∞ :=
  fun i j => if i == j then 1 else m

def I₂ₘ : Matrix (Fin 2) (Fin 2) ℕ∞ :=
  Matrix.of @I₂ₘAux m

theorem I₂ₙIsCoxeter (h : 3 ≤ (m : ℕ∞)) : Matrix.IsCoxeter (Fin 2) (@I₂ₘ m) where
  symmetric := by
    unfold I₂ₘ I₂ₘAux
    aesop
  diagonal := by
    unfold I₂ₘ I₂ₘAux
    aesop
  off_diagonal := by
    unfold I₂ₘ I₂ₘAux
    intro _ _
    simp [Matrix.IsCoxeter]
    split_ifs
    · aesop
    · intro _
      calc
        2 ≤ 3 := by simp
        _ ≤ ↑m := h

/-- The Coxeter matrix of system E₆.

The corresponding Coxeter-Dynkin diagram is:
```
                o
                |
    o --- o --- o --- o --- o
```
-/
def E₆ : Matrix (Fin 6) (Fin 6) ℕ∞ :=
  !![1, 2, 3, 2, 2, 2;
     2, 1, 2, 3, 2, 2;
     3, 2, 1, 3, 2, 2;
     2, 3, 3, 1, 3, 2;
     2, 2, 2, 3, 1, 3;
     2, 2, 2, 2, 3, 1]

theorem E₆IsCoxeter : E₆.IsCoxeter (Fin 6) where
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
def E₇ : Matrix (Fin 7) (Fin 7) ℕ∞ :=
  !![1, 2, 3, 2, 2, 2, 2;
     2, 1, 2, 3, 2, 2, 2;
     3, 2, 1, 3, 2, 2, 2;
     2, 3, 3, 1, 3, 2, 2;
     2, 2, 2, 3, 1, 3, 2;
     2, 2, 2, 2, 3, 1, 3;
     2, 2, 2, 2, 2, 3, 1]

theorem E₇IsCoxeter : E₇.IsCoxeter (Fin 7) where
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
def E₈ : Matrix (Fin 8) (Fin 8) ℕ∞ :=
  !![1, 2, 3, 2, 2, 2, 2, 2;
     2, 1, 2, 3, 2, 2, 2, 2;
     3, 2, 1, 3, 2, 2, 2, 2;
     2, 3, 3, 1, 3, 2, 2, 2;
     2, 2, 2, 3, 1, 3, 2, 2;
     2, 2, 2, 2, 3, 1, 3, 2;
     2, 2, 2, 2, 2, 3, 1, 3;
     2, 2, 2, 2, 2, 2, 3, 1]

theorem E₈IsCoxeter : E₈.IsCoxeter (Fin 8) where
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
def F₄ : Matrix (Fin 4) (Fin 4) ℕ∞ :=
  !![1, 3, 2, 2;
     3, 1, 4, 2;
     2, 4, 1, 3;
     2, 2, 3, 1]

theorem F₄IsCoxeter : F₄.IsCoxeter (Fin 4) where
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
def G₂ : Matrix (Fin 2) (Fin 2) ℕ∞ :=
  !![1, 6;
     6, 1]

theorem G₂IsCoxeter : G₂.IsCoxeter (Fin 2) where
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
def H₃ : Matrix (Fin 3) (Fin 3) ℕ∞ :=
  !![1, 3, 2;
     3, 1, 5;
     2, 5, 1]

theorem H₃IsCoxeter : H₃.IsCoxeter (Fin 3) where
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
def H₄ : Matrix (Fin 4) (Fin 4) ℕ∞ :=
  !![1, 3, 2, 2;
     3, 1, 3, 2;
     2, 3, 1, 5;
     2, 2, 5, 1]

theorem H₄IsCoxeter : H₄.IsCoxeter (Fin 4) where
  symmetric := by simp [Matrix.IsSymm]
  diagonal := by decide
  off_diagonal := by decide


end CoxeterMatrix
