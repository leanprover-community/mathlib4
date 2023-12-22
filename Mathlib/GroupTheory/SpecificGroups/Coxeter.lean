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
  presentation corresponding to a Coxeter matrix, i.e. `Matrix.CoxeterGroup M`.
* `IsCoxeterGroup` : A group is a Coxeter group if it is registered in a Coxeter system.

## References

* https://en.wikipedia.org/wiki/Coxeter_group

* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*](bourbaki1968) chapter IV
  pages 13--15

## Tags

coxeter system, coxeter group
-/


universe u

noncomputable section

variable {B : Type*} [DecidableEq B]

variable (M : Matrix B B ℕ)

/-- A matrix `IsCoxeter` if it is a symmetric matrix with diagonal entries equal to one
and off-diagonal entries distinct from one. -/
class Matrix.IsCoxeter : Prop where
  symmetric : M.IsSymm := by aesop
  diagonal : ∀ i : B, M i i = 1 := by aesop
  off_diagonal : ∀ i j : B, i ≠ j → M i j ≠ 1 := by aesop

namespace CoxeterGroup

namespace Relations

/-- The relations corresponding to a Coxeter matrix. -/
def ofMatrix : B × B → FreeGroup B :=
 Function.uncurry fun i j => (FreeGroup.of i * FreeGroup.of j) ^ M i j

/-- The set of relations corresponding to a Coxeter matrix. -/
def toSet : Set (FreeGroup B) :=
  Set.range <| ofMatrix M

end Relations

end CoxeterGroup

/-- The group presentation corresponding to a Coxeter matrix. -/
def Matrix.CoxeterGroup := PresentedGroup <| CoxeterGroup.Relations.toSet M

instance : Group (Matrix.CoxeterGroup M) := by
  exact QuotientGroup.Quotient.group _

namespace CoxeterGroup

def of (b : B) : Matrix.CoxeterGroup M := by
  unfold Matrix.CoxeterGroup
  exact PresentedGroup.of b

end CoxeterGroup

/-- A Coxeter system `CoxeterSystem W` is a structure recording the isomorphism between
a group `W` and the group presentation corresponding to a Coxeter matrix. Equivalently, this can
be seen as a list of generators of `W` parameterized by the underlying type of `M`, which
satisfy the relations of the Coxeter matrix `M`. -/
structure CoxeterSystem (W : Type*) [Group W]  where
  /-- `CoxeterSystem.ofMulEquiv` constructs a Coxeter system given an equivalence with the group
  presentation corresponding to a Coxeter matrix `M`. -/
  ofMulEquiv ::
    /-- `mulEquiv` is the isomorphism between the group `W` and the group presentation
    corresponding to a Coxeter matrix `M`. -/
    mulEquiv : W ≃* Matrix.CoxeterGroup M

/-- Coxeter system of type `M` on the group `M.CoxeterGroup`. -/
def Matrix.coxeterSystemCoxeterGroup : CoxeterSystem M M.CoxeterGroup :=
  CoxeterSystem.ofMulEquiv (MulEquiv.refl _)

/-- A group is a Coxeter group if it is registered in a Coxeter system
 for some Coxeter matrix `M`. -/
class IsCoxeterGroup (W : Type u) [Group W] : Prop where
  nonempty_system : ∃ (B : Type u), ∃ (M : Matrix B B ℕ),
    M.IsCoxeter ∧ Nonempty (CoxeterSystem M W)

namespace CoxeterSystem

open Matrix

variable {B B' W H : Type*} [Group W] [Group H]

variable {M : Matrix B B ℕ} [M.IsCoxeter]

instance funLike : FunLike (CoxeterSystem M W) B (fun _ => W) where
  coe cs := fun b => cs.mulEquiv.symm (.of b)
  coe_injective' := by
    rintro ⟨cs⟩ ⟨cs'⟩ hcs'
    have H : (cs.symm : CoxeterGroup M →* W) = (cs'.symm : CoxeterGroup M →* W) := by
      unfold CoxeterGroup
      ext i; exact congr_fun hcs' i
    have : cs.symm = cs'.symm := by ext x; exact FunLike.congr_fun H x
    rw [ofMulEquiv.injEq, ← MulEquiv.symm_symm cs, ← MulEquiv.symm_symm cs', this]

@[simp] lemma mulEquiv_apply_coe (cs : CoxeterSystem M W) (b : B) :
    cs.mulEquiv (cs b) = .of b :=
  (MulEquiv.eq_symm_apply cs.mulEquiv).mp rfl

/-- The canonical Coxeter system of the Coxeter group over `X`. -/
def ofCoxeterGroup (X : Type*) (D : Matrix X X ℕ) : CoxeterSystem D (CoxeterGroup D) :=
  ofMulEquiv (MulEquiv.refl _)

@[simp] lemma ofCoxeterGroup_apply {X : Type*} (D : Matrix X X ℕ) (x : X) :
    CoxeterSystem.ofCoxeterGroup X D x = CoxeterGroup.of D x :=
  rfl

@[simp]
lemma map_relations_eq_reindex_relations (e : B ≃ B') :
    (FreeGroup.freeGroupCongr e) '' CoxeterGroup.Relations.toSet M =
    CoxeterGroup.Relations.toSet (reindex e e M) := by
  simp [CoxeterGroup.Relations.toSet, CoxeterGroup.Relations.ofMatrix]
  apply le_antisymm
  · rw [Set.le_iff_subset]; intro _
    simp only [Set.mem_image, Set.mem_range, Prod.exists, Function.uncurry_apply_pair,
      forall_exists_index, and_imp]
    intro _ hb b _ heq; rw [← heq]
    use (e hb); use (e b); aesop
  · rw [Set.le_iff_subset]; intro hb'
    simp only [Set.mem_range, Prod.exists, Function.uncurry_apply_pair, Set.mem_image,
      forall_exists_index]
    intro b1' b2' heq; rw [← heq]
    use ((FreeGroup.freeGroupCongr e).symm hb')
    exact ⟨by use (e.symm b1'); use (e.symm b2'); aesop, by aesop⟩

/-- Coxeter groups of isomorphic types types are isomorphic. -/
def equivCoxeterGroup (e : B ≃ B') : CoxeterGroup M ≃* CoxeterGroup (reindex e e M) := by
  simp [CoxeterGroup]
  have := PresentedGroup.equivPresentedGroup (rels := CoxeterGroup.Relations.toSet M) e
  rwa [@map_relations_eq_reindex_relations B B' M e] at this

/-- Reindex a Coxeter system through a bijection of the indexing sets. -/
protected def reindex (cs : CoxeterSystem M W) (e : B ≃ B') :
    CoxeterSystem (reindex e e M) W :=
  ofMulEquiv (cs.mulEquiv.trans (equivCoxeterGroup e))

@[simp]
lemma reindex_apply (cs : CoxeterSystem M W) (e : B ≃ B') (b : B') :
    cs.reindex e b = cs (e.symm b) :=
  rfl

/-- Pushing a Coxeter system through a group isomorphism. -/
protected def map (cs : CoxeterSystem M W) (e : W ≃* H) : CoxeterSystem M H :=
  ofMulEquiv (e.symm.trans cs.mulEquiv)

@[simp]
lemma map_apply (cs : CoxeterSystem M W) (e : W ≃* H) (x : B) : cs.map e x = e (cs x) :=
  rfl

lemma presentedGroup.of_injective :
    Function.Injective (PresentedGroup.of (rels := CoxeterGroup.Relations.toSet M)) := by
  sorry

protected lemma injective (cs : CoxeterSystem M W) : Function.Injective cs :=
  cs.mulEquiv.symm.injective.comp (presentedGroup.of_injective)

lemma isCoxeterGroup (cs : CoxeterSystem M W) : IsCoxeterGroup W := by
  use Set.range cs
  have h₁ := Equiv.ofInjective (↑cs) cs.injective
  use M.submatrix h₁.symm h₁.symm
  rename_i isCoxeter
  exact ⟨IsCoxeter.mk (by simp_all only [isCoxeter.symmetric, IsSymm.submatrix])
    (by intro i; simp_all only [isCoxeter.diagonal, submatrix_apply])
    (by intro i j a; simp_all [isCoxeter.off_diagonal]), ⟨cs.reindex h₁⟩⟩

instance (X : Type*) (D : Matrix X X ℕ) [D.IsCoxeter] : IsCoxeterGroup D.CoxeterGroup :=
  (coxeterSystemCoxeterGroup D).isCoxeterGroup

end CoxeterSystem

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
      else (if i = n - 1 ∨ j = n - 1 then 2 else 3)

instance AₙIsCoxeter : IsCoxeter (Aₙ n) where

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
      else (if i = (1 : ℕ) ∨ j = (1 : ℕ) then 4
        else (if i = n - 1 ∨ j = n - 1 then 2 else 3))

instance BₙIsCoxeter : IsCoxeter (Bₙ n) where

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
      else (if i = (1 : ℕ) ∨ j = (1 : ℕ) then 4
        else (if i = n - 1 ∨ j = n - 1 then 2 else 3))

instance DₙIsCoxeter : IsCoxeter (Dₙ n) where

/-- The Coxeter matrix of m-indexed family I₂(m).

The corresponding Coxeter-Dynkin diagram is:
```
     m + 2
    o --- o
```
-/
abbrev I₂ₘ (m : ℕ) : Matrix (Fin 2) (Fin 2) ℕ :=
  Matrix.of fun i j => if i = j then 1 else m + 2

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
  symmetric := by simp [Matrix.IsSymm]; decide
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
  symmetric := by simp [Matrix.IsSymm]; decide
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
  symmetric := by simp [Matrix.IsSymm]; decide
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
  symmetric := by simp [Matrix.IsSymm]; decide
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
  symmetric := by simp [Matrix.IsSymm]; decide
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
  symmetric := by simp [Matrix.IsSymm]; decide
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
  symmetric := by simp [Matrix.IsSymm]; decide
  diagonal := by decide
  off_diagonal := by decide

end CoxeterMatrix
