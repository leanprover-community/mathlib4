/-
Copyright (c) 2024 Newell Jensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Newell Jensen, Mitchell Lee
-/
import Mathlib.Data.Matrix.Notation
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Data.Int.Parity

/-!
# Coxeter systems

This file defines Coxeter systems and Coxeter groups.

Let `B` be a (possibly infinite) type, and let $M = (M_{i,i'})_{i, i' \in B}$ be a matrix
of natural numbers. Further assume that $M$ is a *Coxeter matrix*; that is, $M$ is symmetric and
$M_{i,i'} = 1$ if and only if $i = i'$. The *Coxeter group* associated to $M$ has the presentation
$$\langle \{s_i\}_{i \in B} \vert \{(s_i s_{i'})^{M_{i, i'}}\}_{i, i' \in B} \rangle.$$
The elements $s_i$ are called the *simple reflections* (or *simple generators*) of the
Coxeter group. Note that every simple reflection is an involution.

A *Coxeter system* is a group $W$, together with an isomorphism between $W$ and the Coxeter group
associated to some Coxeter matrix $M$. By abuse of language, we also say that $W$ is a Coxeter
group, and we may speak of the simple reflections $s_i \in W$. The simple reflections of $W$
generate $W$.

The finite Coxeter groups are classified (TODO) as the four infinite families:

* `Aₙ, Bₙ, Dₙ, I₂ₘ`

And the exceptional systems:

* `E₆, E₇, E₈, F₄, G₂, H₃, H₄`

## Implementation details

In this file a Coxeter system, designated as `CoxeterSystem M W`, is implemented as a
structure which effectively records the isomorphism between a group `W` and the corresponding
group presentation derived from a Coxeter matrix `M`.  From another perspective, it serves as
a set of generators for `W`, tailored to the underlying type of `M`, while ensuring compliance
with the relations specified by the Coxeter matrix `M`.

A type class `IsCoxeterGroup` is introduced, for groups that are isomorphic to a group
presentation corresponding to a Coxeter matrix which is registered in a Coxeter system.

In most texts on Coxeter groups, each entry $M_{i,i'}$ of the Coxeter matrix can be either a
positive integer or $\infty$. A value of $\infty$ indicates that there is no relation between the
corresponding simple reflections. In our treatment of Coxeter groups, we use the value $0$ instead
of $\infty$. The Coxeter relation $(s_i s_{i'})^{M_{i, i'}}$ is automatically the identity if
$M_{i, i'} = 0$.

Much of the literature on Coxeter groups conflates the set $S = \{s_i : i \in B\} \subseteq W$ of
simple reflections with the set $B$ that indexes the simple reflections. This is usually permissible
because the simple reflections $s_i$ of any Coxeter group are all distinct (a nontrivial fact that
we do not prove in this file). In contrast, we try not to refer to the set $S$ of simple
reflections unless necessary (such as in the statement of
`CoxeterSystem.submonoid_closure_range_simple`); instead, we state our results in terms of $B$
wherever possible.

## Main definitions

* `Matrix.IsCoxeter` : A matrix `IsCoxeter` if it is a symmetric matrix with diagonal
  entries equal to one and off-diagonal entries distinct from one.
* `Matrix.coxeterGroup` : The group presentation corresponding to a Coxeter matrix.
* `CoxeterSystem` : A structure recording the isomorphism between a group `W` and the
  group presentation corresponding to a Coxeter matrix, i.e. `Matrix.CoxeterGroup M`.
* `IsCoxeterGroup` : A group is a Coxeter group if it is registered in a Coxeter system.
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
* `CoxeterSystem.simpleReflection `: The simple reflection corresponding to an index `i : B`.
* `CoxeterSystem.lift`: Given `f : B → G`, where `G` is a monoid and `f` is a function whose values
satisfy the Coxeter relations, extend it to a monoid homomorphism `f' : W → G` satisfying
`f' (s i) = f i` for all `i`.
* `CoxeterSystem.wordProd`: Given a `List B`, returns the product of the corresponding simple
reflections.
* `CoxeterSystem.alternatingWord`: `CoxeterSystem.alternatingWord i i' m` is the word
(i.e. `List B`) of length `m` that alternates between the letters `i` and `i'`, ending with `i'`.

## References

* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*](bourbaki1968) chapter IV
  pages 4--5, 13--15

* [J. Baez, *Coxeter and Dynkin Diagrams*](https://math.ucr.edu/home/baez/twf_dynkin.pdf)

## TODO

* The canonical map from the type to the Coxeter group `W` is an injection.
* A group `W` registered in a Coxeter system is a Coxeter group.
* A Coxeter group is an instance of `IsCoxeterGroup`.
* Introduce some ways to actually construct some Coxeter groups. For example, given a Coxeter matrix
$M : B \times B \to \mathbb{N}$, a real vector space $V$, a basis $\{\alpha_i : i \in B\}$
and a bilinear form $\langle \cdot, \cdot \rangle \colon V \times V \to \mathbb{R}$ satisfying
$$\langle \alpha_i, \alpha_{i'}\rangle = - \cos(\pi / M_{i,i'}),$$ one can form the subgroup of
$GL(V)$ generated by the reflections in the $\alpha_i$, and it is a Coxeter group. We can use this
to combinatorially describe the Coxeter groups of type $A$, $B$, $D$, and $I$.
* State and prove Matsumoto's theorem.
* Classify the finite Coxeter groups.

## Tags

coxeter system, coxeter group
-/

noncomputable section

open Matrix Function List

variable {B B' : Type*} (M : Matrix B B ℕ) (e : B ≃ B')

/-- The relations corresponding to a Coxeter matrix. -/
def Matrix.coxeterRelation (i i' : B) : FreeGroup B :=
 (FreeGroup.of i * FreeGroup.of i') ^ M i i'

/-- The set of relations corresponding to a Coxeter matrix. -/
def Matrix.coxeterRelationsSet : Set (FreeGroup B) :=
  Set.range <| uncurry M.coxeterRelation

/-- The proposition that `M` is a symmetric matrix with diagonal entries equal to one
and off-diagonal entries distinct from one. -/
structure Matrix.IsCoxeter : Prop where
  symmetric : M.IsSymm := by aesop
  diagonal : ∀ i : B, M i i = 1 := by aesop
  off_diagonal : ∀ i i' : B, i ≠ i' → M i i' ≠ 1 := by aesop

namespace CoxeterMatrix

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

theorem isCoxeter_Aₙ : IsCoxeter (Aₙ n) where
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

theorem isCoxeter_Bₙ : IsCoxeter (Bₙ n) where
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

theorem isCoxeter_Dₙ : IsCoxeter (Dₙ n) where
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

theorem isCoxeter_I₂ₘ (m : ℕ) : IsCoxeter (I₂ₘ m) where
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

theorem isCoxeter_E₆ : IsCoxeter E₆ where
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

theorem isCoxeter_E₇ : IsCoxeter E₇ where
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

theorem isCoxeter_E₈ : IsCoxeter E₈ where
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

theorem isCoxeter_F₄ : IsCoxeter F₄ where
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

theorem isCoxeter_G₂ : IsCoxeter G₂ where
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

theorem isCoxeter_H₃ : IsCoxeter H₃ where
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

theorem isCoxeter_H₄ : IsCoxeter H₄ where
  symmetric := by simp [Matrix.IsSymm]; decide
  diagonal := by decide
  off_diagonal := by decide

end CoxeterMatrix

protected theorem Matrix.IsCoxeter.reindex {M} (hM : M.IsCoxeter) : (reindex e e M).IsCoxeter where
  symmetric := by dsimp only [IsSymm]; rw [transpose_reindex, hM.symmetric]
  diagonal := by intro b; dsimp [reindex]; exact hM.diagonal (e.symm b)
  off_diagonal := by intro i i' hii'; dsimp [reindex]; apply hM.off_diagonal; aesop

theorem Matrix.reindex_isCoxeter_iff : (reindex e e M).IsCoxeter ↔ M.IsCoxeter := by
  constructor
  · intro h
    simpa using h.reindex e.symm
  · exact IsCoxeter.reindex _

/-- The group presentation corresponding to a Coxeter matrix. -/
def Matrix.coxeterGroup := PresentedGroup M.coxeterRelationsSet

instance : Group M.coxeterGroup :=
  QuotientGroup.Quotient.group _

/-- The canonical map from `B` to the Coxeter group with generators `i : B`. The term `b`
is mapped to the equivalence class of the image of `i` in `CoxeterGroup M`. -/
def Matrix.coxeterGroupSimpleReflection (i : B) : M.coxeterGroup := PresentedGroup.of i

theorem Matrix.reindex_coxeterRelationsSet :
    (reindex e e M).coxeterRelationsSet =
    (FreeGroup.freeGroupCongr e) '' M.coxeterRelationsSet := let M' := reindex e e M; calc
  Set.range (uncurry M'.coxeterRelation)
  _ = Set.range ((uncurry M'.coxeterRelation) ∘ Prod.map e e) := by simp [Set.range_comp]
  _ = Set.range ((FreeGroup.freeGroupCongr e) ∘ uncurry M.coxeterRelation) := by
      apply congrArg Set.range
      ext ⟨i, i'⟩
      simp [coxeterRelation, submatrix, M']
  _ = _ := by simp [Set.range_comp]; rfl

/-- Coxeter groups of isomorphic types are isomorphic. -/
def Matrix.reindexCoxeterGroupEquiv : (reindex e e M).coxeterGroup ≃* M.coxeterGroup :=
  (QuotientGroup.congr (Subgroup.normalClosure M.coxeterRelationsSet)
    (Subgroup.normalClosure (reindex e e M).coxeterRelationsSet)
    (FreeGroup.freeGroupCongr e) (by
      rw [reindex_coxeterRelationsSet,
        Subgroup.map_normalClosure _ _ (FreeGroup.freeGroupCongr e).surjective,
        ← MulEquiv.coe_toMonoidHom]
      rfl)).symm

theorem Matrix.reindexCoxeterGroupEquiv_apply_simple (i : B') :
    (M.reindexCoxeterGroupEquiv e) ((reindex e e M).coxeterGroupSimpleReflection i) =
    M.coxeterGroupSimpleReflection (e.symm i) :=
  rfl

theorem Matrix.reindexCoxeterGroupEquiv_symm_apply_simple (i : B) :
    (M.reindexCoxeterGroupEquiv e).symm (M.coxeterGroupSimpleReflection i) =
    (reindex e e M).coxeterGroupSimpleReflection (e i) :=
  rfl

/-- A Coxeter system `CoxeterSystem M W` is a structure recording the isomorphism between
a group `W` and the group presentation corresponding to a Coxeter matrix `M`. -/
@[ext]
structure CoxeterSystem (W : Type*) [Group W] where
  isCoxeter : M.IsCoxeter
  /-- `mulEquiv` is the isomorphism between the group `W` and the group presentation
  corresponding to a Coxeter matrix `M`. -/
  mulEquiv : W ≃* M.coxeterGroup

/-- A group is a Coxeter group if it admits a Coxeter system for some Coxeter matrix `M`. -/
class IsCoxeterGroup (W : Type*) [Group W] : Prop where
  nonempty_system : ∃ (B : Type*), ∃ (M : Matrix B B ℕ), Nonempty (CoxeterSystem M W)

/-- The canonical Coxeter system of the Coxeter group over `M`. -/
def Matrix.IsCoxeter.canonicalCoxeterSystem {M : Matrix B B ℕ} (hM : M.IsCoxeter) :
    CoxeterSystem M M.coxeterGroup where
  isCoxeter := hM
  mulEquiv := .refl _

namespace CoxeterSystem

variable {W H : Type*} [Group W] [Group H] {M} (cs : CoxeterSystem M W)

/-- Reindex a Coxeter system through a bijection of the indexing sets. -/
@[simps]
protected def reindex (e : B ≃ B') : CoxeterSystem (reindex e e M) W where
  isCoxeter := cs.isCoxeter.reindex e
  mulEquiv := cs.mulEquiv.trans (M.reindexCoxeterGroupEquiv e).symm

/-- Pushing a Coxeter system through a group isomorphism. -/
@[simps]
protected def map (e : W ≃* H) : CoxeterSystem M H where
  isCoxeter := cs.isCoxeter
  mulEquiv := e.symm.trans cs.mulEquiv

/-! ### Simple reflections -/

/-- The simple reflection of `W` corresponding to the index `i`. -/
def simpleReflection (i : B) : W := cs.mulEquiv.symm (PresentedGroup.of i)

local prefix:100 "s" => cs.simpleReflection

@[simp]
theorem ofCoxeterGroup_simple (hM : IsCoxeter M) :
    hM.canonicalCoxeterSystem.simpleReflection = M.coxeterGroupSimpleReflection := rfl

@[simp]
theorem reindex_simple {B' : Type*} (e : B ≃ B') (i' : B') :
    (cs.reindex e).simpleReflection i' = s (e.symm i') :=
  rfl

@[simp]
theorem map_simple {W' : Type*} [Group W'] (e : W ≃* W') (i : B) :
    (cs.map e).simpleReflection i = e (s i) :=
  rfl

@[simp] theorem simple_mul_simple_self (i : B) : s i * s i = 1 := by
  dsimp [simpleReflection]
  rw [← _root_.map_mul, PresentedGroup.of, ← QuotientGroup.mk_mul]
  have : (FreeGroup.of i) * (FreeGroup.of i) ∈ M.coxeterRelationsSet := by
    use (i, i)
    rw [uncurry, coxeterRelation, cs.isCoxeter.diagonal i, pow_one]
  have : (QuotientGroup.mk (FreeGroup.of i * FreeGroup.of i) : M.coxeterGroup) = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    exact Subgroup.subset_normalClosure this
  rw [this]
  simp

@[simp] theorem simple_mul_simple_cancel_right {w : W} (i : B) : w * s i * s i = w := by
  simp [mul_assoc]

@[simp] theorem simple_mul_simple_cancel_left {w : W} (i : B) : s i * (s i * w) = w := by
  simp [← mul_assoc]

@[simp] theorem simple_sq (i : B) : s i ^ 2 = 1 := pow_two (s i) ▸ cs.simple_mul_simple_self i

@[simp] theorem inv_simple (i : B) : (s i)⁻¹ = s i :=
  (eq_inv_of_mul_eq_one_right (cs.simple_mul_simple_self i)).symm

@[simp] theorem simple_mul_simple_pow (i i' : B) : (s i * s i') ^ M i i' = 1 := by
  dsimp [simpleReflection]
  rw [← _root_.map_mul, ← map_pow, PresentedGroup.of, PresentedGroup.of,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow]
  have : (FreeGroup.of i * FreeGroup.of i') ^ M i i' ∈ M.coxeterRelationsSet := by
    use (i, i')
    rfl
  have : (QuotientGroup.mk ((FreeGroup.of i * FreeGroup.of i') ^ M i i') : M.coxeterGroup) = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    exact Subgroup.subset_normalClosure this
  rw [this]
  simp

@[simp] theorem simple_mul_simple_pow' (i i' : B) : (s i' * s i) ^ M i i' = 1 :=
  cs.isCoxeter.symmetric.apply i' i ▸ cs.simple_mul_simple_pow i' i

/-- The simple reflections of `W` generate `W` as a group. -/
theorem subgroup_closure_range_simple : Subgroup.closure (Set.range cs.simpleReflection) = ⊤ := by
  have : cs.simpleReflection = cs.mulEquiv.symm ∘ PresentedGroup.of := rfl
  rw [this, Set.range_comp, ← MulEquiv.coe_toMonoidHom, ← MonoidHom.map_closure,
    PresentedGroup.closure_range_of, ← MonoidHom.range_eq_map]
  exact MonoidHom.range_top_of_surjective _ (MulEquiv.surjective _)

/-- The simple reflections of `W` generate `W` as a monoid. -/
theorem submonoid_closure_range_simple : Submonoid.closure (Set.range cs.simpleReflection) = ⊤ := by
  set S := Set.range cs.simpleReflection
  have h₀ : S = S⁻¹ := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      use i
      simp only [inv_simple]
    · rintro ⟨i, hi⟩
      use i
      simpa only [inv_simple, inv_inv] using congrArg (·⁻¹) hi

  have h₁ : S = S ∪ S⁻¹ := by rw [← h₀, Set.union_self]

  rw [h₁, ← Subgroup.closure_toSubmonoid, subgroup_closure_range_simple, Subgroup.top_toSubmonoid]

/-! ### Induction principles for Coxeter systems -/

/-- If `p : W → Prop` holds for all simple reflections, it holds for the identity, and it is
preserved under multiplication, then it holds for all elements of `W`. -/
theorem simple_induction {p : W → Prop} (w : W) (Hs : ∀ i : B, p (s i)) (H1 : p 1)
    (Hmul : ∀ w w' : W, p w → p w' → p (w * w')) : p w := by
  have := cs.submonoid_closure_range_simple.symm ▸ Submonoid.mem_top w
  apply Submonoid.closure_induction (p := p) this
  · rintro x ⟨i, rfl⟩
    exact Hs i
  · exact H1
  · exact Hmul

/-- If `p : W → Prop` holds for the identity and it is preserved under multiplying on the left
by a simple reflection, then it holds for all elements of `W`. -/
theorem simple_induction_left {p : W → Prop} (w : W) (H1 : p 1)
    (Hmul : ∀ (w : W) (i : B), p w → p (s i * w)) : p w := by
  let p' : ((w : W) → w ∈ Submonoid.closure (Set.range cs.simpleReflection) → Prop) :=
    fun w _ ↦ p w
  have := cs.submonoid_closure_range_simple.symm ▸ Submonoid.mem_top w
  apply Submonoid.closure_induction_left (p := p')
  · exact H1
  · rintro _ ⟨i, rfl⟩ y hy h
    exact Hmul y i h
  · exact this

/-- If `p : W → Prop` holds for the identity and it is preserved under multiplying on the right
by a simple reflection, then it holds for all elements of `W`. -/
theorem simple_induction_right {p : W → Prop} (w : W) (H1 : p 1)
    (Hmul : ∀ (w : W) (i : B), p w → p (w * s i)) : p w := by
  let p' : ((w : W) → w ∈ Submonoid.closure (Set.range cs.simpleReflection) → Prop) :=
    fun w _ ↦ p w
  have := cs.submonoid_closure_range_simple.symm ▸ Submonoid.mem_top w
  apply Submonoid.closure_induction_right (p := p')
  · exact H1
  · rintro x hx _ ⟨i, rfl⟩ h
    exact Hmul x i h
  · exact this

/-! ### Homomorphisms from a Coxeter group -/

/-- The proposition that the values of the function `f : B → G` satisfy the Coxeter relations
corresponding to the matrix `M`. -/
def IsLiftable {G : Type*} [Monoid G] (M : Matrix B B ℕ) (f : B → G) : Prop :=
    ∀ i i' : B, (f i * f i') ^ M i i' = 1

private theorem relations_liftable {G : Type*} [Group G] {f : B → G} (hf : IsLiftable M f) :
    ∀ r ∈ M.coxeterRelationsSet, (FreeGroup.lift f) r = 1 := by
  rintro r ⟨⟨i, i'⟩, rfl⟩
  rw [uncurry, coxeterRelation, map_pow, _root_.map_mul, FreeGroup.lift.of, FreeGroup.lift.of]
  exact hf i i'

private def groupLift {G : Type*} [Group G] {f : B → G} (hf : IsLiftable M f) : W →* G :=
  (PresentedGroup.toGroup (relations_liftable hf)).comp cs.mulEquiv.toMonoidHom

private def restrictUnit {G : Type*} [Monoid G] {f : B → G} (hf : IsLiftable M f) (i : B) :
    Gˣ where
  val := f i
  inv := f i
  val_inv := pow_one (f i * f i) ▸ (cs.isCoxeter.diagonal i ▸ hf i i)
  inv_val := pow_one (f i * f i) ▸ (cs.isCoxeter.diagonal i ▸ hf i i)

/-- Extend the function `f : B → G` to a monoid homomorphism
`f' : W → G` satisfying `f' (s i) = f i` for all `i`.
-/
def lift {G : Type*} [Monoid G] {f : B → G} (hf : IsLiftable M f) : W →* G :=
  MonoidHom.comp (Units.coeHom G) (cs.groupLift
    (show ∀ i i' : B, ((cs.restrictUnit hf) i * (cs.restrictUnit hf) i') ^ M i i' = 1 from
      fun i i' ↦ Units.ext (hf i i')))

private theorem toMonoidHom_symm (a : PresentedGroup (M.coxeterRelationsSet)):
    (MulEquiv.toMonoidHom cs.mulEquiv : W →* PresentedGroup (M.coxeterRelationsSet))
    ((MulEquiv.symm cs.mulEquiv) a) = a := calc
  _ = cs.mulEquiv ((MulEquiv.symm cs.mulEquiv) a) := by rfl
  _ = _                                           := by rw [MulEquiv.apply_symm_apply]

theorem lift_apply_simple {G : Type*} [Monoid G] {f : B → G}
    (hf : IsLiftable M f) (i : B) : cs.lift hf (s i) = f i := by
  dsimp only [simpleReflection, lift, groupLift, MonoidHom.comp_apply]
  rw [← MonoidHom.toFun_eq_coe, cs.toMonoidHom_symm (PresentedGroup.of i)]
  simp
  rfl

/-- If two homomorphisms with domain `W` agree on all simple reflections, then they are equal. -/
theorem ext_simple {G : Type*} [Monoid G] {φ₁ φ₂ : W →* G} (h : ∀ i : B, φ₁ (s i) = φ₂ (s i)) :
    φ₁ = φ₂ := by
  apply MonoidHom.eq_of_eqOn_denseM (cs.submonoid_closure_range_simple)
  rintro x ⟨i, rfl⟩
  exact h i

/-- If two Coxeter systems on the same group `W` have the same Coxeter matrix `M : Matrix B B ℕ`
and the same simple reflection map `B → W`, then they are identical. -/
theorem simpleReflection_determines_coxeterSystem :
    Injective (simpleReflection : CoxeterSystem M W → B → W) := by
  intro cs1 cs2 h
  apply CoxeterSystem.ext
  apply MulEquiv.toMonoidHom_injective
  apply cs1.ext_simple
  intro i
  nth_rw 2 [h]
  simp [simpleReflection]

/-! ### Words -/

/-- The product of the simple reflections of `W` corresponding to the indices in `ω`.-/
def wordProd (ω : List B) : W := prod (map cs.simpleReflection ω)

local prefix:100 "π" => cs.wordProd

@[simp] theorem wordProd_nil : π [] = 1 := by simp [wordProd]

theorem wordProd_cons (i : B) (ω : List B) : π (i :: ω) = s i * π ω := by simp [wordProd]

@[simp] theorem wordProd_singleton (i : B) : π ([i]) = s i := by simp [wordProd]

theorem wordProd_concat (i : B) (ω : List B) : π (ω.concat i) = π ω * s i := by simp [wordProd]

theorem wordProd_append (ω ω' : List B) : π (ω ++ ω') = π ω * π ω' := by simp [wordProd]

@[simp] theorem wordProd_reverse (ω : List B) : π (reverse ω) = (π ω)⁻¹ := by
  induction' ω with x ω' ih
  · simp
  · simpa [wordProd_cons, wordProd_append] using ih

theorem wordProd_surjective : Surjective cs.wordProd := by
  intro w
  apply cs.simple_induction_left w
  · use nil
    simp
  · rintro _ i ⟨ω, rfl⟩
    use i :: ω
    rw [wordProd_cons]

/-- The word of length `m` that alternates between `i` and `i'`, ending with `i'`.-/
def alternatingWord (i i' : B) (m : ℕ) : List B :=
  match m with
  | 0    => []
  | m+1  => (alternatingWord i' i m).concat i'

theorem alternatingWord_succ (i i' : B) (m : ℕ) :
    alternatingWord i i' (m + 1) = (alternatingWord i' i m).concat i' := by
  rfl

theorem alternatingWord_succ' (i i' : B) (m : ℕ) :
    alternatingWord i i' (m + 1) = (if Even m then i' else i) :: alternatingWord i i' m := by
  induction' m with m ih generalizing i i'
  · simp [alternatingWord]
  · rw [alternatingWord]
    nth_rw 1 [ih i' i]
    rw [alternatingWord]
    simp [Nat.even_add_one]

@[simp] theorem length_alternatingWord (i i' : B) (m : ℕ) :
    List.length (alternatingWord i i' m) = m := by
  induction' m with m ih generalizing i i'
  · dsimp [alternatingWord]
  · simp [alternatingWord]
    exact ih i' i

theorem prod_alternatingWord_eq_pow (i i' : B) (m : ℕ) :
    π (alternatingWord i i' m) = (if Even m then 1 else s i') * (s i * s i') ^ (m / 2) := by
  induction' m with m ih
  · simp [alternatingWord]
  · rw [alternatingWord_succ', wordProd_cons, ih, Nat.succ_eq_add_one]
    rcases Nat.even_or_odd m with even | odd
    · rcases even with ⟨k, rfl⟩
      ring_nf
      have : Odd (1 + k * 2) := by use k; ring
      simp [← two_mul, Nat.odd_iff_not_even.mp this]
      rw [Nat.add_mul_div_right _ _ (by norm_num : 0 < 2)]
      norm_num
    · rcases odd with ⟨k, rfl⟩
      ring_nf
      have h₁ : Odd (1 + k * 2) := by use k; ring
      have h₂ : Even (2 + k * 2) := by use (k + 1); ring
      simp [Nat.odd_iff_not_even.mp h₁, h₂]
      rw [Nat.add_mul_div_right _ _ (by norm_num : 0 < 2)]
      norm_num
      rw [pow_succ', mul_assoc]

theorem prod_alternatingWord_eq_prod_alternatingWord (i i' : B) (m : ℕ) (hm : m ≤ M i i' * 2) :
    π (alternatingWord i i' m) = π (alternatingWord i' i (M i i' * 2 - m)) := by
  rw [prod_alternatingWord_eq_pow, prod_alternatingWord_eq_pow]
  simp_rw [← Int.even_coe_nat]
  -- Rewrite everything in terms of an integer m' which is equal to m.
  rw [← zpow_natCast, ← zpow_natCast, Int.ofNat_ediv, Int.ofNat_ediv, Int.ofNat_sub hm]
  set m' := (m : ℤ)
  -- The resulting equation holds for all integers m'.
  generalize m' = m'

  rw [Int.ofNat_mul, (by norm_num : (↑(2 : ℕ) : ℤ) = 2)]
  clear hm

  rcases Int.even_or_odd m' with even | odd
  · rcases even with ⟨k, rfl⟩
    ring_nf
    have : Even (k * 2) := by use k; ring
    rw [if_pos this]
    have : Even (-(k * 2) + ↑(M i i') * 2) := by use -k + (M i i'); ring
    rw [if_pos this]
    rw [(by ring : -(k * 2) + ↑(M i i') * 2 = (-k + ↑(M i i')) * 2)]
    rw [Int.mul_ediv_cancel _ (by norm_num), Int.mul_ediv_cancel _ (by norm_num)]
    rw [zpow_add, zpow_natCast]
    rw [simple_mul_simple_pow']
    rw [zpow_neg, ← inv_zpow]
    simp
  · rcases odd with ⟨k, rfl⟩
    ring_nf
    have : ¬Even (1 + k * 2) := by apply Int.odd_iff_not_even.mp; use k; ring
    rw [if_neg this]
    have : ¬Even (-1 - k * 2 + ↑(M i i') * 2) := by
      apply Int.odd_iff_not_even.mp
      use ↑(M i i') - k - 1
      ring
    rw [if_neg this]
    rw [(by ring : -1 - k * 2 + ↑(M i i') * 2 = -1 + (-k + ↑(M i i')) * 2)]
    rw [Int.add_mul_ediv_right _ _ (by norm_num), Int.add_mul_ediv_right _ _ (by norm_num)]
    norm_num
    rw [zpow_add, zpow_add, zpow_natCast]
    rw [simple_mul_simple_pow']
    rw [zpow_neg, ← inv_zpow, zpow_neg, ← inv_zpow]
    simp [← mul_assoc]

end CoxeterSystem
