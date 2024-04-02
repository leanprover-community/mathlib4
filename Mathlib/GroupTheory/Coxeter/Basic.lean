/-
Copyright (c) 2024 Newell Jensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Newell Jensen, Mitchell Lee
-/
import Mathlib.Data.Matrix.Notation
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.LinearAlgebra.Matrix.Symmetric

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

## Implementation details

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

* `Matrix.IsCoxeter` : `IsCoxeter M` means that `M` is a Coxeter matrix; that is, a symmetric matrix
  of natural numbers with diagonal entries equal to 1 and off-diagonal entries not equal to 1.
* `Matrix.coxeterGroup` : `M.coxeterGroup` is the Coxeter group associated to the matrix $M$; that
  is, the group
  $$\langle \{s_i\}_{i \in B} \vert \{(s_i s_{i'})^{M_{i, i'}}\}_{i, i' \in B} \rangle.$$
* `CoxeterSystem` : A structure recording the isomorphism between a group `W` and a
  `M.coxeterGroup` for some Coxeter matrix `M`.
* `IsCoxeterGroup` : `IsCoxeterGroup W` means that there exists a Coxeter matrix `M` such that
  `W` is isomorphic to `M.coxeterGroup`.
* `CoxeterSystem.simpleReflection `: The simple reflection corresponding to an index `i : B`.
* `CoxeterSystem.lift`: Given `f : B → G`, where `G` is a monoid and `f` is a function whose values
satisfy the Coxeter relations, extend it to a monoid homomorphism `f' : W → G` satisfying
`f' (s i) = f i` for all `i`.
* `CoxeterSystem.wordProd`: Given a `List B`, returns the product of the corresponding simple
reflections.

## References

* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*](bourbaki1968) chapter IV
  pages 4--5, 13--15

* [J. Baez, *Coxeter and Dynkin Diagrams*](https://math.ucr.edu/home/baez/twf_dynkin.pdf)

## TODO

* The simple reflections of a Coxeter system are distinct.
* A group `W` registered in a Coxeter system is a Coxeter group.
* A Coxeter group is an instance of `IsCoxeterGroup`.

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
    M.coxeterGroupSimpleReflection (e.symm i) := rfl

theorem Matrix.reindexCoxeterGroupEquiv_symm_apply_simple (i : B) :
    (M.reindexCoxeterGroupEquiv e).symm (M.coxeterGroupSimpleReflection i) =
    (reindex e e M).coxeterGroupSimpleReflection (e i) := rfl

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
def Matrix.IsCoxeter.toCoxeterSystem {M : Matrix B B ℕ} (hM : M.IsCoxeter) :
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

theorem _root_.Matrix.IsCoxeter.toCoxeterSystem_simple (hM : IsCoxeter M) :
    hM.toCoxeterSystem.simpleReflection = M.coxeterGroupSimpleReflection := rfl

@[simp]
theorem reindex_simple {B' : Type*} (e : B ≃ B') (i' : B') :
    (cs.reindex e).simpleReflection i' = s (e.symm i') := rfl

@[simp]
theorem map_simple {W' : Type*} [Group W'] (e : W ≃* W') (i : B) :
    (cs.map e).simpleReflection i = e (s i) := rfl

end CoxeterSystem
