/-
Copyright (c) 2024 Newell Jensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Newell Jensen, Mitchell Lee
-/
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.Coxeter.Matrix

/-!
# Coxeter groups and Coxeter systems

This file defines Coxeter groups and Coxeter systems.

Let `B` be a (possibly infinite) type, and let $M = (M_{i,i'})_{i, i' \in B}$ be a matrix
of natural numbers. Further assume that $M$ is a *Coxeter matrix* (`CoxeterMatrix`); that is, $M$ is
symmetric and $M_{i,i'} = 1$ if and only if $i = i'$. The *Coxeter group* associated to $M$
(`CoxeterMatrix.group`) has the presentation
$$\langle \{s_i\}_{i \in B} \vert \{(s_i s_{i'})^{M_{i, i'}}\}_{i, i' \in B} \rangle.$$
The elements $s_i$ are called the *simple reflections* (`CoxeterMatrix.simple`) of the Coxeter
group. Note that every simple reflection is an involution.

A *Coxeter system* (`CoxeterSystem`) is a group $W$, together with an isomorphism between $W$ and
the Coxeter group associated to some Coxeter matrix $M$. By abuse of language, we also say that $W$
is a Coxeter group (`IsCoxeterGroup`), and we may speak of the simple reflections $s_i \in W$
(`CoxeterSystem.simple`). We state all of our results about Coxeter groups in terms of Coxeter
systems where possible.

## Implementation details

Much of the literature on Coxeter groups conflates the set $S = \{s_i : i \in B\} \subseteq W$ of
simple reflections with the set $B$ that indexes the simple reflections. This is usually permissible
because the simple reflections $s_i$ of any Coxeter group are all distinct (a nontrivial fact that
we do not prove in this file). In contrast, we try not to refer to the set $S$ of simple
reflections unless necessary; instead, we state our results in terms of $B$ wherever possible.

## Main definitions

* `CoxeterMatrix.group`
* `CoxeterSystem`
* `IsCoxeterGroup`
* `CoxeterSystem.simple` : If `cs` is a Coxeter system on the group `W`, then `cs.simple i` is the
  simple reflection of `W` at the index `i`.

## References

* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*](bourbaki1968) chapter IV
  pages 4--5, 13--15

* [J. Baez, *Coxeter and Dynkin Diagrams*](https://math.ucr.edu/home/baez/twf_dynkin.pdf)

## TODO

* The simple reflections of a Coxeter system are distinct.

## Tags

coxeter system, coxeter group

-/

open Function

/-! ### Coxeter groups -/

namespace CoxeterMatrix

variable {B B' : Type*} (M : CoxeterMatrix B) (e : B ≃ B')

/-- The Coxeter relation associated to a Coxeter matrix $M$ and two indices $i, i' \in B$.
That is, the relation $(s_i s_{i'})^{M_{i, i'}}$, considered as an element of the free group
on $\{s_i\}_{i \in B}$.
If $M_{i, i'} = 0$, then this is the identity, indicating that there is no relation between
$s_i$ and $s_{i'}$. -/
def relation (i i' : B) : FreeGroup B := (FreeGroup.of i * FreeGroup.of i') ^ M i i'

/-- The set of all Coxeter relations associated to the Coxeter matrix $M$. -/
def relationsSet : Set (FreeGroup B) := Set.range <| uncurry M.relation

/-- The Coxeter group associated to a Coxeter matrix $M$; that is, the group
$$\langle \{s_i\}_{i \in B} \vert \{(s_i s_{i'})^{M_{i, i'}}\}_{i, i' \in B} \rangle.$$ -/
protected def Group : Type _ := PresentedGroup M.relationsSet

instance : Group M.Group := QuotientGroup.Quotient.group _

/-- The simple reflection of the Coxeter group `M.group` at the index `i`. -/
def simple (i : B) : M.Group := PresentedGroup.of i

theorem reindex_relationsSet :
    (M.reindex e).relationsSet =
    FreeGroup.freeGroupCongr e '' M.relationsSet := let M' := M.reindex e; calc
  Set.range (uncurry M'.relation)
  _ = Set.range (uncurry M'.relation ∘ Prod.map e e) := by simp [Set.range_comp]
  _ = Set.range (FreeGroup.freeGroupCongr e ∘ uncurry M.relation) := by
      apply congrArg Set.range
      ext ⟨i, i'⟩
      simp [relation, reindex_apply, M']
  _ = _ := by simp [Set.range_comp]; rfl

/-- The isomorphism between the Coxeter group associated to the reindexed matrix `M.reindex e` and
the Coxeter group associated to `M`. -/
def reindexGroupEquiv : (M.reindex e).Group ≃* M.Group :=
  (QuotientGroup.congr (Subgroup.normalClosure M.relationsSet)
    (Subgroup.normalClosure (M.reindex e).relationsSet)
    (FreeGroup.freeGroupCongr e) (by
      rw [reindex_relationsSet,
        Subgroup.map_normalClosure _ _ (FreeGroup.freeGroupCongr e).surjective,
        ← MulEquiv.coe_toMonoidHom]
      rfl)).symm

theorem reindexGroupEquiv_apply_simple (i : B') :
    (M.reindexGroupEquiv e) ((M.reindex e).simple i) = M.simple (e.symm i) := rfl

theorem reindexGroupEquiv_symm_apply_simple (i : B) :
    (M.reindexGroupEquiv e).symm (M.simple i) = (M.reindex e).simple (e i) := rfl

end CoxeterMatrix

/-! ### Coxeter systems -/

section

variable {B : Type*} (M : CoxeterMatrix B)

/-- A Coxeter system `CoxeterSystem M W` is a structure recording the isomorphism between
a group `W` and the Coxeter group associated to a Coxeter matrix `M`. -/
@[ext]
structure CoxeterSystem (W : Type*) [Group W] where
  /-- The isomorphism between `W` and the Coxeter group associated to `M`. -/
  mulEquiv : W ≃* M.Group

/-- A group is a Coxeter group if it admits a Coxeter system for some Coxeter matrix `M`. -/
class IsCoxeterGroup.{u} (W : Type u) [Group W] : Prop where
  nonempty_system : ∃ B : Type u, ∃ M : CoxeterMatrix B, Nonempty (CoxeterSystem M W)

/-- The canonical Coxeter system on the Coxeter group associated to `M`. -/
def CoxeterMatrix.toCoxeterSystem : CoxeterSystem M M.Group := ⟨.refl _⟩

end

namespace CoxeterSystem

open CoxeterMatrix

variable {B B' : Type*} (e : B ≃ B')
variable {W H : Type*} [Group W] [Group H]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

/-- Reindex a Coxeter system through a bijection of the indexing sets. -/
@[simps]
protected def reindex (e : B ≃ B') : CoxeterSystem (M.reindex e) W :=
  ⟨cs.mulEquiv.trans (M.reindexGroupEquiv e).symm⟩

/-- Push a Coxeter system through a group isomorphism. -/
@[simps] protected def map (e : W ≃* H) : CoxeterSystem M H := ⟨e.symm.trans cs.mulEquiv⟩

/-! ### Simple reflections -/

/-- The simple reflection of `W` at the index `i`. -/
def simple (i : B) : W := cs.mulEquiv.symm (PresentedGroup.of i)

@[simp]
theorem _root_.CoxeterMatrix.toCoxeterSystem_simple (M : CoxeterMatrix B) :
    M.toCoxeterSystem.simple = M.simple := rfl

@[simp] theorem reindex_simple (i' : B') : (cs.reindex e).simple i' = cs.simple (e.symm i') := rfl

@[simp] theorem map_simple (e : W ≃* H) (i : B) : (cs.map e).simple i = e (cs.simple i) := rfl

end CoxeterSystem
