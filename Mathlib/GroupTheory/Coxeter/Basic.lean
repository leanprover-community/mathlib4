/-
Copyright (c) 2024 Newell Jensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Newell Jensen
-/
import Mathlib.Data.Matrix.Notation
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Coxeter Systems

This file defines Coxeter systems and Coxeter groups.

A Coxeter system is a pair `(W, S)` where `W` is a group generated by a set of
reflections (involutions) `S = {s₁,s₂,...,sₙ}`, subject to relations determined
by a Coxeter matrix `M = (mᵢⱼ)`.  The Coxeter matrix is a symmetric matrix with
entries `mᵢⱼ` representing the order of the product `sᵢsⱼ` for `i ≠ j` and `mᵢᵢ = 1`.

When `(W, S)` is a Coxeter system, one also says, by abuse of language, that `W` is a
Coxeter group.  A Coxeter group `W` is determined by the presentation
`W = ⟨s₁,s₂,...,sₙ | ∀ i j, (sᵢsⱼ)^mᵢⱼ = 1⟩`, where `1` is the identity element of `W`.

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

## Main definitions

* `Matrix.IsCoxeter` : A matrix `IsCoxeter` if it is a symmetric matrix with diagonal
  entries equal to one and off-diagonal entries distinct from one.
* `Matrix.CoxeterGroup` : The group presentation corresponding to a Coxeter matrix.
* `CoxeterSystem` : A structure recording the isomorphism between a group `W` and the
  group presentation corresponding to a Coxeter matrix, i.e. `Matrix.CoxeterGroup M`.
* `equivCoxeterGroup` : Coxeter groups of isomorphic types are isomorphic.
* `IsCoxeterGroup` : A group is a Coxeter group if it is registered in a Coxeter system.

## References

* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*](bourbaki1968) chapter IV
  pages 4--5, 13--15

* [J. Baez, *Coxeter and Dynkin Diagrams*](https://math.ucr.edu/home/baez/twf_dynkin.pdf)

## TODO

* The canonical map from the type to the Coxeter group `W` is an injection.
* A group `W` registered in a Coxeter system is a Coxeter group.
* A Coxeter group is an instance of `IsCoxeterGroup`.

## Tags

coxeter system, coxeter group
-/


universe u

noncomputable section

variable {B : Type*} [DecidableEq B]
variable (M : Matrix B B ℕ)

/-- A matrix `IsCoxeter` if it is a symmetric matrix with diagonal entries equal to one
and off-diagonal entries distinct from one. -/
@[mk_iff]
structure Matrix.IsCoxeter : Prop where
  symmetric : M.IsSymm := by aesop
  diagonal : ∀ b : B, M b b = 1 := by aesop
  off_diagonal : ∀ b₁ b₂ : B, b₁ ≠ b₂ → M b₁ b₂ ≠ 1 := by aesop

instance [Fintype B] [DecidableEq B] : DecidablePred (Matrix.IsCoxeter (B := B)) :=
  fun M => decidable_of_iff' _ M.isCoxeter_iff

namespace CoxeterGroup

namespace Relations

/-- The relations corresponding to a Coxeter matrix. -/
def ofMatrix : B × B → FreeGroup B :=
 Function.uncurry fun b₁ b₂ => (FreeGroup.of b₁ * FreeGroup.of b₂) ^ M b₁ b₂

/-- The set of relations corresponding to a Coxeter matrix. -/
def toSet : Set (FreeGroup B) :=
  Set.range <| ofMatrix M

end Relations

end CoxeterGroup

/-- The group presentation corresponding to a Coxeter matrix. -/
def Matrix.CoxeterGroup := PresentedGroup <| CoxeterGroup.Relations.toSet M

instance : Group (Matrix.CoxeterGroup M) :=
  QuotientGroup.Quotient.group _

namespace CoxeterGroup

/-- The canonical map from `B` to the Coxeter group with generators `b : B`. The term `b`
is mapped to the equivalence class of the image of `b` in `CoxeterGroup M`. -/
def of (b : B) : Matrix.CoxeterGroup M := PresentedGroup.of b

@[simp]
theorem of_apply (b : B) : of M b = PresentedGroup.of (rels := Relations.toSet M) b :=
  rfl

end CoxeterGroup

/-- A Coxeter system `CoxeterSystem W` is a structure recording the isomorphism between
a group `W` and the group presentation corresponding to a Coxeter matrix. Equivalently, this
can be seen as a list of generators of `W` parameterized by the underlying type of `M`, which
satisfy the relations of the Coxeter matrix `M`. -/
structure CoxeterSystem (W : Type*) [Group W]  where
  /-- `CoxeterSystem.ofMulEquiv` constructs a Coxeter system given an equivalence with the group
  presentation corresponding to a Coxeter matrix `M`. -/
  ofMulEquiv ::
    /-- `mulEquiv` is the isomorphism between the group `W` and the group presentation
    corresponding to a Coxeter matrix `M`. -/
    mulEquiv : W ≃* Matrix.CoxeterGroup M

/-- A group is a Coxeter group if it admits a Coxeter system for some Coxeter matrix `M`. -/
class IsCoxeterGroup (W : Type u) [Group W] : Prop where
  nonempty_system : ∃ (B : Type u), ∃ (M : Matrix B B ℕ),
    M.IsCoxeter ∧ Nonempty (CoxeterSystem M W)

namespace CoxeterSystem

open Matrix

variable {B B' W H : Type*} [Group W] [Group H]
variable {M : Matrix B B ℕ}

/-- A Coxeter system for `W` with Coxeter matrix `M` indexed by `B`, is associated to
a map `B → W` recording the images of the indices. -/
instance funLike : FunLike (CoxeterSystem M W) B W where
  coe cs := fun b => cs.mulEquiv.symm (.of b)
  coe_injective' := by
    rintro ⟨cs⟩ ⟨cs'⟩ hcs'
    have H : (cs.symm : CoxeterGroup M →* W) = (cs'.symm : CoxeterGroup M →* W) := by
      unfold CoxeterGroup
      ext i; exact congr_fun hcs' i
    have : cs.symm = cs'.symm := by ext x; exact DFunLike.congr_fun H x
    rw [ofMulEquiv.injEq, ← MulEquiv.symm_symm cs, ← MulEquiv.symm_symm cs', this]

@[simp]
theorem mulEquiv_apply_coe (cs : CoxeterSystem M W) (b : B) : cs.mulEquiv (cs b) = .of b :=
  cs.mulEquiv.eq_symm_apply.mp rfl

/-- The map sending a Coxeter system to its associated map `B → W` is injective. -/
theorem ext' {cs₁ cs₂ : CoxeterSystem M W} (H : ⇑cs₁ = ⇑cs₂) : cs₁ = cs₂ := DFunLike.coe_injective H

/-- Extensionality rule for Coxeter systems. -/
theorem ext {cs₁ cs₂ : CoxeterSystem M W} (H : ∀ b, cs₁ b = cs₂ b) : cs₁ = cs₂ :=
  ext' <| by ext; apply H

/-- The canonical Coxeter system of the Coxeter group over `X`. -/
def ofCoxeterGroup (X : Type*) (D : Matrix X X ℕ) : CoxeterSystem D (CoxeterGroup D) where
  mulEquiv := .refl _

@[simp]
theorem ofCoxeterGroup_apply {X : Type*} (D : Matrix X X ℕ) (x : X) :
    CoxeterSystem.ofCoxeterGroup X D x = CoxeterGroup.of D x :=
  rfl

theorem map_relations_eq_reindex_relations (e : B ≃ B') :
    (MulEquiv.toMonoidHom (FreeGroup.freeGroupCongr e)) '' CoxeterGroup.Relations.toSet M =
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
    use (FreeGroup.freeGroupCongr e).symm hb'
    exact ⟨by use (e.symm b1'); use (e.symm b2'); aesop, by aesop⟩

/-- Coxeter groups of isomorphic types are isomorphic. -/
def equivCoxeterGroup (e : B ≃ B') : CoxeterGroup M ≃* CoxeterGroup (reindex e e M) :=
  QuotientGroup.congr (Subgroup.normalClosure (CoxeterGroup.Relations.toSet M))
    (Subgroup.normalClosure (CoxeterGroup.Relations.toSet (reindex e e M)))
    (FreeGroup.freeGroupCongr e) (by
      have := Subgroup.map_normalClosure (CoxeterGroup.Relations.toSet M)
        (FreeGroup.freeGroupCongr e).toMonoidHom (FreeGroup.freeGroupCongr e).surjective
      rwa [map_relations_eq_reindex_relations] at this)

theorem equivCoxeterGroup_apply_of (b : B) (M : Matrix B B ℕ) (e : B ≃ B') :
    (equivCoxeterGroup e) (CoxeterGroup.of M b) = CoxeterGroup.of (reindex e e M) (e b) :=
  rfl

theorem equivCoxeterGroup_symm_apply_of (b' : B') (M : Matrix B B ℕ) (e : B ≃ B') :
    (equivCoxeterGroup e).symm (CoxeterGroup.of (reindex e e M) b') =
    CoxeterGroup.of M (e.symm b') :=
  rfl

/-- Reindex a Coxeter system through a bijection of the indexing sets. -/
@[simps]
protected def reindex (cs : CoxeterSystem M W) (e : B ≃ B') :
    CoxeterSystem (reindex e e M) W :=
  ofMulEquiv (cs.mulEquiv.trans (equivCoxeterGroup e))

@[simp]
theorem reindex_apply (cs : CoxeterSystem M W) (e : B ≃ B') (b' : B') :
    cs.reindex e b' = cs (e.symm b') :=
  rfl

/-- Pushing a Coxeter system through a group isomorphism. -/
@[simps]
protected def map (cs : CoxeterSystem M W) (e : W ≃* H) : CoxeterSystem M H :=
  ofMulEquiv (e.symm.trans cs.mulEquiv)

@[simp]
theorem map_apply (cs : CoxeterSystem M W) (e : W ≃* H) (b : B) : cs.map e b = e (cs b) :=
  rfl

end CoxeterSystem
