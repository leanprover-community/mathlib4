/-
Copyright (c) 2024 Felix Weilacher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Weilacher
-/
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Logic.Equiv.PartialEquiv

/-!
# Equidecompositions

This file develops the basic theory of equidecompositions.

## Main Definitions

Let `G` be a group acting on a space `X`, and `A B : Set X`.

An *equidecomposition* of `A` and `B` is typically defined as a finite partition of `A` together
with a finite list of elements of `G` of the same size such that applying each element to the
matching piece of the partition yields a partition of `B`.

This yields a bijection `f : A ≃ B` where, given `a : A`, `f a = γ • a` for `γ : G` the group
element for `a`'s piece of the partition. Reversing this is easy, and so we get an equivalent
(up to the choice of group elements) definition: an *Equidecomposition* of `A` and `B` is a
bijection `f : A ≃ B` such that for some `S : Finset G`, `f a ∈ S • a` for all `a`.

We take this as our definition as it is easier to work with. It is implemented as an element
`PartialEquiv X X` with source `A` and target `B`.

## Implementation Notes

* Equidecompositions are implemented as elements of `PartialEquiv X X` together with a
  `Finset` of elements of the acting group and a proof that every point in the source is moved
  by an element in the finset.

* The requirement that `G` be a group is relaxed where possible.

* We introduce a non-standard predicate, `IsDecompOn`, to state that a function satisfies the main
  combinatorial property of equidecompositions, even if it is not injective or surjective.

## TODO

* Prove that if two sets embeddidecompose into eachother, they are equidecomposable
  (Schroeder-Bernstein type theorem)
* Define embeddidecomposability as a preorder on sets and prove that its induced equivalence
  relation is equidecomposability.
* Prove the definition of equidecomposition used here is equivalent to the more familiar one
  using partitions.

-/

variable {X G : Type*} {A B C: Set X}

open Function Set Pointwise PartialEquiv

namespace Equidecomp

section SMul

variable [SMul G X]

/-- Let `G` act on a space `X` and `A : Set X`. We say `f : X → X` is a decomposition on `A`
as witnessed by some `S : Finset G` if for all `a ∈ A`, the value `f a` can be obtained
by applying some element of `S` to `a` instead.

More familiarly, the restriction of `f` to `A` is the result of partitioning `A` into finitely many
pieces, then applying a single element of `G` to each piece. -/
def IsDecompOn (f : X → X) (A : Set X) (S : Finset G) : Prop := ∀ a ∈ A, ∃ g ∈ S, f a = g • a

variable (X G)

/-- Let `G` act on a space `X`. An `Equidecomposition` with respect to `X` and `G` is a partial
bijection `f : PartialEquiv X X` with the property that for some set `elements : Finset G`,
(which we record), for each `a ∈ f.source`, `f a` can be obtained by applying some `g ∈ elements`
instead. We call `f` an equidecomposition of `f.source` with `f.target`.

More familiarly, `f` is the result of partitioning `f.source` into finitely many pieces,
then applying a single element of `G` to each to get a partition of `f.target`.
-/
structure _root_.Equidecomp extends PartialEquiv X X where
  decomp' : ∃ S : Finset G, IsDecompOn toFun source S

variable {X G}

/-- Note that `Equidecomp X G` is not `FunLike`. -/
instance : CoeFun (Equidecomp X G) fun _ => X → X := ⟨fun f => f.toFun⟩

/-- A finite set of group elements witnessing that `f` is an equidecomposition. -/
noncomputable
def elements (f : Equidecomp X G) : Finset G := f.decomp'.choose

theorem decomp (f : Equidecomp X G) : IsDecompOn f f.source f.elements := f.decomp'.choose_spec

@[simp]
theorem apply_mem_target {f : Equidecomp X G} {x : X} (h : x ∈ f.source) :
    f x ∈ f.target := f.toPartialEquiv.map_source h

theorem toPartialEquiv_injective : Injective <| toPartialEquiv (X := X) (G := G) := by
  intro ⟨_, _, _⟩ _ _
  congr

theorem IsDecompOn.mono {f f' : X → X} {A A' : Set X} {S : Finset G} (h : IsDecompOn f A S)
    (hA' : A' ⊆ A) (hf' : EqOn f f' A') : IsDecompOn f' A' S := by
  intro a ha
  rw [← hf' ha]
  exact h a (hA' ha)

/-- The restriction of an equidecomposition as an equidecomposition. -/
@[simps!]
def restr (f : Equidecomp X G) (A : Set X) : Equidecomp X G where
  toPartialEquiv := f.toPartialEquiv.restr A
  decomp' := ⟨f.elements,
    f.decomp.mono (source_restr_subset_source _ _) fun _ ↦ congrFun rfl⟩

@[simp]
theorem toPartialEquiv_restr (f : Equidecomp X G) (A : Set X) :
    (f.restr A).toPartialEquiv = f.toPartialEquiv.restr A := rfl

theorem source_restr (f : Equidecomp X G) {A : Set X} (hA : A ⊆ f.source) :
    (f.restr A).source = A := by rw [restr_source, inter_eq_self_of_subset_right hA]

theorem restr_of_source_subset {f : Equidecomp X G} {A : Set X} (hA : f.source ⊆ A) :
    f.restr A = f := by
  apply toPartialEquiv_injective
  rw [toPartialEquiv_restr, PartialEquiv.restr_eq_of_source_subset hA]

@[simp]
theorem restr_univ (f : Equidecomp X G) : f.restr univ = f :=
  restr_of_source_subset <| subset_univ _

end SMul

open scoped Classical

section Monoid

variable [Monoid G] [MulAction G X]

variable (X G)

/-- The identity function is an equidecomposition of the space with itself. -/
@[simps toPartialEquiv]
def refl : Equidecomp X G where
  toPartialEquiv := .refl _
  decomp' := ⟨{1}, by simp [IsDecompOn]⟩

/-@[simp]
theorem refl_toPartialEquiv : (Equidecomp.refl X G).toPartialEquiv = .refl X := rfl-/

variable {X} {G}

theorem IsDecompOn.comp' {g f : X → X} {B A : Set X} {T S : Finset G}
    (hg : IsDecompOn g B T) (hf : IsDecompOn f A S) :
    IsDecompOn (g ∘ f) (A ∩ f ⁻¹' B) (T * S)  := by
  intro _ ⟨aA, aB⟩
  rcases hf _ aA with ⟨γ, γ_mem, hγ⟩
  rcases hg _ aB with ⟨δ, δ_mem, hδ⟩
  use δ * γ, Finset.mul_mem_mul δ_mem γ_mem
  rwa [mul_smul, ← hγ]

theorem IsDecompOn.comp {g f : X → X} {B A : Set X} {T S : Finset G}
    (hg : IsDecompOn g B T) (hf : IsDecompOn f A S) (h : MapsTo f A B) :
    IsDecompOn (g ∘ f) A (T * S)  := by
  rw [left_eq_inter.mpr h]
  exact hg.comp' hf

/-- The composition of two equidecompositions as an equidecomposition. -/
@[simps toPartialEquiv, trans]
noncomputable def trans (f g : Equidecomp X G) : Equidecomp X G where
  toPartialEquiv := f.toPartialEquiv.trans g.toPartialEquiv
  decomp' := ⟨g.elements * f.elements, g.decomp.comp' f.decomp⟩

/-@[simp] theorem trans_toPartialEquiv (f g : Equidecomp X G) :
    (f.trans g).toPartialEquiv = f.toPartialEquiv.trans g.toPartialEquiv := rfl -/

end Monoid

section Group

variable [Group G] [MulAction G X]

theorem IsDecompOn.of_leftInvOn {f g : X → X} {A : Set X} {S : Finset G}
    (hf : IsDecompOn f A S) (h : LeftInvOn g f A) : IsDecompOn g (f '' A) S⁻¹ := by
  rintro _ ⟨a, ha, rfl⟩
  rcases hf a ha with ⟨γ, γ_mem, hγ⟩
  use γ⁻¹, Finset.inv_mem_inv γ_mem
  rw [hγ, inv_smul_smul, ← hγ, h ha]

/-- The inverse function of an equidecomposition as an equidecomposition. -/
@[symm, simps toPartialEquiv]
noncomputable def symm (f : Equidecomp X G) : Equidecomp X G where
  toPartialEquiv := f.toPartialEquiv.symm
  decomp' := ⟨f.elements⁻¹, by
    convert f.decomp.of_leftInvOn f.leftInvOn
    rw [image_source_eq_target, symm_source]⟩

theorem map_target {f : Equidecomp X G} {x : X} (h : x ∈ f.target) :
    f.symm x ∈ f.source := f.toPartialEquiv.map_target h

@[simp]
theorem left_inv {f : Equidecomp X G} {x : X} (h : x ∈ f.source) :
    f.toPartialEquiv.symm (f x) = x := f.toPartialEquiv.left_inv h

@[simp]
theorem right_inv {f : Equidecomp X G} {x : X} (h : x ∈ f.target) :
    f (f.toPartialEquiv.symm x) = x := f.toPartialEquiv.right_inv h

@[simp]
theorem symm_symm (f : Equidecomp X G) : f.symm.symm = f := rfl

@[simp]
theorem refl_symm : (refl X G).symm = refl X G := rfl

@[simp]
theorem restr_refl_symm (A : Set X) :
    ((Equidecomp.refl X G).restr A).symm = (Equidecomp.refl X G).restr A := rfl

end Group

end Equidecomp
