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

* An *Equidecomposition* of `A` and `B` is typically defined as a finite partition of `A` together
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

* We introduce a non-standard predicate, `DecompOn`, to state that a function satisfies the main
  combinatorial property of equidecompositions, even if it is not injective or surjective.

## TODO

* Prove that if two sets embeddidecompose into eachother, they are equidecomposable (Schroeder-Bernstein type theorem)
* Define embeddidecomposability as a Preorder on sets and prove that its induced equivalence relation is equidecomposability.
* Prove the definition of equidecomposition used here is equivalent to the more familiar one using partitions.

-/

variable {X G : Type*} {A B C: Set X}

open Function Set Pointwise PartialEquiv

namespace Equidecomp

section SMul

variable [SMul G X]

--Should this be private?
/-- Let `G` act on a space `X` and `A : Set X`. We say `f : X → X` is a `DecompOn` `A`
as witnessed by some `S : Finset G` if for all `a ∈ A`, the value `f a` can be obtained
by applying some element of `S` to `a` instead.

More familiarly, the restriction of `f` to `A` is the result of partitioning `A` into finitely many
pieces, then applying a single element of `G` to each piece. -/
def DecompOn (f : X → X) (A : Set X) (S : Finset G) : Prop :=  ∀ a ∈ A, ∃ g ∈ S, f a = g • a

variable (X G)

/-- Let `G` act on a space `X`. An `Equidecomposition` with respect to `X` and `G` is a partial
bijection `f : PartialEquiv X X` with the property that for some set `elements : Finset G`,
(which we record), for each `a ∈ f.source`, `f a` can be obtained by applying some `g ∈ elements`
instead. We call `f` an equidecomposition of `f.source` with `f.target`.

More familiarly, `f` is the result of partitioning `f.source` into finitely many pieces,
then applying a single element of `G` to each to get a partition of `f.target`.
-/
structure _root_.Equidecomp extends PartialEquiv X X where
  decomp' : ∃ S : Finset G, DecompOn toFun source S

variable {X G}

/-- Note that `Equidecomp X G` is not `FunLike`. -/
instance : CoeFun (Equidecomp X G) fun _ => X → X := ⟨fun f => f.toFun⟩

/-- A finite set of group elements witnessing that `f` is an equidecomposition. -/
noncomputable
def elements (f : Equidecomp X G) := f.decomp'.choose

theorem decomp (f : Equidecomp X G) : DecompOn f f.source f.elements := f.decomp'.choose_spec

@[simp]
theorem map_source {f : Equidecomp X G} {x : X} (h : x ∈ f.source) :
    f x ∈ f.target := f.toPartialEquiv.map_source h

private theorem ext' {f f' : Equidecomp X G} (h_equiv : f.toPartialEquiv = f'.toPartialEquiv) :
    f = f' := by
  let ⟨_, _, _⟩ := f
  congr

theorem DecompOn.mono {f f' : X → X} {A A' : Set X} {S : Finset G} (h : DecompOn f A S)
    (hA' : A' ⊆ A) (hf' : EqOn f f' A') : DecompOn f' A' S := by
  intro a ha
  rcases h _ (hA' ha) with ⟨γ, γ_mem, hγ⟩
  use γ, γ_mem
  rwa [← hf' ha]

/-- The restriction of an equidecomposition is an equidecomposition. -/
def restr (f : Equidecomp X G) (A : Set X) : Equidecomp X G where
  toPartialEquiv := f.toPartialEquiv.restr A
  decomp' := ⟨f.elements,
    f.decomp.mono (restr_source_subset_source _ _) (by exact fun ⦃x⦄ ↦ congrFun rfl)⟩

@[simp]
theorem restr_toPartialEquiv (f : Equidecomp X G) (A : Set X) :
    (f.restr A).toPartialEquiv = f.toPartialEquiv.restr A := rfl

theorem restr_source (f : Equidecomp X G) (A : Set X) : (f.restr A).source = f.source ∩ A := rfl

theorem restr_source_of_subset (f : Equidecomp X G) {A : Set X} (hA : A ⊆ f.source) :
    (f.restr A).source = A := by rw [restr_source, inter_eq_self_of_subset_right hA]

theorem restr_eq_of_source_subset {f : Equidecomp X G} {A : Set X} (hA : f.source ⊆ A) :
    f.restr A = f :=
  Equidecomp.ext' (by rw [restr_toPartialEquiv, PartialEquiv.restr_eq_of_source_subset hA])

@[simp]
theorem restr_univ (f : Equidecomp X G) : f.restr univ = f :=
  restr_eq_of_source_subset <| subset_univ _

end SMul

open scoped Classical

section Monoid

variable [Monoid G] [MulAction G X]

variable (X G)

/-- The identity function is an equidecomposition of the space with itself. -/
def refl : Equidecomp X G where
  toPartialEquiv := PartialEquiv.refl _
  decomp' := ⟨{1}, by simp [DecompOn]⟩

@[simp]
theorem refl_toPartialEquiv : (Equidecomp.refl X G).toPartialEquiv = PartialEquiv.refl X := rfl

variable {X}

/-- The identity function is an equidecomposition of any set with itself. -/
def reflSet (A : Set X) : Equidecomp X G := (Equidecomp.refl X G).restr A

theorem reflSet_source (A : Set X) : (reflSet G A).source = A :=
  restr_source_of_subset _ <| subset_univ _

@[simp]
theorem reflSet_toPartialEquiv (A : Set X) :
    (reflSet G A).toPartialEquiv = PartialEquiv.ofSet A := by
  ext <;> try rfl
  rw [reflSet_source, ofSet_source]

theorem reflSet_target (A : Set X) : (reflSet G A).target = A := by
  rw [reflSet_toPartialEquiv, ofSet_target]

variable {G}

theorem DecompOn.comp' {g f : X → X} {B A : Set X} {T S : Finset G}
    (hg : DecompOn g B T) (hf : DecompOn f A S) : DecompOn (g ∘ f) (A ∩ f ⁻¹' B) (T * S)  := by
  intro _ ⟨aA, aB⟩
  rcases hf _ aA with ⟨γ, γ_mem, hγ⟩
  rcases hg _ aB with ⟨δ, δ_mem, hδ⟩
  use δ * γ, Finset.mul_mem_mul δ_mem γ_mem
  rwa [mul_smul, ← hγ]

theorem DecompOn.comp {g f : X → X} {B A : Set X} {T S : Finset G}
    (hg : DecompOn g B T) (hf : DecompOn f A S) (h : MapsTo f A B) :
    DecompOn (g ∘ f) A (T * S)  := by
  rw [left_eq_inter.mpr h]
  exact hg.comp' hf

/-- The composition of two equidecompositions is an equidecomposition.-/
@[trans]
noncomputable def trans (f g : Equidecomp X G) : Equidecomp X G where
  toPartialEquiv := f.toPartialEquiv.trans g.toPartialEquiv
  decomp' := ⟨g.elements * f.elements, g.decomp.comp' f.decomp⟩

@[simp] theorem trans_toPartialEquiv (f g : Equidecomp X G) :
    (f.trans g).toPartialEquiv = f.toPartialEquiv.trans g.toPartialEquiv := rfl

@[simp] theorem coe_trans (f g : Equidecomp X G) : ↑(f.trans g) = g ∘ f := rfl

theorem trans_apply (f g : Equidecomp X G) (x : X) : (f.trans g) x = g (f x) := rfl

end Monoid

section Group

variable [Group G] [MulAction G X]

theorem DecompOn.of_leftInvOn {f g : X → X} {A : Set X} {S : Finset G}
    (hf : DecompOn f A S) (h : LeftInvOn g f A) : DecompOn g (f '' A) S⁻¹ := by
  rintro _ ⟨a, ha, rfl⟩
  rcases hf a ha with ⟨γ, γ_mem, hγ⟩
  use γ⁻¹, Finset.inv_mem_inv γ_mem
  rw [hγ, inv_smul_smul, ← hγ, h ha]


/-- The inverse function of an equidecomposition is an equidecomposition.-/
@[symm]
noncomputable def symm (f : Equidecomp X G) : Equidecomp X G where
  toPartialEquiv := f.toPartialEquiv.symm
  decomp' := ⟨f.elements⁻¹, by
    convert f.decomp.of_leftInvOn f.leftInvOn
    rw [image_source_eq_target, symm_source]⟩

@[simp]
theorem invFun_eq_coe (f : Equidecomp X G) : f.invFun = f.symm := rfl

@[simp]
theorem symm_toPartialEquiv (f : Equidecomp X G) :
    f.symm.toPartialEquiv = f.toPartialEquiv.symm := rfl

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
theorem reflSet_symm (A : Set X) : (reflSet G A).symm = reflSet G A := rfl

end Group

end Equidecomp
