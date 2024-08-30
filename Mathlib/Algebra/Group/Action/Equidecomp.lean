/-
Copyright (c) 2024 Felix Weilacher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Weilacher
-/
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Data.Finset.Pointwise.Basic

/-!
# Equidecompositions

This file develops the basic theory of equidecompositions.

## Main Definitions

Let `G` be a group acting on a space `X`, and `A B : Set X`.

* An *Equidecomposition* of `A` and `B` is typically defined as a finite partition of `A` together
  with a finite list of elements of `G` of the same size such that applying each element to the
  matching piece of the partition yields a partition of `B`.

  This yields a bijection `f : A ≃ B` where, given `a : A`, `f a = γ • a` for `γ : G` the group
  element for `a`'s piece of the parition. Reversing this is easy, and so we get an equivalent
  (up to the choice of group elements) definition: an *Equidecomposition* of `A` and `B` is a
  bijection `f : A ≃ B` such that for some `S : Finset G`, `f a ∈ S • a` for all `a`.

  We take this as our definition as it is easier to work with. `Equidecomp G A B` is the
  type of such equidecompositions. TODO: Prove this equivalence

  Finally, we define the notation `A ≃ₑ[G] B` for `Equidecomp G A B`.

* An *Embeddidecomposition* of `A` into `B` is an equidecomposition of `A` with a subset of `B`.
  Equivalently, it is an injection `A ↪ B` with the property above.

  We take this as our definition. `Embeddidecomp G A B` is the type of such equidecompositions.
  For the less trivial direction of the equivalence, see `Embeddidecomp.equidecompRange`.

  Finally, we define the notation `A ↪ₑ[G] B` for `Embeddidecomp G A B`.

## Implementation Notes

* The requirement that `G` be a group is relaxed where possible.

* We introduce a non-standard predicate, `Decomp`, to state that a function satisfies the main
  combinatorial property of equidecompositions, even if it is not injective/surjective. This helps
  unify lemmas about Equi- and Embeddi- decompositions.

-/

variable {X G : Type*} {A B C: Set X}

open Function Set Pointwise

section SMul

variable [SMul G X]

--Should this be private?
/-- Let `G` act on a space `X` and `A B : Set X`. We say `f : A → B` is a `Decomp` function
as witnessed by some `S : Finset G` if for all `a ∈ A`, the value `f a` can be obtained
by applying some element of `S` to `a` instead.

More familiarly, `f` is the result of paritioning `A` into finitely many pieces, then
applying a single element of `G` to each piece. -/
def Decomp (f : A → B) (S : Finset G) : Prop :=  ∀ a : A, ∃ g ∈ S, f a = g • (a : X)

variable (G)

/-- Let `G` act on a space `X` and `A B : Set X`. We say an injective function `f : A → B`
is an *embeddidecomposition* if for some `S : Finset G`, for all `a ∈ A`, the value `f a` can be
obtained by applying some element of `S` to `a` instead.

Equivalently, `f` is an equidecomposition between `A` and a subset of `B`.
See `Embeddidecomp.equidecompRange`. -/
structure Embeddidecomp (A B : Set X) where
  /-- The underlying function-/
  toFun : A → B
  injective' : Injective toFun
  decomp : ∃ S : Finset G, Decomp toFun S

/-- Let `G` act on a space `X` and `A B : Set X`. We say a bijection `f : A → B`
is an *equidecomposition* if for some `S : Finset G`, for all `a ∈ A`, the value `f a` can be
obtained by applying some element of `S` to `a` instead.

More familiarly, `f` is the result of paritioning `A` into finitely many pieces, then applying
a single elementof `G` to each piece to obtain a partition of `B`. TODO: Prove this equivalence.
-/
structure Equidecomp (A B : Set X) extends A ≃ B where
  decomp : ∃ S : Finset G, Decomp toFun S

/-- The type of embeddidecompositions from `A` to `B` with respect to the action by `G`.-/
notation:50 A " ↪ₑ[" G:50 "] " B:50 => Embeddidecomp G A B

/-- The type of equidecompositions from `A` to `B` with respect to the action by `G`.-/
notation:50 A " ≃ₑ[" G:50 "] " B:50 => Equidecomp G A B

variable {G}

instance Embeddidecomp.instFunLike : FunLike (A ↪ₑ[G] B) A B where
  coe f := f.toFun
  coe_injective' f g h := by cases f; cases g; congr;

@[ext] theorem Embeddidecomp.ext {f g : A ↪ₑ[G] B} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

instance Embeddidecomp.instEmbeddingLike : EmbeddingLike (A ↪ₑ[G] B) A B where
  injective' f := f.injective'

instance Equidecomp.instEquivLike : EquivLike (A ≃ₑ[G] B) A B where
  coe f := f.toEquiv
  inv f := f.toEquiv.symm
  left_inv f := f.toEquiv.left_inv
  right_inv f := f.toEquiv.right_inv
  coe_injective' f g h₁ h₂ := by cases f; cases g; congr; exact EquivLike.coe_injective' _ _ h₁ h₂

@[ext] theorem Equidecomp.ext {f g : A ≃ₑ[G] B} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h

theorem Embeddidecomp.def (f : A ↪ₑ[G] B) : ∃ S : Finset G, Decomp f S := f.decomp

theorem Equidecomp.def (f : A ≃ₑ[G] B) : ∃ S : Finset G, Decomp f S := f.decomp

/-- An equidecomposition is an embeddidecomposition-/
def Equidecomp.embeddidecomp (f : A ≃ₑ[G] B) : A ↪ₑ[G] B where
  toFun := f.toFun
  injective' := EquivLike.injective f
  decomp := f.decomp

theorem Decomp.mono {f : A → B} {S : Finset G} (h : Decomp f S)
    {A' B': Set X} (hA' : A' ⊆ A) (hB' : B' ⊆ B) (f' : A' → B')
    (hf' : ∀ a : A', (inclusion hB') (f' a) = f (inclusion hA' a)) : Decomp f' S := by
  intro a
  rcases h (inclusion hA' a) with ⟨g, gmem, hg⟩
  use g, gmem
  rw [coe_inclusion] at hg
  rw [← hg, ← hf', coe_inclusion]

/-- An embeddidecomposition is an equidecomposition with its range. -/
noncomputable def Embeddidecomp.equidecompRange (f : A ↪ₑ[G] B) :
    A ≃ₑ[G] (range <| Subtype.val ∘ f) where
  toEquiv := Equiv.ofInjective (Subtype.val ∘ f) (Subtype.val_injective.comp f.injective')
  decomp := by
    rcases f.decomp with ⟨S, hS⟩
    refine ⟨S, hS.mono ?_ ?_ _ ?_⟩
    · rfl
    · refine (range_comp_subset_range _ _).trans ?_
      rw [Subtype.range_val]
    intro a
    simp only [Equiv.toFun_as_coe, Equiv.ofInjective_apply, comp_apply, Subtype.map_id, id_eq]
    rfl

end SMul

open scoped Classical

section Monoid

variable [Monoid G] [MulAction G X]

/-- The identity function is an equidecomposition of any set with itself. -/
def Equidecomp.refl (A : Set X) : A ≃ₑ[G] A where
  toEquiv := Equiv.refl A
  decomp := ⟨{1}, by simp [Decomp]⟩

@[simp] theorem Equidecomp.coe_refl (A : Set X) : ↑(Equidecomp.refl A (G := G)) = id := rfl

theorem Decomp.comp  {g : B → C} {f : A → B} {T S : Finset G}
    (hg : Decomp g T) (hf : Decomp f S) : Decomp (g ∘ f) (T * S) := by
  intro a
  rcases hf a with ⟨γ, γ_mem, hγ⟩
  rcases hg (f a) with ⟨δ, δ_mem, hδ⟩
  use δ * γ, Finset.mul_mem_mul δ_mem γ_mem
  rw [mul_smul, ← hγ, ← hδ]
  rfl

/-- The composition of two embeddidecompositions is an embeddidecomposition.-/
def Embeddidecomp.trans (f : A ↪ₑ[G] B) (g : B ↪ₑ[G] C) : A ↪ₑ[G] C where
  toFun := g ∘ f
  injective' := g.injective'.comp f.injective'
  decomp := by
    rcases f.decomp with ⟨S, hS⟩
    rcases g.decomp with ⟨T, hT⟩
    exact ⟨T * S, hT.comp hS⟩

/-- The composition of two equidecompositions is an equidecomposition.-/
def Equidecomp.trans (f : A ≃ₑ[G] B) (g : B ≃ₑ[G] C) : A ≃ₑ[G] C where
  toEquiv := f.toEquiv.trans g.toEquiv
  decomp := by
    rcases f.decomp with ⟨S, hS⟩
    rcases g.decomp with ⟨T, hT⟩
    exact ⟨T * S, hT.comp hS⟩

@[simp] theorem Embeddidecomp.coe_trans (f : A ↪ₑ[G] B) (g : B ↪ₑ[G] C) :
    ↑(f.trans g) = g ∘ f := rfl

@[simp] theorem Equidecomp.coe_trans (f : A ≃ₑ[G] B) (g : B ≃ₑ[G] C) : ↑(f.trans g) = g ∘ f := rfl

end Monoid

section Group

variable [Group G] [MulAction G X]

theorem Decomp.of_rightInverse {f : A → B} {g : B → A} {S : Finset G}
    (hf : Decomp f S) (h : RightInverse g f) : Decomp g S⁻¹ := by
  intro b
  rcases hf (g b) with ⟨γ, γ_mem, hγ⟩
  use γ⁻¹, Finset.inv_mem_inv γ_mem
  apply smul_left_cancel γ
  rw [smul_inv_smul, ← hγ, h]

/-- The inverse function of an equidecomposition is an equidecomposition.-/
def Equidecomp.symm (f : A ≃ₑ[G] B) : B ≃ₑ[G] A where
  toEquiv := f.toEquiv.symm
  decomp := by
    rcases f.decomp with ⟨S, hS⟩
    refine ⟨S⁻¹, hS.of_rightInverse <| Equiv.right_inv' _⟩

end Group
