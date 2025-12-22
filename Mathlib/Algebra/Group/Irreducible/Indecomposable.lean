/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Group.Irreducible.Defs
public import Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Order.Preorder.Finite

/-!
# Indecomposable elements of commutative monoids
-/

@[expose] public section

open Set

variable {ι M : Type*} [Monoid M]

/-- Given a family of elements of a monoid, a member is said to be indecomposable if it cannot be
written as a product of two others in a non-trivial way. -/
@[to_additive (attr := simp) /-- Given a family of elements of an additive monoid, a member is said
to be indecomposable if it cannot be written as a sum of two others in a non-trivial way.-/]
def IsMulIndecomposable (v : ι → M) (s : Set ι) (i : ι) : Prop :=
  i ∈ s ∧ ∀ᵉ (j ∈ s) (k ∈ s), v i = v j * v k → v j = 1 ∨ v k = 1

@[to_additive]
lemma IsMulIndecomposable_id_univ [Subsingleton Mˣ] (x : M) (hx : x ≠ 1) :
    IsMulIndecomposable id univ x ↔ Irreducible x :=
  ⟨fun h ↦ ⟨by simpa, by simpa using h⟩, fun h ↦ by simpa using h.isUnit_or_isUnit⟩

/-- This is [serre1965](Ch. V, §9, Lemma 2) and may be used to prove that crystallographic root
systems have bases. -/
@[to_additive]
lemma Submonoid.closure_image_one_lt_and_isMulIndecomposable [Finite ι]
    {S : Type*} [CommMonoid S] [LinearOrder S] [IsOrderedCancelMonoid S]
    (v : ι → M) (f : M →* S) :
    closure (v '' {i | IsMulIndecomposable v {j | 1 < f (v j)} i}) =
      closure (v '' {i | 1 < f (v i)}) := by
  refine le_antisymm (closure_mono (image_mono <| by aesop)) (closure_le.mpr ?_)
  rintro - ⟨i, hi : 1 < f (v i), rfl⟩
  by_contra hi'
  let t : Set ι := {i | IsMulIndecomposable v {j | 1 < f (v j)} i}
  let s : Set ι := {j | 1 < f (v j) ∧ v j ∉ closure (v '' t)}
  have hne : s.Nonempty := ⟨i, hi, hi'⟩
  clear! i
  obtain ⟨i, hi⟩ := s.toFinite.exists_minimalFor (f ∘ v) s hne
  have ⟨(hi₀ : 1 < f (v i)), (hi₁ : v i ∉ _)⟩ : i ∈ s := hi.prop
  have hi₂ (k : ι) (hk₀ : 1 < f (v k)) (hk₁ : f (v k) < f (v i)) : v k ∈ closure (v '' t) := by
    by_contra hk₂; exact not_le.mpr hk₁ <| hi.le_of_le ⟨hk₀, hk₂⟩ hk₁.le
  have hi₃ : i ∉ t := by contrapose! hi₁; exact subset_closure <| mem_image_of_mem v hi₁
  obtain ⟨j, k, hj, hk, hjk⟩ : ∃ (j k : ι) (hj : 1 < f (v j)) (hk : 1 < f (v k)),
      v i = v j * v k := by
    grind [IsMulIndecomposable]
  have hj' : v j ∈ closure (v '' t) := hi₂ j hj <| by aesop
  have hk' : v k ∈ closure (v '' t) := hi₂ k hk <| by aesop
  replace hjk : v i ∈ closure (v '' t) := hjk ▸ mul_mem hj' hk'
  exact hi₁ hjk
