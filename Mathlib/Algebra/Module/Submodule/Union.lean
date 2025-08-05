/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Tactic.Module

/-!
# Unions of `Submodule`s

This file is a home for results about unions of submodules.

## Main results:
* `Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt`: a finite union of proper submodules is
a proper subset, provided the coefficients are a sufficiently large field.

-/

open Function Set

variable {ι K M : Type*} [Field K] [AddCommGroup M] [Module K M]

lemma Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt (s : Finset ι) (p : ι → Submodule K M)
    (h₁ : ∀ i, p i ≠ ⊤) (h₂ : s.card < ENat.card K) :
    ⋃ i ∈ s, (p i : Set M) ⊂ univ := by
  -- Following https://mathoverflow.net/a/14241
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj hj' =>
    simp only [ssubset_univ_iff] at hj' ⊢
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simpa [← SetLike.coe_ne_coe] using h₁ j
    replace h₂ : s.card + 1 < ENat.card K := by simpa [Finset.card_insert_of_notMem hj] using h₂
    specialize hj' (lt_trans ENat.natCast_lt_succ h₂)
    contrapose! hj'
    replace hj' : (p j : Set M) ∪ (⋃ i ∈ s, p i) = univ := by
      simpa only [Finset.mem_insert, iUnion_iUnion_eq_or_left] using hj'
    suffices (p j : Set M) ⊆ ⋃ i ∈ s, p i by rwa [union_eq_right.mpr this] at hj'
    intro x (hx : x ∈ p j)
    rcases eq_or_ne x 0 with rfl | hx₀
    · simpa using hs
    obtain ⟨y, hy⟩ : ∃ y, y ∉ p j := by specialize h₁ j; contrapose! h₁; ext; simp [h₁]
    have hy₀ : y ≠ 0 := by aesop
    let sxy := {x + t • y | (t : K) (ht : t ≠ 0)}
    have hsxy : sxy ⊆ ⋃ i ∈ s, p i := by
      suffices Disjoint sxy (p j) from this.subset_right_of_subset_union <| hj' ▸ sxy.subset_univ
      rw [Set.disjoint_iff]
      rintro - ⟨⟨t, ht₀, rfl⟩, ht : x + t • y ∈ p j⟩
      rw [(p j).add_mem_iff_right hx, (p j).smul_mem_iff ht₀] at ht
      contradiction
    obtain ⟨k, hk, t₁, t₂, ht, ht₁, ht₂⟩ : ∃ᵉ (k ∈ s) (t₁ : K) (t₂ : K),
        t₁ ≠ t₂ ∧ x + t₁ • y ∈ p k ∧ x + t₂ • y ∈ p k := by
      suffices ∃ᵉ (k ∈ s) (z₁ ∈ sxy) (z₂ ∈ sxy), z₁ ≠ z₂ ∧ z₁ ∈ p k ∧ z₂ ∈ p k by
        obtain ⟨k, hk, -, ⟨t₁, -, rfl⟩, -, ⟨t₂, -, rfl⟩, htne, ht₁, ht₂⟩ := this
        exact ⟨k, hk, t₁, t₂, by aesop, ht₁, ht₂⟩
      choose f hf using fun z : sxy ↦ mem_iUnion.mp (hsxy z.property)
      have hf' : MapsTo f univ s := fun z _ ↦ by specialize hf z; aesop
      suffices ∃ z₁ z₂, z₁ ≠ z₂ ∧ f z₁ = f z₂ by
        obtain ⟨z₁, z₂, hne, heq⟩ := this
        exact ⟨f z₁, hf' (mem_univ _), z₁, z₁.property, z₂, z₂.property,
          Subtype.coe_ne_coe.mpr hne, by specialize hf z₁; aesop, by specialize hf z₂; aesop⟩
      have key : s.card < sxy.encard := by
        refine lt_of_add_lt_add_right <| lt_of_lt_of_le h₂ ?_
        have : Injective (fun t : K ↦ x + t • y) :=
          fun t₁ t₂ ht ↦ smul_left_injective K hy₀ <| by simpa using ht
        have aux : sxy = ((fun t : K ↦ x + t • y) '' {t | t ≠ 0}) := by ext; simp [sxy]
        rw [aux, this.encard_image, encard_ne_add_one]
      obtain ⟨z₁, -, z₂, -, h⟩ := exists_ne_map_eq_of_encard_lt_of_maps_to (by simpa) hf'
      exact ⟨z₁, z₂, h⟩
    replace ht : y ∈ p k := by
      have : (t₁ - t₂) • y ∈ p k := by convert sub_mem ht₁ ht₂ using 1; module
      refine ((p k).smul_mem_iff ?_).mp this
      rwa [sub_ne_zero]
    replace ht : x ∈ p k := by convert sub_mem ht₁ ((p k).smul_mem t₁ ht); simp
    simpa using ⟨k, hk, ht⟩

variable [Finite ι] [Infinite K]

lemma Submodule.exists_forall_notMem_of_forall_ne_top (p : ι → Submodule K M) (h : ∀ i, p i ≠ ⊤) :
    ∃ x, ∀ i, x ∉ p i := by
  let _i : Fintype ι := Fintype.ofFinite ι
  suffices ⋃ i, (p i : Set M) ⊂ univ by simpa [ssubset_univ_iff, iUnion_eq_univ_iff] using this
  simpa using iUnion_ssubset_of_forall_ne_top_of_card_lt Finset.univ p h (by simp)

lemma Module.Dual.exists_forall_ne_zero_of_forall_exists
    (f : ι → Dual K M) (h : ∀ i, ∃ x, f i x ≠ 0) :
    ∃ x, ∀ i, f i x ≠ 0 := by
  let p i := LinearMap.ker (f i)
  replace h i : p i ≠ ⊤ := by specialize h i; aesop
  obtain ⟨x, hx⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p h
  exact ⟨x, by simpa [p] using hx⟩

/-- A convenience variation of `Module.Dual.exists_forall_ne_zero_of_forall_exists` where we are
concerned only about behaviour on a fixed submodule. -/
lemma Module.Dual.exists_forall_mem_ne_zero_of_forall_exists (p : Submodule K M)
    (f : ι → Dual K M) (h : ∀ i, ∃ x ∈ p, f i x ≠ 0) :
    ∃ x ∈ p, ∀ i, f i x ≠ 0 := by
  let f' (i : ι) : Dual K p := (f i).domRestrict p
  replace h (i : ι) : ∃ x : p, f' i x ≠ 0 := by obtain ⟨x, hxp, hx₀⟩ := h i; exact ⟨⟨x, hxp⟩, hx₀⟩
  obtain ⟨⟨x, hxp⟩, hx₀⟩ := exists_forall_ne_zero_of_forall_exists f' h
  exact ⟨x, hxp, hx₀⟩
