/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Multiset.Antidiagonal

import Mathlib.Data.Finsupp.Order

/-!
# The `Finsupp` counterpart of `Multiset.antidiagonal`.

The antidiagonal of `s : α →₀ ℕ` consists of
all pairs `(t₁, t₂) : (α →₀ ℕ) × (α →₀ ℕ)` such that `t₁ + t₂ = s`.
-/

@[expose] public section

namespace Finsupp

open Finset

universe u

variable {α : Type u} [DecidableEq α]

/-- The `Finsupp` counterpart of `Multiset.antidiagonal`: the antidiagonal of
`s : α →₀ ℕ` consists of all pairs `(t₁, t₂) : (α →₀ ℕ) × (α →₀ ℕ)` such that `t₁ + t₂ = s`.
The finitely supported function `antidiagonal s` is equal to the multiplicities of these pairs. -/
noncomputable def antidiagonal' (f : α →₀ ℕ) : (α →₀ ℕ) × (α →₀ ℕ) →₀ ℕ :=
  Multiset.toFinsupp
    ((Finsupp.toMultiset f).antidiagonal.map (Prod.map Multiset.toFinsupp Multiset.toFinsupp))

/-- The antidiagonal of `s : α →₀ ℕ` is the finset of all pairs `(t₁, t₂) : (α →₀ ℕ) × (α →₀ ℕ)`
such that `t₁ + t₂ = s`. -/
noncomputable instance instHasAntidiagonal : HasAntidiagonal (α →₀ ℕ) where
  antidiagonal f := f.antidiagonal'.support
  mem_antidiagonal {f} {p} := by
    rcases p with ⟨p₁, p₂⟩
    simp [antidiagonal', ← and_assoc, Multiset.toFinsupp_eq_iff,
    ← Multiset.toFinsupp_eq_iff (f := f)]

@[simp]
theorem antidiagonal_zero : antidiagonal (0 : α →₀ ℕ) = singleton (0, 0) := rfl

@[to_additive]
theorem prod_antidiagonal_swap {M : Type*} [CommMonoid M] (n : α →₀ ℕ)
    (f : (α →₀ ℕ) → (α →₀ ℕ) → M) :
    ∏ p ∈ antidiagonal n, f p.1 p.2 = ∏ p ∈ antidiagonal n, f p.2 p.1 :=
  prod_equiv (Equiv.prodComm _ _) (by simp [add_comm]) (by simp)

@[simp]
theorem antidiagonal_single (a : α) (n : ℕ) :
    antidiagonal (single a n) = (antidiagonal n).map
      (Function.Embedding.prodMap ⟨_, single_injective a⟩ ⟨_, single_injective a⟩) := by
  ext ⟨x, y⟩
  simp only [mem_antidiagonal, mem_map, mem_antidiagonal, Function.Embedding.coe_prodMap,
    Function.Embedding.coeFn_mk, Prod.map_apply, Prod.mk.injEq, Prod.exists]
  constructor
  · intro h
    refine ⟨x a, y a, DFunLike.congr_fun h a |>.trans single_eq_same, ?_⟩
    simp_rw [DFunLike.ext_iff, ← forall_and]
    intro i
    replace h := DFunLike.congr_fun h i
    simp_rw [single_apply, Finsupp.add_apply] at h ⊢
    obtain rfl | hai := Decidable.eq_or_ne a i
    · exact ⟨if_pos rfl, if_pos rfl⟩
    · simp_rw [if_neg hai, add_eq_zero] at h ⊢
      exact h.imp Eq.symm Eq.symm
  · rintro ⟨a, b, rfl, rfl, rfl⟩
    exact (single_add _ _ _).symm

theorem image_prodMap_embDomain_antidiagonal {β : Type*} [DecidableEq β] (f : α ↪ β)
    (y : α →₀ ℕ) : image (Prod.map (embDomain f) (embDomain f)) (antidiagonal y) =
      antidiagonal (embDomain f y) := by
  ext ⟨u, v⟩
  simp only [mem_image, mem_antidiagonal, Prod.exists, Prod.map_apply,
    Prod.mk.injEq]
  refine ⟨fun ⟨w, z, h, hw, hz⟩ ↦ ?_, fun h ↦ ⟨u.comapDomain f f.injective.injOn,
    ⟨v.comapDomain f f.injective.injOn, ?_, ?_, ?_⟩⟩⟩
  · rw [← hw, ← hz, ← embDomain_add, h]
  · rw [← comapDomain_add_of_injective f.injective, h, comapDomain_embDomain]
  · rw [embDomain_comapDomain ((mem_range_embDomain_iff ..).mp
      (isLowerSet_range_embDomain f (le_iff_exists_add.mpr ⟨v, h.symm⟩) (by simp)))]
  · rw [embDomain_comapDomain ((mem_range_embDomain_iff ..).mp
      (isLowerSet_range_embDomain f (le_iff_exists_add'.mpr ⟨u, h.symm⟩) (by simp)))]

open Finset in
theorem image_sumElim_product_antidiagonal {β : Type*} [DecidableEq β]
    {x : α →₀ ℕ} {y : β →₀ ℕ} : image (fun ((x, y), z, w) ↦
      (x.sumElim z, y.sumElim w)) (antidiagonal x ×ˢ antidiagonal y) =
    antidiagonal (x.sumElim y) := by
  symm; ext ⟨u, v⟩
  simp only [mem_antidiagonal, mem_image, mem_product, Prod.mk.injEq, Prod.exists]
  refine ⟨fun h ↦ ⟨u.comapDomain Sum.inl Sum.inl_injective.injOn,
    v.comapDomain Sum.inl Sum.inl_injective.injOn, u.comapDomain Sum.inr Sum.inr_injective.injOn,
    v.comapDomain Sum.inr Sum.inr_injective.injOn, ⟨?_, ?_⟩, comapDomain_sumElim_comapDomain ..,
    comapDomain_sumElim_comapDomain ..⟩, fun ⟨a, b, a', b', h1, h2, h3⟩ ↦ ?_⟩
  · rw [← comapDomain_add_of_injective Sum.inl_injective, h, comapDomain_sumInl_sumElim]
  · rw [← comapDomain_add_of_injective Sum.inr_injective, h, comapDomain_sumInr_sumElim]
  rw [← h2, ← h3, sumElim_add, h1.left, h1.right]

end Finsupp
