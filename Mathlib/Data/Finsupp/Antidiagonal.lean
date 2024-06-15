/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Multiset.Antidiagonal

#align_import data.finsupp.antidiagonal from "leanprover-community/mathlib"@"0a0ec35061ed9960bf0e7ffb0335f44447b58977"

/-!
# The `Finsupp` counterpart of `Multiset.antidiagonal`.

The antidiagonal of `s : α →₀ ℕ` consists of
all pairs `(t₁, t₂) : (α →₀ ℕ) × (α →₀ ℕ)` such that `t₁ + t₂ = s`.
-/

namespace Finsupp

open Finset

universe u

variable {α : Type u} [DecidableEq α]

/-- The `Finsupp` counterpart of `Multiset.antidiagonal`: the antidiagonal of
`s : α →₀ ℕ` consists of all pairs `(t₁, t₂) : (α →₀ ℕ) × (α →₀ ℕ)` such that `t₁ + t₂ = s`.
The finitely supported function `antidiagonal s` is equal to the multiplicities of these pairs. -/
def antidiagonal' (f : α →₀ ℕ) : (α →₀ ℕ) × (α →₀ ℕ) →₀ ℕ :=
  Multiset.toFinsupp
    ((Finsupp.toMultiset f).antidiagonal.map (Prod.map Multiset.toFinsupp Multiset.toFinsupp))
#align finsupp.antidiagonal' Finsupp.antidiagonal'

/-- The antidiagonal of `s : α →₀ ℕ` is the finset of all pairs `(t₁, t₂) : (α →₀ ℕ) × (α →₀ ℕ)`
such that `t₁ + t₂ = s`. -/
instance instHasAntidiagonal : HasAntidiagonal (α →₀ ℕ) where
  antidiagonal f := f.antidiagonal'.support
  mem_antidiagonal {f} {p} := by
    rcases p with ⟨p₁, p₂⟩
    simp [antidiagonal', ← and_assoc, Multiset.toFinsupp_eq_iff,
    ← Multiset.toFinsupp_eq_iff (f := f)]

#align finsupp.antidiagonal_filter_fst_eq Finset.filter_fst_eq_antidiagonal
#align finsupp.antidiagonal_filter_snd_eq Finset.filter_snd_eq_antidiagonal

-- nolint as this is for dsimp
@[simp, nolint simpNF]
theorem antidiagonal_zero : antidiagonal (0 : α →₀ ℕ) = singleton (0, 0) := rfl
#align finsupp.antidiagonal_zero Finsupp.antidiagonal_zero

@[to_additive]
theorem prod_antidiagonal_swap {M : Type*} [CommMonoid M] (n : α →₀ ℕ)
    (f : (α →₀ ℕ) → (α →₀ ℕ) → M) :
    ∏ p ∈ antidiagonal n, f p.1 p.2 = ∏ p ∈ antidiagonal n, f p.2 p.1 :=
  prod_equiv (Equiv.prodComm _ _) (by simp [add_comm]) (by simp)
#align finsupp.prod_antidiagonal_swap Finsupp.prod_antidiagonal_swap
#align finsupp.sum_antidiagonal_swap Finsupp.sum_antidiagonal_swap

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
    · simp_rw [if_neg hai, _root_.add_eq_zero_iff] at h ⊢
      exact h.imp Eq.symm Eq.symm
  · rintro ⟨a, b, rfl, rfl, rfl⟩
    exact (single_add _ _ _).symm

end Finsupp
