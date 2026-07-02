/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.HeckeRing.Basic

/-!
# Hecke rings: the multiplicity function

Shimura's multiplicity (Proposition 3.2 of [Shimura][shimura1971]) counts, for double cosets
`Γ₁gΓ₂`, `Γ₂hΓ₃` and `Γ₁dΓ₃`, the pairs of left-coset representatives `(σᵢ, τⱼ)` with
`σᵢ g τⱼ h Γ₃ = d Γ₃`. These natural numbers are the structure constants of the Hecke product
defined in later files: the diagonal case `Γ₁ = Γ₂ = Γ₃` gives the multiplication of the Hecke
ring, and the general case gives the composition of Hecke bimodules. This file defines the
multiplicity, the map `mulMap` sending a pair of representatives to the double coset of their
product, and the uniqueness lemmas for the fibres of the multiplicity.

## Main definitions

* `DoubleCoset.multiplicity`: Shimura's multiplicity, a natural number structure constant.
* `HeckePair.mulMap`: the double coset `H (σᵢ g₁ τⱼ g₂) H` of a pair of coset representatives.
-/

@[expose] public section

open Subgroup
open scoped Pointwise

namespace DoubleCoset

variable {G : Type*} [Group G]

lemma subsingleton_decompQuotient {Γ₁ Γ₂ : Subgroup G} {g : G}
    (h : Γ₁ ≤ ConjAct.toConjAct g • Γ₂) : Subsingleton (DecompQuotient Γ₁ Γ₂ g) := by
  change Subsingleton (Γ₁ ⧸ (ConjAct.toConjAct g • Γ₂).subgroupOf Γ₁)
  rw [Subgroup.subgroupOf_eq_top.mpr h]
  exact QuotientGroup.subsingleton_quotient_top

lemma subsingleton_decompQuotient_of_mem {Γ : Subgroup G} {g : G} (hg : g ∈ Γ) :
    Subsingleton (DecompQuotient Γ Γ g) :=
  subsingleton_decompQuotient
    (Subgroup.conjAct_pointwise_smul_eq_self (Subgroup.le_normalizer hg)).ge

/-- The left cosets `σᵢ g Γ₂` of the decomposition of `Γ₁gΓ₂` are pairwise distinct: the map
`i ↦ σᵢ g Γ₂` into `G ⧸ Γ₂` is injective. -/
lemma mk_out_mul_injective (Γ₁ Γ₂ : Subgroup G) (g : G) :
    Function.Injective fun i : DecompQuotient Γ₁ Γ₂ g ↦ (((i.out : G) * g : G) : G ⧸ Γ₂) := by
  intro i j hij
  simp only [QuotientGroup.eq] at hij
  rw [← QuotientGroup.out_eq' i, ← QuotientGroup.out_eq' j, QuotientGroup.eq,
    Subgroup.mem_subgroupOf, Subgroup.mem_conjAct_pointwise_smul_iff]
  simpa [mul_assoc] using hij

/-- Shimura's multiplicity (Proposition 3.2 of [Shimura][shimura1971]): the number of pairs
`(i, j)` of coset representatives such that `σᵢ g τⱼ h Γ₃ = d Γ₃`. The diagonal case
`Γ₁ = Γ₂ = Γ₃` gives the structure constants of the Hecke ring. -/
noncomputable def multiplicity (Γ₁ Γ₂ Γ₃ : Subgroup G) (g h d : G) : ℕ :=
  Nat.card {p : DecompQuotient Γ₁ Γ₂ g × DecompQuotient Γ₂ Γ₃ h |
    ((p.1.out : G) * g * ((p.2.out : G) * h) : G ⧸ Γ₃) = (d : G ⧸ Γ₃)}

/-- When the first components of two pairs in the fibre of the multiplicity agree, the second
components agree. -/
lemma snd_eq_of_fst_eq {Γ₁ Γ₂ Γ₃ : Subgroup G} {g h d : G} {i : DecompQuotient Γ₁ Γ₂ g}
    {j₁ j₂ : DecompQuotient Γ₂ Γ₃ h}
    (h₁ : ((i.out : G) * g * ((j₁.out : G) * h) : G ⧸ Γ₃) = (d : G ⧸ Γ₃))
    (h₂ : ((i.out : G) * g * ((j₂.out : G) * h) : G ⧸ Γ₃) = (d : G ⧸ Γ₃)) :
    j₁ = j₂ := by
  refine mk_out_mul_injective Γ₂ Γ₃ h ?_
  have h := h₁.trans h₂.symm
  rw [QuotientGroup.eq] at h ⊢
  simpa [mul_assoc] using h

/-- When the common second component of two pairs in the fibre of the multiplicity satisfies
`τⱼ h ∈ Γ₂`, the first components agree. -/
lemma fst_eq_of_mul_snd_mem {Γ₁ Γ₂ : Subgroup G} {g h d : G} {i₁ i₂ : DecompQuotient Γ₁ Γ₂ g}
    {j : DecompQuotient Γ₂ Γ₂ h} (hj : (j.out : G) * h ∈ Γ₂)
    (h₁ : ((i₁.out : G) * g * ((j.out : G) * h) : G ⧸ Γ₂) = (d : G ⧸ Γ₂))
    (h₂ : ((i₂.out : G) * g * ((j.out : G) * h) : G ⧸ Γ₂) = (d : G ⧸ Γ₂)) :
    i₁ = i₂ := by
  rw [QuotientGroup.mk_mul_of_mem _ hj] at h₁ h₂
  exact mk_out_mul_injective Γ₁ Γ₂ g (h₁.trans h₂.symm)

end DoubleCoset

namespace HeckePair

open DoubleCoset

variable {G : Type*} [Group G] (P : HeckePair G)

attribute [local instance] HeckePair.doubleCosetSetoid

/-- The map sending a pair of coset representatives `(σᵢ, τⱼ)` to the double coset
of their product `H (σᵢ g₁ τⱼ g₂) H`. -/
noncomputable def mulMap (g₁ g₂ : P.Δ)
    (p : DecompQuotient P.H P.H (g₁ : G) × DecompQuotient P.H P.H (g₂ : G)) : HeckeCoset P :=
  ⟦⟨(p.1.out : G) * g₁ * ((p.2.out : G) * g₂),
    P.Δ.mul_mem (P.Δ.mul_mem (P.subgroup_le p.1.out.2) g₁.2)
      (P.Δ.mul_mem (P.subgroup_le p.2.out.2) g₂.2)⟩⟧

/-- If `σᵢ g₁ τⱼ g₂ H = d H` then the double coset of `σᵢ g₁ τⱼ g₂` equals that of `d`. -/
lemma mulMap_eq_of_mk_eq {g₁ g₂ d : P.Δ}
    {p : DecompQuotient P.H P.H (g₁ : G) × DecompQuotient P.H P.H (g₂ : G)}
    (h : ((p.1.out : G) * g₁ * ((p.2.out : G) * g₂) : G ⧸ P.H) = ((d : G) : G ⧸ P.H)) :
    P.mulMap g₁ g₂ p = (⟦d⟧ : HeckeCoset P) := by
  rw [QuotientGroup.eq] at h
  exact HeckeCoset.mk_eq_mk_of_mem (DoubleCoset.mem_doubleCoset.mpr
    ⟨1, P.H.one_mem, _, P.H.inv_mem h, by rw [one_mul, mul_inv_rev, inv_inv, mul_inv_cancel_left]⟩)

end HeckePair
