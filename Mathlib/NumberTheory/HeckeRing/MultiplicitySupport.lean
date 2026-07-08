/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.HeckeRing.MultiplicityUnit

/-!
# Hecke rings: the support of the multiplicity

Shimura's multiplicity `m(g, h; d)` is nonzero exactly when `d` lies in the product set
`Γ₁gΓ₂hΓ₃` of the two double cosets. For a Hecke triple this identifies the support
of the structure constants of the Hecke product with the image of `HeckeCoset.mulMap`, which is
a finite set; this is what makes the convolution product of Hecke coset modules well-defined in
the next file.

## Main results

* `DoubleCoset.multiplicity_ne_zero_iff`: `m(g, h; d) ≠ 0 ↔ d ∈ Γ₁gΓ₂hΓ₃`.
* `HeckeCoset.mem_image_mulMap_iff`: the support of the structure constants at `(g₁, g₂)` is
  the image of `mulMap`.
-/

@[expose] public section

open Subgroup
open scoped Pointwise

namespace DoubleCoset

variable {G : Type*} [Group G] {Γ₁ Γ₂ Γ₃ : Subgroup G}

/-- Shimura's multiplicity `m(g, h; d)` is nonzero exactly when `d` lies in the product set
`Γ₁gΓ₂hΓ₃` of the double cosets of `g` and `h`. -/
theorem multiplicity_ne_zero_iff {g h d : G} [Finite (DecompQuotient Γ₁ Γ₂ g)]
    [Finite (DecompQuotient Γ₂ Γ₃ h)] :
    multiplicity Γ₁ Γ₂ Γ₃ g h d ≠ 0 ↔ d ∈ doubleCoset h (doubleCoset g Γ₁ Γ₂) Γ₃ := by
  rw [multiplicity, Nat.card_ne_zero]
  constructor
  · rintro ⟨⟨p, hp⟩, -⟩
    have hp' : _ = (d : G ⧸ Γ₃) := hp
    rw [QuotientGroup.eq] at hp'
    refine mem_doubleCoset.mpr ⟨(p.1.out : G) * g * p.2.out,
      mem_doubleCoset.mpr ⟨p.1.out, p.1.out.2, p.2.out, p.2.out.2, rfl⟩, _, hp', ?_⟩
    simp [mul_assoc]
  · intro hd
    refine ⟨?_, inferInstance⟩
    obtain ⟨w, hw, k, hk, rfl⟩ := mem_doubleCoset.mp hd
    rw [doubleCoset_eq_iUnion_leftCosets, Set.mem_iUnion] at hw
    obtain ⟨i, hi⟩ := hw
    rw [mem_leftCoset_iff] at hi
    have hch : (((i.out : G) * g)⁻¹ * w) * h ∈ doubleCoset h Γ₂ Γ₃ :=
      mem_doubleCoset.mpr ⟨_, hi, 1, Γ₃.one_mem, by rw [mul_one]⟩
    rw [doubleCoset_eq_iUnion_leftCosets, Set.mem_iUnion] at hch
    obtain ⟨j, hj⟩ := hch
    rw [mem_leftCoset_iff] at hj
    refine ⟨⟨(i, j), ?_⟩⟩
    rw [Set.mem_setOf_eq, QuotientGroup.eq]
    have : ((i.out : G) * g * ((j.out : G) * h))⁻¹ * (w * h * k) =
        (((j.out : G) * h)⁻¹ * ((((i.out : G) * g)⁻¹ * w) * h)) * k := by
      simp [mul_assoc]
    rw [this]
    exact Γ₃.mul_mem hj hk

end DoubleCoset

namespace HeckeCoset

open DoubleCoset

variable {G : Type*} [Group G] {Δ : Submonoid G} {H₁ H₂ H₃ : Subgroup G}

/-- The support of the structure constants of the Hecke product at `(g₁, g₂)` is the image
of `HeckeCoset.mulMap`: the multiplicity of a double coset `D` in the product `H₁g₁H₂ * H₂g₂H₃`
is nonzero exactly when `D` is the double coset of `σᵢ g₁ τⱼ g₂` for some pair of coset
representatives. -/
theorem mem_image_mulMap_iff [IsHeckeTriple Δ H₁ H₂] [IsHeckeTriple Δ H₂ H₃]
    [DecidableEq (HeckeCoset Δ H₁ H₃)] (g₁ g₂ : Δ) (D : HeckeCoset Δ H₁ H₃) :
    D ∈ Finset.univ.image (mulMap H₁ H₂ H₃ g₁ g₂) ↔
      multiplicity H₁ H₂ H₃ (g₁ : G) (g₂ : G) (D.rep : G) ≠ 0 := by
  rw [multiplicity_ne_zero_iff]
  constructor
  · intro hD
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hD
    obtain ⟨p, hp⟩ := hD
    have hrep : (D.rep : G) ∈
        doubleCoset ((p.1.out : G) * g₁ * ((p.2.out : G) * g₂)) H₁ H₃ := by
      rw [show doubleCoset ((p.1.out : G) * g₁ * ((p.2.out : G) * g₂)) H₁ H₃ =
          doubleCoset (D.rep : G) H₁ H₃ from HeckeCoset.eq_iff.mp (hp.trans D.mk_rep.symm)]
      exact mem_doubleCoset_self H₁ H₃ _
    obtain ⟨h₁, hh₁, h₂, hh₂, hrep_eq⟩ := mem_doubleCoset.mp hrep
    rw [hrep_eq]
    refine mem_doubleCoset.mpr ⟨h₁ * p.1.out * g₁ * p.2.out,
      mem_doubleCoset.mpr ⟨h₁ * p.1.out, H₁.mul_mem hh₁ p.1.out.2, p.2.out, p.2.out.2, rfl⟩,
      h₂, hh₂, by simp [mul_assoc]⟩
  · intro hD
    obtain ⟨w, hw, k, hk, hd⟩ := mem_doubleCoset.mp hD
    rw [doubleCoset_eq_iUnion_leftCosets, Set.mem_iUnion] at hw
    obtain ⟨i, hi⟩ := hw
    rw [mem_leftCoset_iff] at hi
    have hch : (((i.out : G) * g₁)⁻¹ * w) * g₂ ∈ doubleCoset (g₂ : G) H₂ H₃ :=
      mem_doubleCoset.mpr ⟨_, hi, 1, H₃.one_mem, by rw [mul_one]⟩
    rw [doubleCoset_eq_iUnion_leftCosets, Set.mem_iUnion] at hch
    obtain ⟨j, hj⟩ := hch
    rw [mem_leftCoset_iff] at hj
    refine Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, ?_⟩
    rw [← D.mk_rep]
    refine mulMap_eq_of_mk_eq ?_
    rw [QuotientGroup.eq, hd]
    have : ((i.out : G) * g₁ * ((j.out : G) * g₂))⁻¹ * (w * g₂ * k) =
        (((j.out : G) * g₂)⁻¹ * ((((i.out : G) * g₁)⁻¹ * w) * g₂)) * k := by
      simp [mul_assoc]
    rw [this]
    exact H₃.mul_mem hj hk

end HeckeCoset
