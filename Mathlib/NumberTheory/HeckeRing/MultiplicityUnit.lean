/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.HeckeRing.Multiplicity

/-!
# Hecke rings: the multiplicity of the identity double coset

For `e ∈ Γ₂` the double coset `Γ₂eΓ₂` is `Γ₂` itself, the identity of the Hecke ring of `Γ₂`;
this file proves the two computations expressing this at the level of Shimura's multiplicity:
multiplying by such an `e` on either side, the multiplicity is `1` exactly on the diagonal
`Γ₁gΓ₂ = Γ₁dΓ₂`. Specialised to a Hecke coset module, these compute the products `T(g) * T(1)`
and `T(1) * T(g)` in later files.

## Main results

* `DoubleCoset.multiplicity_eq_one_iff_of_mem_right`: for `e ∈ Γ₂`,
  `multiplicity Γ₁ Γ₂ Γ₂ g e d = 1 ↔ Γ₁gΓ₂ = Γ₁dΓ₂`.
* `DoubleCoset.multiplicity_eq_one_iff_of_mem_left`: for `e ∈ Γ₁`,
  `multiplicity Γ₁ Γ₁ Γ₂ e g d = 1 ↔ Γ₁gΓ₂ = Γ₁dΓ₂`.
-/

@[expose] public section

open Subgroup
open scoped Pointwise

namespace DoubleCoset

variable {G : Type*} [Group G] {Γ₁ Γ₂ : Subgroup G}

/-- Every pair of representatives multiplies into the coset of `g` when the second element
lies in `Γ₂`. -/
private lemma exists_fibre_of_mem_right {g e d : G} (he : e ∈ Γ₂)
    (hd : d ∈ doubleCoset g Γ₁ Γ₂) :
    ∃ p : DecompQuotient Γ₁ Γ₂ g × DecompQuotient Γ₂ Γ₂ e,
      ((p.1.out : G) * g * ((p.2.out : G) * e) : G ⧸ Γ₂) = (d : G ⧸ Γ₂) := by
  rw [doubleCoset_eq_iUnion_leftCosets, Set.mem_iUnion] at hd
  obtain ⟨i₀, hi₀⟩ := hd
  obtain ⟨j₀⟩ : Nonempty (DecompQuotient Γ₂ Γ₂ e) := inferInstance
  rw [mem_leftCoset_iff] at hi₀
  refine ⟨(i₀, j₀), ?_⟩
  rw [QuotientGroup.mk_mul_of_mem _ (Γ₂.mul_mem j₀.out.2 he), QuotientGroup.eq]
  exact hi₀

private lemma exists_fibre_of_mem_left {e g d : G} (he : e ∈ Γ₁)
    (hd : d ∈ doubleCoset g Γ₁ Γ₂) :
    ∃ p : DecompQuotient Γ₁ Γ₁ e × DecompQuotient Γ₁ Γ₂ g,
      ((p.1.out : G) * e * ((p.2.out : G) * g) : G ⧸ Γ₂) = (d : G ⧸ Γ₂) := by
  obtain ⟨i₀⟩ : Nonempty (DecompQuotient Γ₁ Γ₁ e) := inferInstance
  set a := (i₀.out : G) * e with ha_def
  have ha : a ∈ Γ₁ := Γ₁.mul_mem i₀.out.2 he
  have hd' : a⁻¹ * d ∈ doubleCoset g Γ₁ Γ₂ := by
    obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := mem_doubleCoset.mp hd
    exact mem_doubleCoset.mpr ⟨a⁻¹ * h₁, Γ₁.mul_mem (Γ₁.inv_mem ha) hh₁, h₂, hh₂,
      by simp [mul_assoc]⟩
  rw [doubleCoset_eq_iUnion_leftCosets, Set.mem_iUnion] at hd'
  obtain ⟨j₀, hj₀⟩ := hd'
  rw [mem_leftCoset_iff] at hj₀
  refine ⟨(i₀, j₀), ?_⟩
  rw [QuotientGroup.eq]
  simpa [ha_def, mul_assoc] using hj₀

/-- For `e ∈ Γ₂`, right multiplication by the identity double coset `Γ₂eΓ₂ = Γ₂` has
multiplicity `1` exactly on the diagonal. -/
theorem multiplicity_eq_one_iff_of_mem_right {g e d : G} (he : e ∈ Γ₂) :
    multiplicity Γ₁ Γ₂ Γ₂ g e d = 1 ↔ doubleCoset g Γ₁ Γ₂ = doubleCoset d Γ₁ Γ₂ := by
  rw [multiplicity, Nat.card_eq_one_iff_unique]
  constructor
  · rintro ⟨-, ⟨p, hp⟩⟩
    have hp' : _ = (d : G ⧸ Γ₂) := hp
    rw [QuotientGroup.mk_mul_of_mem _ (Γ₂.mul_mem p.2.out.2 he), QuotientGroup.eq] at hp'
    exact (doubleCoset_eq_of_mem (mem_doubleCoset.mpr
      ⟨(p.1.out : G), p.1.out.2, _, hp', (mul_inv_cancel_left _ _).symm⟩)).symm
  · intro h
    haveI := subsingleton_decompQuotient_of_mem he
    obtain ⟨p, hp⟩ := exists_fibre_of_mem_right he (h ▸ mem_doubleCoset_self Γ₁ Γ₂ d)
    refine ⟨⟨fun q₁ q₂ ↦ Subtype.ext ?_⟩, ⟨p, hp⟩⟩
    have hsnd : q₁.1.2 = q₂.1.2 := Subsingleton.elim _ _
    have h₁ : _ = (d : G ⧸ Γ₂) := q₁.2
    have h₂ : _ = (d : G ⧸ Γ₂) := q₂.2
    rw [← hsnd] at h₂
    exact Prod.ext (fst_eq_of_mul_snd_mem (Γ₂.mul_mem q₁.1.2.out.2 he) h₁ h₂) hsnd

/-- For `e ∈ Γ₁`, left multiplication by the identity double coset `Γ₁eΓ₁ = Γ₁` has
multiplicity `1` exactly on the diagonal. -/
theorem multiplicity_eq_one_iff_of_mem_left {e g d : G} (he : e ∈ Γ₁) :
    multiplicity Γ₁ Γ₁ Γ₂ e g d = 1 ↔ doubleCoset g Γ₁ Γ₂ = doubleCoset d Γ₁ Γ₂ := by
  rw [multiplicity, Nat.card_eq_one_iff_unique]
  constructor
  · rintro ⟨-, ⟨p, hp⟩⟩
    have hp' : _ = (d : G ⧸ Γ₂) := hp
    rw [QuotientGroup.eq] at hp'
    exact (doubleCoset_eq_of_mem (mem_doubleCoset.mpr
      ⟨(p.1.out : G) * e * p.2.out, Γ₁.mul_mem (Γ₁.mul_mem p.1.out.2 he) p.2.out.2, _, hp',
        by simp [mul_assoc]⟩)).symm
  · intro h
    haveI := subsingleton_decompQuotient_of_mem he
    obtain ⟨p, hp⟩ := exists_fibre_of_mem_left he (h ▸ mem_doubleCoset_self Γ₁ Γ₂ d)
    refine ⟨⟨fun q₁ q₂ ↦ Subtype.ext ?_⟩, ⟨p, hp⟩⟩
    have hfst : q₁.1.1 = q₂.1.1 := Subsingleton.elim _ _
    have h₁ : _ = (d : G ⧸ Γ₂) := q₁.2
    have h₂ : _ = (d : G ⧸ Γ₂) := q₂.2
    rw [← hfst] at h₂
    exact Prod.ext hfst (snd_eq_of_fst_eq h₁ h₂)

end DoubleCoset

namespace HeckeCoset

open DoubleCoset

variable {G : Type*} [Group G] {Δ : Submonoid G} {H₁ H₂ : Subgroup G}

/-- Every pair of representatives multiplies into `mk H₁ H₂ g₁` when the second double coset is
the identity. -/
lemma mulMap_one_right [IsHeckeTriple Δ H₁ H₂] [IsHeckeTriple Δ H₂ H₂] (g₁ : Δ)
    (p : DecompQuotient H₁ H₂ (g₁ : G) ×
      DecompQuotient H₂ H₂ (((1 : HeckeCoset Δ H₂ H₂).rep : G))) :
    mulMap H₁ H₂ H₂ g₁ (1 : HeckeCoset Δ H₂ H₂).rep p = mk H₁ H₂ g₁ :=
  HeckeCoset.mk_eq_mk_of_mem (mem_doubleCoset.mpr ⟨(p.1.out : G), p.1.out.2,
    (p.2.out : G) * ((1 : HeckeCoset Δ H₂ H₂).rep : G),
    H₂.mul_mem p.2.out.2 HeckeCoset.rep_one_mem, rfl⟩)

/-- Every pair of representatives multiplies into `mk H₁ H₂ g₁` when the first double coset is
the identity. -/
lemma mulMap_one_left [IsHeckeTriple Δ H₁ H₁] [IsHeckeTriple Δ H₁ H₂] (g₁ : Δ)
    (p : DecompQuotient H₁ H₁ (((1 : HeckeCoset Δ H₁ H₁).rep : G)) ×
      DecompQuotient H₁ H₂ (g₁ : G)) :
    mulMap H₁ H₁ H₂ (1 : HeckeCoset Δ H₁ H₁).rep g₁ p = mk H₁ H₂ g₁ :=
  HeckeCoset.mk_eq_mk_of_mem (mem_doubleCoset.mpr
    ⟨(p.1.out : G) * ((1 : HeckeCoset Δ H₁ H₁).rep : G) * (p.2.out : G),
      H₁.mul_mem (H₁.mul_mem p.1.out.2 HeckeCoset.rep_one_mem) p.2.out.2, 1, H₂.one_mem,
      by simp [mul_assoc]⟩)

/-- Right multiplication by the identity double coset has multiplicity `1` exactly on the
diagonal. -/
theorem multiplicity_mul_one (g d : Δ) :
    multiplicity H₁ H₂ H₂ (g : G) ((1 : HeckeCoset Δ H₂ H₂).rep : G) (d : G) = 1 ↔
      mk H₁ H₂ g = mk H₁ H₂ d := by
  rw [multiplicity_eq_one_iff_of_mem_right HeckeCoset.rep_one_mem, HeckeCoset.eq_iff]

/-- Left multiplication by the identity double coset has multiplicity `1` exactly on the
diagonal. -/
theorem multiplicity_one_mul (g d : Δ) :
    multiplicity H₁ H₁ H₂ ((1 : HeckeCoset Δ H₁ H₁).rep : G) (g : G) (d : G) = 1 ↔
      mk H₁ H₂ g = mk H₁ H₂ d := by
  rw [multiplicity_eq_one_iff_of_mem_left HeckeCoset.rep_one_mem, HeckeCoset.eq_iff]

end HeckeCoset
