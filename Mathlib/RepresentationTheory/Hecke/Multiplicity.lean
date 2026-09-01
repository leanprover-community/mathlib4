/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Jiaxi Mo
-/
module

public import Mathlib.RepresentationTheory.Hecke.LeftFiniteDoubleCoset
public import Mathlib.Data.Finsupp.Defs

/-!
# Multiplicity of convolution product

-/

@[expose] public section

variable {G : Type*} [Group G] {H₁ H₂ H₃ : Subgroup G}
open DoubleCoset

namespace DoubleCoset.LeftDecompQuotient

lemma snd_eq_of_fst_eq {g g' d : G} {i : LeftDecompQuotient H₁ H₂ g}
    {j₁ j₂ : LeftDecompQuotient H₂ H₃ g'}
    (h₁ : (i.out * g * (j₁.out * g') : G ⧸ H₃) = (d : G ⧸ H₃))
    (h₂ : (i.out * g * (j₂.out * g') : G ⧸ H₃) = (d : G ⧸ H₃)) :
    j₁ = j₂ := by
  apply toLeftCoset_injective
  have h := h₁.trans h₂.symm
  simp only [toLeftCoset_apply, QuotientGroup.eq] at h ⊢
  simpa [mul_assoc] using h

lemma nat_card_fiber (H₁ H₂ : Subgroup G) (x y : G) [Decidable (mk H₁ H₂ x = mk H₁ H₂ y)] :
    Nat.card {j : LeftDecompQuotient H₁ H₂ x | ((j.out : G) * x : G ⧸ H₂) = (y : G ⧸ H₂)} =
      if mk H₁ H₂ x = mk H₁ H₂ y then 1 else 0 := by
  split_ifs with hxy
  · apply Nat.card_eq_one_iff_unique.mpr
    constructor
    · exact ⟨fun i j ↦ Subtype.ext <| toLeftCoset_injective <| by
        simpa [toLeftCoset_apply] using i.2.trans j.2.symm⟩
    · obtain ⟨i, hi⟩ := mem_range_toLeftCoset_iff.mpr hxy
      exact ⟨⟨i, by simpa [toLeftCoset_apply] using hi⟩⟩
  · have : IsEmpty {j : LeftDecompQuotient H₁ H₂ x | ((j.out : G) * x : G ⧸ H₂) = (y : G ⧸ H₂)} :=
      ⟨fun i => hxy <| mem_range_toLeftCoset_iff.mp ⟨i.1, by rw [toLeftCoset_apply]; exact i.2⟩⟩
    exact Nat.card_of_isEmpty

lemma nat_card_fiber_helper (H₁ : Subgroup G) (x y z : G) :
    (x * y : G ⧸ H₁) = z ↔ y = (x⁻¹ * z : G ⧸ H₁) := by
  simp only [← smul_eq_mul, ← MulAction.Quotient.smul_mk, ← inv_smul_eq_iff, inv_inv]

end DoubleCoset.LeftDecompQuotient

namespace DoubleCoset₀

/-- The map sending a pair of coset representatives `(σᵢ, τⱼ)` to the mixed double coset
`H₁ (σᵢ g₁ τⱼ g₂) H₃` of their product. -/
noncomputable def mulMap (x : DoubleCoset₀ H₁ H₂) (y : DoubleCoset₀ H₂ H₃)
    (p : LeftDecompQuotient H₁ H₂ x.rep × LeftDecompQuotient H₂ H₃ y.rep) : DoubleCoset₀ H₁ H₃ :=
  mk H₁ H₃ (p.1.out * x.rep * p.2.out * y.rep)

lemma mulMap_eq_of_mk_eq (x : DoubleCoset₀ H₁ H₂) (y : DoubleCoset₀ H₂ H₃)
    (z : DoubleCoset₀ H₁ H₃) {p : LeftDecompQuotient H₁ H₂ x.rep × LeftDecompQuotient H₂ H₃ y.rep}
    (h : (p.1.out * x.rep * (p.2.out * y.rep) : G ⧸ H₃) = (z.rep : G ⧸ H₃)) :
    x.mulMap y p = z := by
  rw [← DoubleCoset₀.mk_rep z]
  apply DoubleCoset₀.mk_eq_iff.mpr
  exact ⟨1, H₁.one_mem, ((p.1.out * x.rep * p.2.out * y.rep)⁻¹ * z.rep), by
    simpa [mul_assoc] using QuotientGroup.eq.mp h, by simp [mul_assoc]⟩

/-- Shimura's multiplicity descended to Hecke double cosets. -/
noncomputable def multiplicity (x : DoubleCoset₀ H₁ H₂) (y : DoubleCoset₀ H₂ H₃) :
    DoubleCoset₀ H₁ H₃ →₀ ℕ :=
  Finsupp.ofSupportFinite
    (fun z => Nat.card {p : LeftDecompQuotient H₁ H₂ x.rep × LeftDecompQuotient H₂ H₃ y.rep |
      (p.1.out * x.rep * (p.2.out * y.rep) : G ⧸ H₃) = (z.rep : G ⧸ H₃)}) <| by
    classical
    refine (Finset.univ.image (x.mulMap y)).finite_toSet.subset ?_
    intro z hz
    simp only [Function.mem_support, Nat.card_ne_zero] at hz
    obtain ⟨⟨p, hp⟩, _⟩ := hz
    exact Finset.mem_image.mpr ⟨p, Finset.mem_univ p, mulMap_eq_of_mk_eq x y z hp⟩

lemma multiplicity_apply (x : DoubleCoset₀ H₁ H₂) (y : DoubleCoset₀ H₂ H₃)
    (z : DoubleCoset₀ H₁ H₃) :
    x.multiplicity y z =
      Nat.card {p : LeftDecompQuotient H₁ H₂ x.rep × LeftDecompQuotient H₂ H₃ y.rep |
        (p.1.out * x.rep * (p.2.out * y.rep) : G ⧸ H₃) = (z.rep : G ⧸ H₃)} := rfl

end DoubleCoset₀
