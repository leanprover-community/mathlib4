/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Jiaxi Mo
-/
module

public import Mathlib.NumberTheory.HeckeRing.HeckeCoset.Basic
public import Mathlib.Data.Finsupp.Defs

/-!
# Multiplicity

-/

@[expose] public section

open DoubleCoset

variable {G : Type*} [Group G] {H₁ H₂ H₃ : Subgroup G} (g g' : G)

namespace DoubleCoset

lemma DecompQuotient.snd_eq_of_fst_eq {g g' d : G} {i : DecompQuotient H₁ H₂ g}
    {j₁ j₂ : DecompQuotient H₂ H₃ g'}
    (h₁ : ((i.out : G) * g * ((j₁.out : G) * g') : G ⧸ H₃) = (d : G ⧸ H₃))
    (h₂ : ((i.out : G) * g * ((j₂.out : G) * g') : G ⧸ H₃) = (d : G ⧸ H₃)) :
    j₁ = j₂ := by
  apply toLeftCoset_injective
  have h := h₁.trans h₂.symm
  simp only [toLeftCoset_apply, QuotientGroup.eq] at h ⊢
  simpa [mul_assoc] using h

end DoubleCoset

namespace DoubleCoset₀

/-- The map sending a pair of coset representatives `(σᵢ, τⱼ)` to the mixed double coset
`H₁ (σᵢ g₁ τⱼ g₂) H₃` of their product. -/
noncomputable def mulMap (x : DoubleCoset₀ H₁ H₂) (y : DoubleCoset₀ H₂ H₃)
    (p : DecompQuotient H₁ H₂ x.rep × DecompQuotient H₂ H₃ y.rep) : DoubleCoset₀ H₁ H₃ :=
  mk H₁ H₃ (p.1.out * x.rep * p.2.out * y.rep)

lemma mulMap_eq_of_mk_eq (x : DoubleCoset₀ H₁ H₂) (y : DoubleCoset₀ H₂ H₃)
    (z : DoubleCoset₀ H₁ H₃) {p : DecompQuotient H₁ H₂ x.rep × DecompQuotient H₂ H₃ y.rep}
    (h : ((p.1.out * x.rep * ((p.2.out : G) * y.rep) : G) : G ⧸ H₃) = (z.rep : G ⧸ H₃)) :
    x.mulMap y p = z := by
  rw [← DoubleCoset₀.mk_rep z]
  apply DoubleCoset₀.mk_eq_iff.mpr
  exact ⟨1, H₁.one_mem, ((p.1.out * x.rep * p.2.out * y.rep)⁻¹ * z.rep), by
    simpa [mul_assoc] using QuotientGroup.eq.mp h, by simp [mul_assoc]⟩

/-- Shimura's multiplicity descended to Hecke double cosets. -/
noncomputable def multiplicity (x : DoubleCoset₀ H₁ H₂) (y : DoubleCoset₀ H₂ H₃) :
    DoubleCoset₀ H₁ H₃ →₀ ℕ :=
  Finsupp.ofSupportFinite
    (fun z => Nat.card {p : DecompQuotient H₁ H₂ x.rep × DecompQuotient H₂ H₃ y.rep |
      ((p.1.out : G) * x.rep * ((p.2.out : G) * y.rep) : G ⧸ H₃) = (z.rep : G ⧸ H₃)}) <| by
    classical
    refine (Finset.univ.image (x.mulMap y)).finite_toSet.subset ?_
    intro z hz
    simp only [Function.mem_support, Nat.card_ne_zero] at hz
    obtain ⟨⟨p, hp⟩, _⟩ := hz
    exact Finset.mem_image.mpr ⟨p, Finset.mem_univ p, mulMap_eq_of_mk_eq x y z hp⟩

lemma multiplicity_apply (x : DoubleCoset₀ H₁ H₂) (y : DoubleCoset₀ H₂ H₃)
    (z : DoubleCoset₀ H₁ H₃) :
    x.multiplicity y z =
      Nat.card {p : DecompQuotient H₁ H₂ x.rep × DecompQuotient H₂ H₃ y.rep |
        (p.1.out * x.rep * (p.2.out * y.rep) : G ⧸ H₃) = (z.rep : G ⧸ H₃)} := rfl

end DoubleCoset₀
