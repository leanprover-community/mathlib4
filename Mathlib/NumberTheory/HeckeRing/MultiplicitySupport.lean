/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.HeckeRing.MultiplicityUnit

/-!
# Hecke rings: positivity of the multiplicity on the product support

The product `D₁ * D₂` of two double cosets is supported on the finite set `mulSupport`. This file
relates membership of `mulSupport` to positivity of Shimura's multiplicity: `heckeMultiplicity` is
positive exactly on the double cosets that occur in the product, and zero off the support.

## Main results

* `HeckeRing.heckeMultiplicity_pos_of_mem`: the multiplicity is positive on the support.
* `HeckeRing.heckeMultiplicity_eq_zero_of_nmem_mulSupport`: zero off the support.
* `HeckeRing.mem_mulSupport_of_product_mem`: a product in `HdH` witnesses membership.
-/

@[expose] public section

open Set DoubleCoset Subgroup
open scoped Pointwise

namespace HeckeRing

variable {G : Type*} [Group G]

attribute [local instance] doubleCosetSetoid

variable (P : HeckePair G)

/-- If the double coset of `σ_{i₀} τ_{j₀}` equals `HcH`, then the fibre defining the multiplicity
at `c` is nonempty: some pair of representatives multiplies into the right coset `cH`. -/
private lemma nonempty_witness_of_doubleCoset_eq (g₁ g₂ : P.Δ) (c : G)
    (i₀ : decompQuot P g₁) (j₀ : decompQuot P g₂)
    (hset_eq : DoubleCoset.doubleCoset
      ((↑i₀.out : G) * (↑g₁ : G) * ((↑j₀.out : G) * (↑g₂ : G)))
      (P.H : Set G) (P.H : Set G) =
      DoubleCoset.doubleCoset c P.H P.H) :
    Nonempty ↑{x : decompQuot P g₁ × decompQuot P g₂ |
      ({(↑x.1.out : G) * (↑g₁ : G)} : Set G) *
        {(↑x.2.out : G) * (↑g₂ : G)} * P.H = {c} * (P.H : Set G)} := by
  obtain ⟨h₁, hh₁, h₂, hh₂, hprod⟩ := (DoubleCoset.eq P.H P.H _ _).mp
    (DoubleCoset.mk_eq_of_doubleCoset_eq hset_eq)
  set α := (↑g₁ : G)
  set β := (↑g₂ : G)
  set K₁ := (ConjAct.toConjAct α • P.H).subgroupOf P.H
  set i' : decompQuot P g₁ := ⟦⟨h₁ * ↑i₀.out, P.H.mul_mem hh₁ i₀.out.2⟩⟧
  obtain ⟨κ₁, hκ₁_eq⟩ := QuotientGroup.mk_out_eq_mul K₁
    ⟨h₁ * ↑i₀.out, P.H.mul_mem hh₁ i₀.out.2⟩
  have hκ₁_conj : α⁻¹ * (κ₁.val : G) * α ∈ P.H :=
    inv_mul_mul_mem_of_mem_subgroupOf (H := P.H) κ₁
  set K₂ := (ConjAct.toConjAct β • P.H).subgroupOf P.H
  set j' : decompQuot P g₂ := ⟦⟨(α⁻¹ * (κ₁.val : G) * α)⁻¹ * ↑j₀.out,
    P.H.mul_mem (P.H.inv_mem hκ₁_conj) j₀.out.2⟩⟧
  obtain ⟨κ₂, hκ₂_eq⟩ := QuotientGroup.mk_out_eq_mul K₂
    ⟨(α⁻¹ * (κ₁.val : G) * α)⁻¹ * ↑j₀.out,
      P.H.mul_mem (P.H.inv_mem hκ₁_conj) j₀.out.2⟩
  have hκ₂_conj : β⁻¹ * (κ₂.val : G) * β ∈ P.H :=
    inv_mul_mul_mem_of_mem_subgroupOf (H := P.H) κ₂
  have hi'_coe : (↑i'.out : G) = h₁ * ↑i₀.out * (κ₁.val : G) := by
    have := congr_arg (Subtype.val : P.H → G) hκ₁_eq
    simpa [Subgroup.coe_mul] using this
  have hj'_coe : (↑j'.out : G) =
      (α⁻¹ * (κ₁.val : G) * α)⁻¹ * ↑j₀.out * (κ₂.val : G) := by
    have h := hκ₂_eq
    apply_fun (↑· : ↥P.H → G) at h
    simp only [Subgroup.coe_mul] at h
    exact h
  refine ⟨⟨(i', j'), ?_⟩⟩
  simp only [Set.mem_setOf_eq]
  have hprod_main : (↑i'.out : G) * α * ((↑j'.out : G) * β) =
      c * (h₂⁻¹ * (β⁻¹ * (κ₂.val : G) * β)) := by
    rw [hi'_coe, hj'_coe]
    have hprod' : c = h₁ * (↑i₀.out * α * (↑j₀.out * β)) * h₂ := hprod
    rw [hprod']
    group
  rw [Set.singleton_mul_singleton, hprod_main, ← Set.singleton_mul_singleton, mul_assoc,
    Subgroup.singleton_mul_subgroup (P.H.mul_mem (P.H.inv_mem hh₂) hκ₂_conj)]

/-- The multiplicity is nonzero for double cosets in the product support. -/
lemma heckeMultiplicity_pos_of_mem_mulSupport (g₁ g₂ : P.Δ) (d : HeckeCoset P)
    (hd : d ∈ mulSupport P g₁ g₂) :
    heckeMultiplicity P g₁ g₂ (HeckeCoset.rep d) ≠ 0 := by
  rw [heckeMultiplicity]
  simp only [ne_eq, Nat.cast_eq_zero]
  rw [Nat.card_eq_zero, not_or, not_isEmpty_iff]
  refine ⟨?_, not_infinite_iff_finite.mpr inferInstance⟩
  rw [mulSupport] at hd
  simp only [Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ, true_and,
    Prod.exists] at hd
  obtain ⟨i₀, j₀, hmap⟩ := hd
  exact nonempty_witness_of_doubleCoset_eq P g₁ g₂ (HeckeCoset.rep d) i₀ j₀
    ((HeckeCoset.eq_iff _ _).mp (hmap.trans (Quotient.out_eq d).symm))

/-- The multiplicity is zero for double cosets outside the product support. -/
lemma heckeMultiplicity_eq_zero_of_nmem_mulSupport (g₁ g₂ : P.Δ) (d : HeckeCoset P)
    (hd : d ∉ mulSupport P g₁ g₂) :
    heckeMultiplicity P g₁ g₂ (HeckeCoset.rep d) = 0 := by
  simp only [heckeMultiplicity, Nat.cast_eq_zero, Nat.card_eq_zero, isEmpty_subtype]
  left
  rintro ⟨i, j⟩ hij
  refine hd ?_
  rw [mulSupport]
  simp only [Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ, true_and, Prod.exists]
  exact ⟨i, j, (doubleCoset_eq_of_rightCoset_eq P g₁ g₂ (HeckeCoset.rep d) (i, j) hij).trans
    (Quotient.out_eq d)⟩

/-- A multiplicity that is both at most one and positive must equal one. -/
lemma heckeMultiplicity_eq_one_of_le_one_and_pos (g₁ g₂ d : P.Δ)
    (h_le : heckeMultiplicity P g₁ g₂ d ≤ 1)
    (h_pos : 0 < heckeMultiplicity P g₁ g₂ d) :
    heckeMultiplicity P g₁ g₂ d = 1 := by omega

/-- The multiplicity is positive for double cosets in the product support. -/
lemma heckeMultiplicity_pos_of_mem (g₁ g₂ : P.Δ) (d : HeckeCoset P)
    (hd : d ∈ mulSupport P g₁ g₂) :
    0 < heckeMultiplicity P g₁ g₂ (HeckeCoset.rep d) := by
  have h_ne := heckeMultiplicity_pos_of_mem_mulSupport P g₁ g₂ d hd
  have h_nonneg : (0 : ℤ) ≤ heckeMultiplicity P g₁ g₂ (HeckeCoset.rep d) := by
    simp only [heckeMultiplicity]
    exact_mod_cast Nat.zero_le _
  exact lt_of_le_of_ne h_nonneg (Ne.symm h_ne)

/-- If `h₁ g₁ (h₂ g₂) ∈ HdH` (with `h₁, h₂ ∈ H`), then `⟦d⟧ ∈ mulSupport g₁ g₂`. -/
lemma mem_mulSupport_of_product_mem (g₁ g₂ d : P.Δ) (h₁ h₂ : P.H)
    (hmem : (h₁ : G) * g₁ * ((h₂ : G) * g₂) ∈
      DoubleCoset.doubleCoset (d : G) P.H P.H) :
    (⟦d⟧ : HeckeCoset P) ∈ mulSupport P g₁ g₂ := by
  have key : mulMap P g₁ g₂ (⟦⟨h₁, h₁.2⟩⟧, ⟦⟨h₂, h₂.2⟩⟧) =
      (⟦d⟧ : HeckeCoset P) := by
    unfold mulMap
    change (⟦_⟧ : HeckeCoset P) = ⟦_⟧
    rw [HeckeCoset.eq_iff]
    dsimp only
    obtain ⟨n₁, hn₁⟩ := QuotientGroup.mk_out_eq_mul
      ((ConjAct.toConjAct (g₁ : G) • P.H).subgroupOf P.H) ⟨(h₁ : G), h₁.2⟩
    obtain ⟨n₂, hn₂⟩ := QuotientGroup.mk_out_eq_mul
      ((ConjAct.toConjAct (g₂ : G) • P.H).subgroupOf P.H) ⟨(h₂ : G), h₂.2⟩
    have hi : ((⟦⟨(h₁ : G), h₁.2⟩⟧ : decompQuot P g₁).out : G) = h₁ * n₁ := by
      have := congr_arg (Subtype.val : P.H → G) hn₁
      simpa [Subgroup.coe_mul]
    have hj : ((⟦⟨(h₂ : G), h₂.2⟩⟧ : decompQuot P g₂).out : G) = h₂ * n₂ := by
      have := congr_arg (Subtype.val : P.H → G) hn₂
      simpa [Subgroup.coe_mul]
    have hn₂c : (g₂ : G)⁻¹ * ↑n₂ * g₂ ∈ P.H :=
      inv_mul_mul_mem_of_mem_subgroupOf (H := P.H) n₂
    rw [hi, hj]
    apply HeckeCoset.doubleCoset_eq_of_mem
    rw [DoubleCoset.mem_doubleCoset] at hmem
    obtain ⟨a, ha, b, hb, hab⟩ := hmem
    rw [DoubleCoset.mem_doubleCoset]
    refine ⟨(h₁ : G) * ↑↑n₁ * (h₁ : G)⁻¹ * a,
      P.H.mul_mem (P.H.mul_mem (P.H.mul_mem h₁.2 (SetLike.coe_mem n₁.val))
        (P.H.inv_mem h₁.2)) ha,
      b * ((g₂ : G)⁻¹ * ↑↑n₂ * g₂), P.H.mul_mem hb hn₂c, ?_⟩
    have key : (↑h₁ * ↑↑n₁ * (↑h₁ : G)⁻¹ * a) * ↑d *
        (b * ((↑g₂ : G)⁻¹ * ↑↑n₂ * ↑g₂)) =
        (↑h₁ * ↑↑n₁) * (↑g₁ : G) * ((↑h₂ * ↑↑n₂) * ↑g₂) :=
      calc (↑h₁ * ↑↑n₁ * (↑h₁ : G)⁻¹ * a) * ↑d
          * (b * ((↑g₂ : G)⁻¹ * ↑↑n₂ * ↑g₂))
          = ↑h₁ * ↑↑n₁ * (↑h₁)⁻¹ * (a * ↑d * b) *
            ((↑g₂)⁻¹ * ↑↑n₂ * ↑g₂) := by group
        _ = ↑h₁ * ↑↑n₁ * (↑h₁)⁻¹ * (↑h₁ * ↑g₁ * (↑h₂ * ↑g₂)) *
            ((↑g₂)⁻¹ * ↑↑n₂ * ↑g₂) := by rw [hab]
        _ = (↑h₁ * ↑↑n₁) * ↑g₁ * ((↑h₂ * ↑↑n₂) * ↑g₂) := by group
    exact key.symm
  unfold mulSupport
  exact key ▸ Finset.mem_image_of_mem (mulMap P g₁ g₂) (Finset.mem_univ _)

end HeckeRing
