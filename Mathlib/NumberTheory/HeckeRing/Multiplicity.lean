/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.HeckeRing.Basic

/-!
# Hecke rings: the multiplicity function

Shimura's multiplicity `heckeMultiplicity` (Proposition 3.2 of *Introduction to the Arithmetic
Theory of Automorphic Functions*) counts, for double cosets `Hg₁H`, `Hg₂H` and `HdH`, the pairs of
left-coset representatives `(σᵢ, τⱼ)` with `σᵢ τⱼ H = d H`. These integers are the structure
constants of the Hecke product defined in later files. This file sets up the multiplicity, the map
`mulMap` on pairs of representatives, and the structural lemmas on the coset decomposition.

## Main definitions

* `HeckeRing.mulMap`: the double coset `H(σᵢ τⱼ)H` of a pair of coset representatives.
* `HeckeRing.heckeMultiplicity`: Shimura's multiplicity, an integer structure constant.
* `HeckeRing.mulSupport`: the finite set of double cosets appearing in a product.
-/

@[expose] public section

open Set DoubleCoset Subgroup
open scoped Pointwise

namespace HeckeRing

variable {G : Type*} [Group G] (H : Subgroup G) (Δ : Submonoid G) (P : HeckePair G)

attribute [local instance] doubleCosetSetoid

/-- Two `HeckeCoset` elements are equal iff their `toSet`s are equal. -/
lemma HeckeCoset_ext_toSet {D₁ D₂ : HeckeCoset P}
    (h : HeckeCoset.toSet D₁ = HeckeCoset.toSet D₂) : D₁ = D₂ := by
  revert h
  refine Quotient.ind₂ (motive := fun D₁ D₂ ↦
    HeckeCoset.toSet D₁ = HeckeCoset.toSet D₂ → D₁ = D₂)
    (fun g₁ g₂ h ↦ ?_) D₁ D₂
  simp only [HeckeCoset.toSet_mk] at h
  exact Quotient.sound h

/-- The stabilizer quotient for the identity double coset is trivial. -/
lemma decompQuot_one_eq_top :
    (ConjAct.toConjAct ((HeckeCoset.one P).rep : G) • P.H).subgroupOf P.H = ⊤ := by
  have h := HeckeCoset.one_rep_mem_H P
  rw [Subgroup.subgroupOf_eq_top]
  intro x hx
  rw [← @SetLike.mem_coe]
  simp only [Subgroup.coe_pointwise_smul]
  rw [conjAct_smul_coe_eq, Subgroup.singleton_mul_subgroup h,
    Subgroup.subgroup_mul_singleton (by simp [h])]
  exact hx

/-- The decomposition quotient for `HeckeCoset.one` is nonempty. -/
lemma one_in_decompQuot_one :
    Nonempty (decompQuot P (HeckeCoset.one P).rep) :=
  ⟨(1 : P.H)⟩

/-- The decomposition quotient for `HeckeCoset.one` is a subsingleton. -/
lemma subsingleton_decompQuot_one :
    Subsingleton (decompQuot P (HeckeCoset.one P).rep) := by
  unfold decompQuot
  rw [decompQuot_one_eq_top]
  exact QuotientGroup.subsingleton_quotient_top

private lemma conjAct_mem_of_leftCoset_eq (d : Δ) (h h' : H)
    (hyp : {(h : G)} * {(d : G)} * (H : Set G) =
      {(h' : G)} * {(d : G)} * (H : Set G)) :
    (h')⁻¹ * h ∈ (ConjAct.toConjAct (d : G) • H).subgroupOf H := by
  have h_mem_lhs : (h : G) * (d : G) ∈ {(h : G)} * {(d : G)} * (H : Set G) := by
    rw [Set.singleton_mul_singleton]
    exact ⟨(h : G) * (d : G), Set.mem_singleton _, 1, H.one_mem, by simp⟩
  rw [hyp, Set.singleton_mul_singleton] at h_mem_lhs
  obtain ⟨_, rfl, k, hk, hkk⟩ := h_mem_lhs
  have hkk' : ↑h' * ↑d * k = ↑h * ↑d := hkk
  have key : (h' : G)⁻¹ * (h : G) = (d : G) * k * (d : G)⁻¹ := by
    apply mul_right_cancel (b := (d : G))
    rw [mul_assoc, mul_assoc, inv_mul_cancel, mul_one]
    apply mul_left_cancel (a := (h' : G))
    rw [mul_inv_cancel_left, ← mul_assoc]
    exact hkk'.symm
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.smul_def]
  simp only [map_inv, ConjAct.ofConjAct_toConjAct, Subgroup.coe_mul,
    Subgroup.coe_inv]
  rw [inv_inv, key]
  simp only [mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left]
  exact hk

/-- Distinct elements of `decompQuot` give distinct left cosets. -/
lemma decompQuot_coset_diff (g : P.Δ) (i j : decompQuot P g) (hij : i ≠ j) :
    {((i.out : G) * (g : G))} * (P.H : Set G) ≠ {((j.out : G) * (g : G))} * (P.H : Set G) := by
  intro h
  simp_rw [← Set.singleton_mul_singleton] at h
  have := conjAct_mem_of_leftCoset_eq P.H P.Δ g i.out j.out h
  rw [← @QuotientGroup.leftRel_apply, ← @Quotient.eq''] at this
  simp only [Quotient.out_eq'] at this
  exact hij this.symm

/-- Two left cosets that are not disjoint must be equal. -/
lemma leftCoset_eq_of_not_disjoint (f g : G)
    (h : ¬ Disjoint (g • (H : Set G)) (f • H)) :
    {g} * (H : Set G) = {f} * H := by
  simp_rw [← Set.singleton_smul] at *
  rw [not_disjoint_iff] at h
  obtain ⟨a, ha, ha2⟩ := h
  simp only [smul_eq_mul, singleton_mul, image_mul_left, mem_preimage,
    SetLike.mem_coe] at ha ha2
  ext Y
  simp only [singleton_mul, image_mul_left, mem_preimage, SetLike.mem_coe]
  simp_rw [← QuotientGroup.eq] at *
  rw [← ha] at ha2
  rw [ha2]

/-- The map sending a pair of coset representatives `(σᵢ, τⱼ)` to the double coset
of their product `H(σᵢ τⱼ)H`. -/
noncomputable def mulMap (g₁ g₂ : P.Δ) (i : decompQuot P g₁ × decompQuot P g₂) :
    HeckeCoset P :=
  ⟦⟨i.1.out * g₁ * (i.2.out * g₂),
    Submonoid.mul_mem _ (Submonoid.mul_mem _ (P.h₀ i.1.out.2) g₁.2)
      (Submonoid.mul_mem _ (P.h₀ i.2.out.2) g₂.2)⟩⟧

/-- Shimura's multiplicity (Proposition 3.2): `heckeMultiplicity g₁ g₂ d` counts pairs
`(i, j)` such that `σᵢ τⱼ H = ξ H`. -/
noncomputable def heckeMultiplicity (g₁ g₂ d : P.Δ) : ℤ :=
  Nat.card {⟨i, j⟩ : decompQuot P g₁ × decompQuot P g₂ |
    ({(i.out : G) * (g₁ : G)} : Set G) * {(j.out : G) * (g₂ : G)} * P.H =
      {(d : G)} * (P.H : Set G)}

/-- The finite set of double cosets appearing in the product `D₁ * D₂`. -/
noncomputable def mulSupport (g₁ g₂ : P.Δ) : Finset (HeckeCoset P) :=
  Finset.image (mulMap P g₁ g₂) ⊤

/-- If `σᵢ τⱼ H = ξ H` then the double coset of `σᵢ τⱼ` equals that of `ξ`. -/
lemma doubleCoset_eq_of_rightCoset_eq (g₁ g₂ d : P.Δ)
    (p : decompQuot P g₁ × decompQuot P g₂)
    (heq : ({(p.1.out : G) * (g₁ : G)} : Set G) * {(p.2.out : G) * (g₂ : G)} * P.H =
      {(d : G)} * (P.H : Set G)) :
    mulMap P g₁ g₂ p = (⟦d⟧ : HeckeCoset P) := by
  unfold mulMap
  change (⟦_⟧ : HeckeCoset P) = ⟦_⟧
  rw [HeckeCoset.eq_iff]
  have h_mem : (p.1.out : G) * (g₁ : G) * ((p.2.out : G) * (g₂ : G)) ∈
      ({(d : G)} : Set G) * (P.H : Set G) := by
    rw [← heq, Set.singleton_mul_singleton]
    exact ⟨_, rfl, 1, P.H.one_mem, by simp⟩
  obtain ⟨_, hd_eq, h, hh, hprod⟩ := h_mem
  simp only [Set.mem_singleton_iff] at hd_eq
  subst hd_eq
  dsimp only at hprod ⊢
  rw [← hprod]
  exact doubleCoset_mul_right_eq_self P ⟨h, hh⟩ _

/-- Left multiplication by a singleton set is cancellative. -/
lemma set_singleton_mul_left_cancel (a : G) {S T : Set G}
    (h : ({a} : Set G) * S = ({a} : Set G) * T) : S = T := by
  rw [Set.singleton_mul, Set.singleton_mul] at h
  exact Set.image_injective.mpr (mul_right_injective a) h

/-- When the first-component representatives agree, the second-component
representatives must also agree (by left-cancellation on the common prefix). -/
lemma decompQuot_snd_eq_of_fst_eq (g₁ g₂ d : P.Δ) (i : decompQuot P g₁)
    (j₁ j₂ : decompQuot P g₂)
    (h₁ : ({(i.out : G) * (g₁ : G)} : Set G) * {(j₁.out : G) * (g₂ : G)} * P.H =
      {(d : G)} * (P.H : Set G))
    (h₂ : ({(i.out : G) * (g₁ : G)} : Set G) * {(j₂.out : G) * (g₂ : G)} * P.H =
      {(d : G)} * (P.H : Set G)) :
    j₁ = j₂ := by
  by_contra hne
  refine decompQuot_coset_diff P g₂ j₁ j₂ hne
    (set_singleton_mul_left_cancel ((i.out : G) * (g₁ : G)) ?_)
  have := h₁.trans h₂.symm
  rwa [mul_assoc, mul_assoc] at this

/-- When `j.out * g₂ ∈ H`, the second factor collapses and
first-component injectivity follows from coset disjointness. -/
lemma decompQuot_fst_eq_of_snd_mem_H (g₁ g₂ d : P.Δ) (i₁ i₂ : decompQuot P g₁)
    (j : decompQuot P g₂) (hj : (j.out : G) * (g₂ : G) ∈ P.H)
    (h₁ : ({(i₁.out : G) * (g₁ : G)} : Set G) * {(j.out : G) * (g₂ : G)} * P.H =
      {(d : G)} * (P.H : Set G))
    (h₂ : ({(i₂.out : G) * (g₁ : G)} : Set G) * {(j.out : G) * (g₂ : G)} * P.H =
      {(d : G)} * (P.H : Set G)) :
    i₁ = i₂ := by
  by_contra hne
  refine decompQuot_coset_diff P g₁ i₁ i₂ hne ?_
  simp only [mul_assoc, Subgroup.singleton_mul_subgroup hj] at h₁ h₂
  exact h₁.trans h₂.symm

end HeckeRing
