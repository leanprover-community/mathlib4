/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.HeckeRing.Multiplicity

/-!
# Hecke rings: the multiplicity of the identity double coset

The identity double coset `HeckeCoset.one` acts as the unit for the Hecke product. This file proves
the two computations that express this at the level of Shimura's multiplicity: for the identity on
either side, `heckeMultiplicity` is `1` exactly on the diagonal `⟦g⟧ = ⟦d⟧` and `0` elsewhere.

## Main results

* `HeckeRing.heckeMultiplicity_mul_one`: `⟦g⟧ = ⟦d⟧ ↔ heckeMultiplicity g (one).rep d = 1`.
* `HeckeRing.heckeMultiplicity_one_mul`: `⟦g⟧ = ⟦d⟧ ↔ heckeMultiplicity (one).rep g d = 1`.
-/

@[expose] public section

open Set DoubleCoset Subgroup
open scoped Pointwise

namespace HeckeRing

variable {G : Type*} [Group G]

attribute [local instance] doubleCosetSetoid

/-- Membership in `(ConjAct.toConjAct a • H).subgroupOf H` unfolds to conjugation by `a`
landing back in `H`. -/
lemma inv_mul_mul_mem_of_mem_subgroupOf (H : Subgroup G) {a : G}
    (x : (ConjAct.toConjAct a • H).subgroupOf H) : a⁻¹ * (x.val : G) * a ∈ H := by
  have := x.2
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.smul_def] at this
  simpa [ConjAct.ofConjAct_toConjAct] using this

variable (P : HeckePair G)

/-- If `Hg₁H = HdH`, the fibre defining the multiplicity for right multiplication by the
identity double coset is nonempty. -/
private lemma nonempty_mul_one_witness_of_doubleCoset_eq (g₁ d : P.Δ)
    (hg₁d : DoubleCoset.doubleCoset (g₁ : G) P.H P.H =
      DoubleCoset.doubleCoset (d : G) P.H P.H) :
    Nonempty ↑{x : decompQuot P g₁ × decompQuot P (HeckeCoset.one P).rep |
      ({(↑x.1.out : G) * (↑g₁ : G)} : Set G) *
        {(↑x.2.out : G) * (↑(HeckeCoset.one P).rep : G)} * P.H =
        {(↑d : G)} * (P.H : Set G)} := by
  have hd_in_g₁ : (↑d : G) ∈ doubleCoset (↑g₁ : G) P.H P.H :=
    hg₁d ▸ DoubleCoset.mem_doubleCoset_self P.H P.H _
  rw [doubleCoset_eq_iUnion_leftCosets] at hd_in_g₁
  simp only [Set.mem_iUnion] at hd_in_g₁
  obtain ⟨k, hk⟩ := hd_in_g₁
  rw [smul_eq_singleton_mul] at hk
  obtain ⟨j₀⟩ := one_in_decompQuot_one P
  refine ⟨⟨(k, j₀), ?_⟩⟩
  simp only [Set.mem_setOf_eq]
  have hmem : (j₀.out : G) * ((HeckeCoset.one P).rep : G) ∈ P.H :=
    Subgroup.mul_mem _ (SetLike.coe_mem j₀.out) (HeckeCoset.one_rep_mem_H P)
  rw [mul_assoc, Subgroup.singleton_mul_subgroup hmem]
  apply (leftCoset_eq_of_not_disjoint (H := P.H) _ _ _).symm
  rw [not_disjoint_iff]
  refine ⟨↑d, Set.mem_smul_set.mpr ⟨1, P.H.one_mem, by simp⟩, ?_⟩
  rw [Set.mem_smul_set]
  rw [singleton_mul] at hk
  simp only [image_mul_left, mem_preimage, SetLike.mem_coe] at hk
  exact ⟨(↑k.out * (↑g₁ : G))⁻¹ * ↑d, hk,
    show (↑k.out * (↑g₁ : G)) * ((↑k.out * ↑g₁)⁻¹ * ↑d) = ↑d by group⟩

/-- Right multiplication by the identity double coset sends every pair of representatives
to `⟦g₁⟧`. -/
lemma mulMap_mul_one_eq (g₁ : P.Δ) (i : decompQuot P g₁)
    (j : decompQuot P (HeckeCoset.one P).rep) :
    mulMap P g₁ (HeckeCoset.one P).rep (i, j) = (⟦g₁⟧ : HeckeCoset P) := by
  unfold mulMap
  change (⟦_⟧ : HeckeCoset P) = ⟦_⟧
  rw [HeckeCoset.eq_iff]
  dsimp only
  rw [mul_assoc, doubleCoset_mul_left_eq_self]
  apply doubleCoset_mul_right_eq_self P
    ⟨j.out * (HeckeCoset.one P).rep,
      Subgroup.mul_mem _ (by simp) (HeckeCoset.one_rep_mem_H P)⟩

/-- Right multiplication by `HeckeCoset.one` has multiplicity `1` on the diagonal and `0`
elsewhere. -/
lemma heckeMultiplicity_mul_one (g₁ d : P.Δ) :
    (⟦g₁⟧ : HeckeCoset P) = ⟦d⟧ ↔
      heckeMultiplicity P g₁ (HeckeCoset.one P).rep d = 1 := by
  constructor
  · intro h
    have hg₁d : DoubleCoset.doubleCoset (g₁ : G) P.H P.H =
        DoubleCoset.doubleCoset (d : G) P.H P.H := (HeckeCoset.eq_iff g₁ d).mp h
    simp only [heckeMultiplicity]
    norm_cast
    rw [Nat.card_eq_one_iff_unique]
    have : Subsingleton (decompQuot P (HeckeCoset.one P).rep) :=
      subsingleton_decompQuot_one P
    refine ⟨⟨?_⟩, nonempty_mul_one_witness_of_doubleCoset_eq P g₁ d hg₁d⟩
    intro ⟨⟨i₁, j₁⟩, h₁⟩ ⟨⟨i₂, j₂⟩, h₂⟩
    have hj : j₁ = j₂ := Subsingleton.elim j₁ j₂
    subst hj
    simp only [Set.mem_setOf_eq] at h₁ h₂
    exact Subtype.ext (Prod.ext
      (decompQuot_fst_eq_of_snd_mem_H P g₁ (HeckeCoset.one P).rep d i₁ i₂ j₁
        (Subgroup.mul_mem _ (SetLike.coe_mem j₁.out) (HeckeCoset.one_rep_mem_H P)) h₁ h₂)
      rfl)
  · intro hm
    by_contra hne
    have : heckeMultiplicity P g₁ (HeckeCoset.one P).rep d = 0 := by
      simp only [heckeMultiplicity, Nat.cast_eq_zero, Nat.card_eq_zero, isEmpty_subtype]
      left
      intro ⟨i, j⟩ heq
      exact hne ((mulMap_mul_one_eq P g₁ i j).symm.trans
        (doubleCoset_eq_of_rightCoset_eq P g₁ (HeckeCoset.one P).rep d (i, j) heq))
    omega

/-- Left multiplication by the identity double coset sends every pair of representatives
to `⟦g₁⟧`. -/
lemma mulMap_one_mul_eq (g₁ : P.Δ) (i : decompQuot P (HeckeCoset.one P).rep)
    (j : decompQuot P g₁) :
    mulMap P (HeckeCoset.one P).rep g₁ (i, j) = (⟦g₁⟧ : HeckeCoset P) := by
  unfold mulMap
  change (⟦_⟧ : HeckeCoset P) = ⟦_⟧
  rw [HeckeCoset.eq_iff]
  dsimp only
  rw [mul_assoc]
  simp_rw [doubleCoset_mul_left_eq_self,
    doubleCoset_mul_left_eq_self P ⟨(HeckeCoset.one P).rep, HeckeCoset.one_rep_mem_H P⟩,
    doubleCoset_mul_left_eq_self]

/-- If `Hg₁H = HdH`, the fibre defining the multiplicity for left multiplication by the
identity double coset is nonempty. -/
private lemma nonempty_one_mul_witness_of_doubleCoset_eq (g₁ d : P.Δ)
    (hg₁d : DoubleCoset.doubleCoset (g₁ : G) P.H P.H =
      DoubleCoset.doubleCoset (d : G) P.H P.H) :
    Nonempty ↑{x : decompQuot P (HeckeCoset.one P).rep × decompQuot P g₁ |
      ({(↑x.1.out : G) * (↑(HeckeCoset.one P).rep : G)} : Set G) *
        {(↑x.2.out : G) * (↑g₁ : G)} * P.H = {(↑d : G)} * (P.H : Set G)} := by
  have hd_in : (↑d : G) ∈ doubleCoset (↑g₁ : G) P.H P.H :=
    hg₁d ▸ DoubleCoset.mem_doubleCoset_self P.H P.H _
  rw [doubleCoset_eq_iUnion_leftCosets] at hd_in
  simp only [Set.mem_iUnion] at hd_in
  obtain ⟨j', hj'⟩ := hd_in
  rw [smul_eq_singleton_mul, singleton_mul] at hj'
  simp only [image_mul_left, mem_preimage, SetLike.mem_coe] at hj'
  obtain ⟨i₀⟩ := one_in_decompQuot_one P
  have h₀_mem : (↑i₀.out : G) * ((HeckeCoset.one P).rep : G) ∈ P.H :=
    Subgroup.mul_mem _ (SetLike.coe_mem i₀.out) (HeckeCoset.one_rep_mem_H P)
  set h₀ := ↑i₀.out * ((HeckeCoset.one P).rep : G) with hh₀_def
  set j₀ : decompQuot P g₁ :=
    ⟦⟨h₀⁻¹ * ↑j'.out, P.H.mul_mem (P.H.inv_mem h₀_mem) j'.out.2⟩⟧
  obtain ⟨n, hn_eq⟩ := QuotientGroup.mk_out_eq_mul
    ((ConjAct.toConjAct (↑g₁ : G) • P.H).subgroupOf P.H)
    ⟨h₀⁻¹ * ↑j'.out, P.H.mul_mem (P.H.inv_mem h₀_mem) j'.out.2⟩
  have hn_coe : (j₀.out : G) = h₀⁻¹ * ↑j'.out * (n : G) := by
    have := congr_arg (Subtype.val : ↥P.H → G) hn_eq
    simpa [Subgroup.coe_mul] using this
  have hn_conj : (↑g₁ : G)⁻¹ * (n : G) * ↑g₁ ∈ P.H :=
    inv_mul_mul_mem_of_mem_subgroupOf P.H n
  refine ⟨⟨(i₀, j₀), ?_⟩⟩
  simp only [Set.mem_setOf_eq, Set.singleton_mul_singleton]
  apply (leftCoset_eq_of_not_disjoint (H := P.H) _ _ _).symm
  rw [not_disjoint_iff]
  refine ⟨↑d, Set.mem_smul_set.mpr ⟨1, P.H.one_mem, by simp⟩, ?_⟩
  rw [Set.mem_smul_set]
  refine ⟨(h₀ * ↑j₀.out * (↑g₁ : G))⁻¹ * ↑d, ?_, by
    change (↑i₀.out * (HeckeCoset.one P).rep * (↑j₀.out * (↑g₁ : G))) *
      ((h₀ * ↑j₀.out * ↑g₁)⁻¹ * ↑d) = ↑d
    simp only [hh₀_def]
    group⟩
  change (h₀ * ↑j₀.out * (↑g₁ : G))⁻¹ * ↑d ∈ P.H
  have key : (h₀ * ↑j₀.out * (↑g₁ : G))⁻¹ * ↑d =
      ((↑g₁ : G)⁻¹ * (↑n : G)⁻¹ * ↑g₁) *
        ((↑j'.out * (↑g₁ : G))⁻¹ * ↑d) := by
    rw [hn_coe]
    group
  rw [key]
  exact P.H.mul_mem (by convert P.H.inv_mem hn_conj using 1; group) hj'

/-- Left multiplication by `HeckeCoset.one` has multiplicity `1` on the diagonal and `0`
elsewhere. -/
lemma heckeMultiplicity_one_mul (g₁ d : P.Δ) :
    (⟦g₁⟧ : HeckeCoset P) = ⟦d⟧ ↔
      heckeMultiplicity P (HeckeCoset.one P).rep g₁ d = 1 := by
  constructor
  · intro h
    have hg₁d : DoubleCoset.doubleCoset (g₁ : G) P.H P.H =
        DoubleCoset.doubleCoset (d : G) P.H P.H := (HeckeCoset.eq_iff g₁ d).mp h
    simp only [heckeMultiplicity]
    norm_cast
    rw [Nat.card_eq_one_iff_unique]
    have : Subsingleton (decompQuot P (HeckeCoset.one P).rep) :=
      subsingleton_decompQuot_one P
    refine ⟨⟨?_⟩, nonempty_one_mul_witness_of_doubleCoset_eq P g₁ d hg₁d⟩
    intro ⟨⟨i₁, j₁⟩, h₁⟩ ⟨⟨i₂, j₂⟩, h₂⟩
    have hi : i₁ = i₂ := Subsingleton.elim i₁ i₂
    subst hi
    simp only [Set.mem_setOf_eq] at h₁ h₂
    exact Subtype.ext (Prod.ext rfl
      (decompQuot_snd_eq_of_fst_eq P (HeckeCoset.one P).rep g₁ d i₁ j₁ j₂ h₁ h₂))
  · intro hm
    by_contra hne
    have : heckeMultiplicity P (HeckeCoset.one P).rep g₁ d = 0 := by
      simp only [heckeMultiplicity, Nat.cast_eq_zero, Nat.card_eq_zero, isEmpty_subtype]
      left
      intro ⟨i, j⟩ heq
      exact hne ((mulMap_one_mul_eq P g₁ i j).symm.trans
        (doubleCoset_eq_of_rightCoset_eq P (HeckeCoset.one P).rep g₁ d (i, j) heq))
    omega

end HeckeRing
