/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.HeckeRing.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

/-!
# Hecke rings: the double coset API

Basic API for the double cosets `HeckeCoset` that index an abstract Hecke ring, following
Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Ch. 3. This file develops
representatives of double cosets, the characterisation of when two elements give the same double
coset, the decomposition of a double coset into left cosets of `H`, and the finite decomposition
quotient `H / (H ∩ gHg⁻¹)` used to define the Hecke product in later files.

## Main definitions

* `HeckeCoset.toSet`: the underlying set `HgH` of a double coset.
* `HeckeCoset.rep`: a chosen representative in `Δ`.
* `HeckeCoset.one`: the identity double coset `H1H = H`.
* `HeckeRing.decompQuot`: the finite quotient `H / (H ∩ gHg⁻¹)` indexing the left cosets in `HgH`.

## Main results

* `HeckeCoset.eq_iff`: `⟦g⟧ = ⟦h⟧ ↔ HgH = HhH`.
* `HeckeRing.doubleCoset_eq_iUnion_leftCosets`: a double coset `HgH` as a union of left cosets.

## Implementation notes

`HeckeRing.doubleCosetSetoid` is a `def`, not a global instance; this file opts in to it with
`attribute [local instance]` so that the quotient notation `⟦·⟧` is available for `HeckeCoset`.
-/

@[expose] public section

open Set DoubleCoset Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

attribute [local instance] doubleCosetSetoid

variable (H : Subgroup G)

namespace HeckeRing

/-- The conjugation action on `H` as a set product: `gHg⁻¹ = {g} * H * {g⁻¹}`. -/
lemma conjAct_smul_coe_eq (g : G) :
    ((ConjAct.toConjAct g • H) : Set G) = {g} * H * {g⁻¹} := by
  ext x
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨a, ha⟩ := Set.mem_smul_set.mp h
    rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct] at ha
    rw [← ha.2]
    simp only [singleton_mul, image_mul_left, mul_singleton, image_mul_right,
      inv_inv, mem_preimage, inv_mul_cancel_right, inv_mul_cancel_left, ha.1]
  · refine Set.mem_smul_set.mpr ⟨g⁻¹ * x * g, ?_,
      by rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct]; group⟩
    simp only [singleton_mul, image_mul_left, mul_singleton, image_mul_right,
      inv_inv, mem_preimage, SetLike.mem_coe] at *
    rwa [← mul_assoc] at h

/-- Conjugation by an element of `H` fixes `H`. -/
lemma conjAct_smul_elt_eq (h : H) : ConjAct.toConjAct (h : G) • H = H := by
  have : ConjAct.toConjAct (h : G) • (H : Set G) = H := by
    rw [conjAct_smul_coe_eq, Subgroup.singleton_mul_subgroup h.2,
      Subgroup.subgroup_mul_singleton (by simp)]
  rw [← Subgroup.coe_pointwise_smul] at this; exact_mod_cast this

/-- Scalar multiplication by a group element is the same as singleton set multiplication. -/
lemma smul_eq_singleton_mul (s : Set G) (g : G) : g • s = {g} * s :=
  Set.singleton_smul.symm

/-- A subgroup `H` is the union of left cosets of any sub-subgroup `K ≤ H`. -/
lemma set_eq_iUnion_leftCosets (K : Subgroup G) (hK : K ≤ H) :
    (H : Set G) = ⋃ (i : H ⧸ K.subgroupOf H), (i.out : G) • (K : Set G) := by
  ext a
  refine ⟨fun ha ↦ ?_, fun ha ↦ ?_⟩
  · simp only [Set.mem_iUnion]
    refine ⟨(⟨a, ha⟩ : H), ?_⟩
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (K.subgroupOf H) (⟨a, ha⟩ : H)
    rw [hh]
    simp only [coe_mul]
    refine Set.mem_smul_set.mpr ⟨h⁻¹, ?_, ?_⟩
    · simpa using Subgroup.mem_subgroupOf.mp (SetLike.coe_mem h)
    · simp
  · simp only [Set.mem_iUnion] at ha
    obtain ⟨i, h, hh, rfl⟩ := ha
    change ((Quotient.out i : H) : G) * h ∈ H
    exact mul_mem (by simp) (hK hh)

/-- The conjugate subgroup `gHg⁻¹` is closed under multiplication. -/
lemma conjAct_mul_self_eq_self (g : G) :
    ((ConjAct.toConjAct g • H) : Set G) * (ConjAct.toConjAct g • H) =
    (ConjAct.toConjAct g • H) := by
  rw [conjAct_smul_coe_eq,
    show {g} * (H : Set G) * {g⁻¹} * ({g} * ↑H * {g⁻¹}) =
      {g} * ↑H * (({g⁻¹} * {g}) * ↑H) * {g⁻¹} by simp_rw [← mul_assoc],
    Set.singleton_mul_singleton]
  conv => enter [1, 1, 2]; simp only [inv_mul_cancel, Set.singleton_one, one_mul]
  conv => enter [1, 1]; rw [mul_assoc, coe_mul_coe H]

/-- The intersection `H ∩ gHg⁻¹` acts trivially on `gHg⁻¹` by left multiplication. -/
lemma inter_mul_conjAct_eq_conjAct (g : G) :
    ((H : Set G) ∩ (ConjAct.toConjAct g • H)) * (ConjAct.toConjAct g • H) =
    (ConjAct.toConjAct g • H) :=
  Subset.antisymm
    (le_trans (Set.inter_mul_subset (s₁ := (H : Set G))
      (s₂ := (ConjAct.toConjAct g • H)) (t := (ConjAct.toConjAct g • H)))
      (by simp [conjAct_mul_self_eq_self]))
    (subset_mul_right _ ⟨Subgroup.one_mem H, Subgroup.one_mem (ConjAct.toConjAct g • H)⟩)

/-- Right multiplication by a singleton is cancellative. -/
lemma mul_singleton_right_cancel (g : G) (K L : Set G) (h : K * {g} = L * {g}) : K = L := by
  have h2 := congrFun (congrArg HMul.hMul h) {g⁻¹}
  simp_rw [mul_assoc, Set.singleton_mul_singleton] at h2; simpa using h2

/-- A double coset `HgH` decomposes as a union of left cosets of `H`. -/
lemma doubleCoset_eq_iUnion_leftCosets (g : G) :
    DoubleCoset.doubleCoset g H H =
    ⋃ (i : H ⧸ (ConjAct.toConjAct g • H).subgroupOf H),
      (i.out * g) • (H : Set G) := by
  rw [DoubleCoset.doubleCoset]
  have := set_eq_iUnion_leftCosets H
    (((ConjAct.toConjAct g • H).subgroupOf H).map H.subtype)
  simp only [Subgroup.subgroupOf_map_subtype, inf_le_right, Subgroup.coe_inf,
    Subgroup.coe_pointwise_smul, true_implies] at this
  have h2 := congrFun (congrArg HMul.hMul this)
    ((ConjAct.toConjAct g • H) : Set G)
  rw [Set.iUnion_mul, inter_comm] at h2
  apply mul_singleton_right_cancel g⁻¹
  rw [conjAct_smul_coe_eq] at *
  simp_rw [← mul_assoc] at h2
  rw [h2, show (Subgroup.map H.subtype
    ((ConjAct.toConjAct g • H).subgroupOf H)).subgroupOf H =
    (ConjAct.toConjAct g • H).subgroupOf H by simp]
  have h1 : ∀ (i : H ⧸ (ConjAct.toConjAct g • H).subgroupOf H),
      ((i.out) : G) • ((H : Set G) ∩ ({g} * ↑H * {g⁻¹})) *
        {g} * ↑H * {g⁻¹} =
      (↑(Quotient.out i) * g) • ↑H * {g⁻¹} := by
    intro i
    have := inter_mul_conjAct_eq_conjAct H g
    rw [conjAct_smul_coe_eq] at this
    simp_rw [smul_mul_assoc]
    simp_rw [← mul_assoc] at this
    conv => enter [1, 2]; rw [this]
    simp_rw [smul_eq_singleton_mul, ← Set.singleton_mul_singleton, ← mul_assoc]
  convert Set.iUnion_congr h1
  rw [Set.iUnion_mul]

end HeckeRing

namespace HeckeCoset

variable {P : HeckePair G}

/-- The underlying set `HgH`, well-defined on the quotient. -/
noncomputable def toSet (D : HeckeCoset P) : Set G :=
  Quotient.lift (fun (g : P.Δ) ↦ DoubleCoset.doubleCoset (g : G) P.H P.H) (fun _ _ h ↦ h) D

/-- A representative `g : Δ` (via `Quotient.out`). -/
noncomputable def rep (D : HeckeCoset P) : P.Δ := Quotient.out D

/-- The representative of a `HeckeCoset` maps back to the coset under `⟦·⟧`. -/
lemma mk_rep (D : HeckeCoset P) : (⟦HeckeCoset.rep D⟧ : HeckeCoset P) = D :=
  Quotient.out_eq D

/-- `⟦g⟧ = ⟦h⟧ ↔ HgH = HhH`. -/
lemma eq_iff (g h : P.Δ) : (⟦g⟧ : HeckeCoset P) = ⟦h⟧ ↔
    DoubleCoset.doubleCoset (g : G) P.H P.H = DoubleCoset.doubleCoset (h : G) P.H P.H :=
  Quotient.eq

/-- The carrier set of `⟦g⟧` is definitionally `HgH`. -/
@[simp] lemma toSet_mk (g : P.Δ) :
    HeckeCoset.toSet (⟦g⟧ : HeckeCoset P) = DoubleCoset.doubleCoset (g : G) P.H P.H := rfl

/-- The carrier set equals the double coset of the representative. -/
lemma toSet_eq_rep (D : HeckeCoset P) :
    HeckeCoset.toSet D = DoubleCoset.doubleCoset (HeckeCoset.rep D : G) P.H P.H := by
  refine Quotient.inductionOn D fun g ↦ ?_
  simpa only [toSet_mk, HeckeCoset.rep] using
    (Quotient.exact (Quotient.out_eq (⟦g⟧ : HeckeCoset P))).symm

/-- The representative lies in its double coset. -/
lemma rep_mem (D : HeckeCoset P) : (HeckeCoset.rep D : G) ∈ HeckeCoset.toSet D :=
  toSet_eq_rep D ▸ DoubleCoset.mem_doubleCoset_self P.H P.H _

/-- If `x ∈ HgH`, then `HxH = HgH`. The fundamental double coset absorption lemma. -/
lemma doubleCoset_eq_of_mem {g : P.Δ} {x : G}
    (hx : x ∈ DoubleCoset.doubleCoset (g : G) P.H P.H) :
    DoubleCoset.doubleCoset x P.H P.H = DoubleCoset.doubleCoset (g : G) P.H P.H := by
  obtain ⟨_, ⟨l, hl, _, rfl, rfl⟩, r, hr, rfl⟩ := hx
  simp only [DoubleCoset.doubleCoset]
  ext y; simp only [Set.mem_mul, Set.mem_singleton_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨_, ⟨a, ha, _, rfl, rfl⟩, b, hb, rfl⟩
    exact ⟨_, ⟨a * l, P.H.mul_mem ha hl, _, rfl, rfl⟩, r * b, P.H.mul_mem hr hb, by group⟩
  · rintro ⟨_, ⟨a, ha, _, rfl, rfl⟩, b, hb, rfl⟩
    exact ⟨_, ⟨a * l⁻¹, P.H.mul_mem ha (P.H.inv_mem hl), _, rfl, rfl⟩,
      r⁻¹ * b, P.H.mul_mem (P.H.inv_mem hr) hb, by group⟩

/-- `⟦g₁⟧ = ⟦g₂⟧` when `g₁` is in the double coset of `g₂`. -/
lemma eq_mk_of_mem {g₁ g₂ : P.Δ}
    (h : (g₁ : G) ∈ DoubleCoset.doubleCoset (g₂ : G) P.H P.H) :
    (⟦g₁⟧ : HeckeCoset P) = ⟦g₂⟧ :=
  (eq_iff g₁ g₂).mpr (doubleCoset_eq_of_mem h)

/-- The identity double coset `H1H = H`. -/
def one (P : HeckePair G) : HeckeCoset P := ⟦⟨1, P.Δ.one_mem⟩⟧

/-- Induction: to prove something for all double cosets, prove it for `⟦g⟧`. -/
protected lemma ind {motive : HeckeCoset P → Prop}
    (h : ∀ g : P.Δ, motive ⟦g⟧) : ∀ D, motive D := Quotient.ind h

/-- Two-argument induction. -/
protected lemma ind₂ {motive : HeckeCoset P → HeckeCoset P → Prop}
    (h : ∀ g₁ g₂ : P.Δ, motive ⟦g₁⟧ ⟦g₂⟧) :
    ∀ D₁ D₂, motive D₁ D₂ := Quotient.ind₂ h

/-- The representative of `HeckeCoset.one` belongs to `H`. -/
lemma one_rep_mem_H (P : HeckePair G) : ((one P).rep : G) ∈ P.H := by
  have hm := rep_mem (one P)
  rw [toSet_eq_rep,
    show DoubleCoset.doubleCoset ((rep (one P)) : G) P.H P.H =
      DoubleCoset.doubleCoset (1 : G) P.H P.H from
    Quotient.exact (Quotient.out_eq (⟦⟨(1 : G), P.Δ.one_mem⟩⟧ : HeckeCoset P)),
    mem_doubleCoset] at hm
  obtain ⟨a, ha, b, hb, hab⟩ := hm
  rw [mul_one] at hab
  exact hab ▸ P.H.mul_mem ha hb

end HeckeCoset

namespace HeckeRing

/-- Left-multiplying the representative by an element of `H` does not change the double coset. -/
lemma doubleCoset_mul_left_eq_self (P : HeckePair G) (h : P.H) (g : G) :
    DoubleCoset.doubleCoset ((h : G) * g) P.H P.H =
    DoubleCoset.doubleCoset g P.H P.H := by
  simp_rw [DoubleCoset.doubleCoset, ← Set.singleton_mul_singleton, ← mul_assoc]
  conv => enter [1, 1, 1]; rw [Subgroup.subgroup_mul_singleton h.2]

/-- Right-multiplying the representative by an element of `H` does not change the double coset. -/
lemma doubleCoset_mul_right_eq_self (P : HeckePair G)
    (h : P.H) (g : G) : DoubleCoset.doubleCoset (g * h) P.H P.H =
    DoubleCoset.doubleCoset g P.H P.H := by
  simp_rw [DoubleCoset.doubleCoset, ← Set.singleton_mul_singleton, ← mul_assoc]
  conv => enter [1]; rw [mul_assoc, Subgroup.singleton_mul_subgroup h.2]

/-- The decomposition quotient `H / (H ∩ gHg⁻¹)` for a concrete `g : Δ`.
Indexes the left cosets in the decomposition of `HgH`. -/
abbrev decompQuot (P : HeckePair G) (g : P.Δ) :=
  P.H ⧸ (ConjAct.toConjAct (g : G) • P.H).subgroupOf P.H

/-- The decomposition quotient is finite because `Δ ≤ commensurator H`. -/
noncomputable instance (P : HeckePair G) (g : P.Δ) :
    Fintype (decompQuot P g) :=
  Subgroup.fintypeOfIndexNeZero (P.h₁ g.2).1

/-- Products of the form `a * h * b` with `h ∈ H`, `a, b ∈ Δ` remain in `Δ`. -/
lemma delta_mul_mem (Δ : Submonoid G) (i : H) (a b : Δ) (h₀ : H.toSubmonoid ≤ Δ) :
    a * (i : G) * b ∈ Δ := by
  rw [mul_assoc]; exact Submonoid.mul_mem _ a.2 (Submonoid.mul_mem _ (h₀ i.2) b.2)

end HeckeRing
