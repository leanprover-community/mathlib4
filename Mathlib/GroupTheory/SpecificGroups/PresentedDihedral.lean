/-
Copyright (c) 2023 Newell Jensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Newell Jensen
-/
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-
# Presentation of Dihedral Groups

This file defines a group presentation of the dihedral groups, `PresentedDihedralGroup n`,
using the presentation `⟨a, b | a² = 1, b² = 1, (a * b)ⁿ = 1⟩`.

## Main definitions

* TODO

## Main results

* `PresentedDihedralGroup n ≃* DihedralGroup n` proves that `PresentedDihedralGroup n` is
  isomorphic to `DihedralGroup n`.

## References

* https://en.wikipedia.org/wiki/Presentation_of_a_group

## Tags
presentation group, dihedral group
-/


variable {n : ℕ}

inductive Generator (n : ℕ)
  | a : Generator n
  | b : Generator n
  deriving DecidableEq

namespace PresentedDihedralGroup

open DihedralGroup

def GenMap : Generator n → DihedralGroup n
  | Generator.a => sr 1
  | Generator.b => sr 1 * r 1

/-- Presentation ⟨a, b | a² = 1, b² = 1, (a * b)ⁿ = 1⟩  -/
def Rels (n : ℕ) : Set (FreeGroup (Generator n)) :=
  {FreeGroup.of Generator.a * FreeGroup.of Generator.a} ∪
  {FreeGroup.of Generator.b * FreeGroup.of Generator.b} ∪
  {(FreeGroup.of Generator.a * FreeGroup.of Generator.b) ^ n}

@[simp] abbrev PresentedDihedralGroup (n : ℕ) := PresentedGroup <| Rels n

lemma a_relsGenMap : (GenMap Generator.a) * (GenMap Generator.a) =
    (1 : DihedralGroup n) := by
  rw [GenMap]; split
  · simp only [sr_mul_sr, sub_self, one_def]
  · simp only [sr_mul_r, sr_mul_sr, sub_self, one_def]

lemma b_relsGenMap : (GenMap Generator.b) * (GenMap Generator.b) =
    (1 : DihedralGroup n) := by
  rw [GenMap]; split
  · simp only [sr_mul_sr, sub_self, one_def]
  · simp only [sr_mul_r, sr_mul_sr, sub_self, one_def]

lemma a_b_relsGenMap : ((GenMap Generator.a) * (GenMap Generator.b)) ^ n =
    (1 : DihedralGroup n) := by
  simp_rw [GenMap]
  simp only [sr_mul_r, sr_mul_sr, add_sub_cancel]
  cases n with
  | zero => simp only [Nat.zero_eq, pow_zero]
  | succ n => simp only [r_zpow_n]

theorem one_of_Rels : ∀ r ∈ Rels n, FreeGroup.lift GenMap r = 1 := by
  intro r hr
  simp only [Rels] at hr
  simp only [Set.union_singleton, Set.mem_singleton_iff, Set.mem_insert_iff] at hr
  rcases hr with hr₁ | hr₂ | hr₃
  · rw [hr₁]
    simp only [map_pow, map_mul, FreeGroup.lift.of, a_b_relsGenMap]
  · rw [hr₂]
    simp only [map_mul, FreeGroup.lift.of, b_relsGenMap]
  · rw [hr₃]
    simp only [map_mul, FreeGroup.lift.of, a_relsGenMap]

/-- Group presentation induced morphism to the DihedarlGroup n. -/
@[simp] theorem presentedGroupHom : PresentedDihedralGroup n →* DihedralGroup n :=
    PresentedGroup.toGroup (f := GenMap) one_of_Rels

lemma a_b_relsGenMapOf_pow {i : ℤ} : presentedGroupHom
    ((PresentedGroup.of Generator.a) * (PresentedGroup.of Generator.b)) ^ i =
    (r i : DihedralGroup n) := by
  unfold presentedGroupHom
  simp only [map_mul, PresentedGroup.toGroup.of]
  simp_rw [GenMap]
  simp only [sr_mul_r, sr_mul_sr, add_sub_cancel, r_one_zpow]

lemma a_a_b_relsGenMapOf_pow {i : ℤ} : presentedGroupHom
    ((PresentedGroup.of Generator.a) *
    ((PresentedGroup.of Generator.a) * (PresentedGroup.of Generator.b)) ^ (i - 1)) =
    (sr i : DihedralGroup n) := by
  unfold presentedGroupHom
  simp only [map_mul, PresentedGroup.toGroup.of, map_zpow]
  simp_rw [GenMap]
  simp only [sr_mul_r, sr_mul_sr, add_sub_cancel, r_one_zpow, Int.cast_sub,
    Int.cast_one, add_sub_cancel'_right]

@[simp]
lemma mk_mem_eq_one_of_mem_normalClosure {x : FreeGroup (Generator n)} :
    x ∈ Subgroup.normalClosure (Rels n) → QuotientGroup.mk x = (1 : PresentedDihedralGroup n) := by
  simp only [QuotientGroup.eq_one_iff, imp_self]

@[simp]
lemma a_b_npow_mem_normalClosure : (FreeGroup.of Generator.a * FreeGroup.of Generator.b) ^ n ∈
    Subgroup.normalClosure (Rels n) := by
  refine Subgroup.subset_normalClosure ?_
  simp only [Rels, Set.union_singleton, Set.mem_singleton_iff, Set.mem_insert_iff, true_or]

lemma a_b_zpow_mem_normalClosure_eq_identity :
    QuotientGroup.mk (FreeGroup.of Generator.a * FreeGroup.of Generator.b) ^ (n : ℤ) =
    (1 : PresentedDihedralGroup n) := by
  exact mk_mem_eq_one_of_mem_normalClosure a_b_npow_mem_normalClosure

lemma powLaw1 {i k : ZMod n} :
    QuotientGroup.mk ((FreeGroup.of Generator.a *
      FreeGroup.of Generator.b) ^ ((i + k : ZMod n) : ℤ)) =
    QuotientGroup.mk (s := Subgroup.normalClosure (Rels n))
    ((FreeGroup.of Generator.a * FreeGroup.of Generator.b) ^ (i : ℤ)) *
    QuotientGroup.mk ((FreeGroup.of Generator.a * FreeGroup.of Generator.b) ^ (k : ℤ)) := by
  have h1 := ZMod.coe_add_eq_ite i k
  symm at h1
  obtain ⟨h2, h3⟩ := ite_eq_iff'.mp h1
  push_neg at h3
  simp only [QuotientGroup.mk_zpow, QuotientGroup.mk_mul]
  by_cases H : (i : ℤ) + (k : ℤ) < n
  · rw [← h3 H]
    exact zpow_add ((QuotientGroup.mk (s := Subgroup.normalClosure (Rels n))
      (FreeGroup.of (@Generator.a n))) * (QuotientGroup.mk (FreeGroup.of Generator.b)))
      (i : ℤ) (k : ℤ)
  · push_neg at H
    rw [← h2 H]
    have h5 : (i : ℤ) + (k : ℤ) = (i : ℤ) + (k : ℤ) - (n : ℤ) + (n : ℤ) := by linarith
    have h6 := zpow_add ((QuotientGroup.mk (s := Subgroup.normalClosure (Rels n))
      (FreeGroup.of (@Generator.a n))) * (QuotientGroup.mk (FreeGroup.of Generator.b)))
      (i : ℤ) (k : ℤ)
    have h7 := @a_b_zpow_mem_normalClosure_eq_identity n
    rw [h5] at h6
    rw [← h6]
    have h8 := zpow_add ((QuotientGroup.mk (s := Subgroup.normalClosure (Rels n))
      (FreeGroup.of (@Generator.a n))) * (QuotientGroup.mk (FreeGroup.of Generator.b)))
      (i + k - n : ℤ) (n : ℤ)
    simp only [QuotientGroup.mk_mul] at h7
    rw [h8, h7, mul_one]

def GenMapInv : DihedralGroup n → PresentedDihedralGroup n
  | r i => QuotientGroup.mk ((FreeGroup.of Generator.a * FreeGroup.of Generator.b) ^ (i : ℤ))
  | sr i => QuotientGroup.mk ((FreeGroup.of Generator.a) *
    (FreeGroup.of Generator.a * FreeGroup.of Generator.b) ^ (i - 1 : ℤ))

lemma map_mul' : ∀ a b : DihedralGroup n, GenMapInv (a * b) = GenMapInv a * GenMapInv b := by
  intro d₁ d₂
  simp only [GenMapInv]
  rcases d₁ with i | j
  · rcases d₂ with k | l
    · simp only [r_mul_r]
      exact powLaw1
    · simp only [r_mul_sr]
      sorry
      -- think I can figure the other sorry's as they will be similar to a certain extent
  · rcases d₂ with k | l
    · simp only [sr_mul_r]
      sorry
    · simp only [sr_mul_sr]
      sorry

/-- Homorphism from DihedralGroup n to group presentation of DihedralGroup n. -/
def dihedralGroupHom : DihedralGroup n →* PresentedDihedralGroup n where
  toFun := GenMapInv
  map_one' := by
    simp only [GenMapInv, one_def, QuotientGroup.mk_zpow, QuotientGroup.mk_mul,
      ZMod.cast_zero, zpow_zero]
  map_mul' := by
    intro x y
    simp only [GenMapInv]
    exact map_mul' x y

lemma dihedralGroupHom1 {i : ZMod n} : dihedralGroupHom (r i : DihedralGroup n) =
    ((PresentedGroup.of Generator.a) * (PresentedGroup.of Generator.b)) ^ (i : ℤ) := by
  unfold dihedralGroupHom
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, GenMapInv, PresentedGroup.of,
    QuotientGroup.mk_zpow, QuotientGroup.mk_mul]

lemma dihedralGroupHom2 {i : ZMod n} : dihedralGroupHom (sr i : DihedralGroup n) =
    (PresentedGroup.of Generator.a) *
    ((PresentedGroup.of Generator.a) * (PresentedGroup.of Generator.b)) ^ (i - 1 : ℤ) := by
  unfold dihedralGroupHom
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, GenMapInv, PresentedGroup.of,
    QuotientGroup.mk_zpow, QuotientGroup.mk_mul]

theorem rightInverseHoms : Function.RightInverse (@dihedralGroupHom n) (@presentedGroupHom n) := by
  intro dn
  rcases dn with i | i
  · rw [dihedralGroupHom1]
    have h1 := @a_b_relsGenMapOf_pow n i
    simp only [map_zpow, map_mul]
    simp only [map_mul, ZMod.int_cast_cast, ZMod.cast_id', id_eq] at h1
    assumption
  · rw [dihedralGroupHom2]
    have h1 := @a_a_b_relsGenMapOf_pow n i
    simp only [map_mul, map_zpow]
    simp only [map_mul, map_zpow, ZMod.int_cast_cast, ZMod.cast_id', id_eq] at h1
    assumption

theorem leftInverseHoms : Function.LeftInverse (@dihedralGroupHom n) (@presentedGroupHom n) := by
  intro pd
  unfold dihedralGroupHom
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  simp [GenMapInv]
  match presentedGroupHom pd with
  | r i => sorry
  | sr i => sorry

noncomputable
def DihedralGroupIsoPresentedDihedralGroup : PresentedDihedralGroup n ≃* DihedralGroup n where
  toFun := presentedGroupHom
  invFun := dihedralGroupHom
  left_inv := leftInverseHoms
  right_inv := rightInverseHoms
  map_mul' x y := by simp only [map_mul]
