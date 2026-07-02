/-
Copyright (c) 2021 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.Coset.Basic

/-!
# Double cosets

This file defines double cosets for two subgroups `H K` of a group `G` and the quotient of `G` by
the double coset relation, i.e. `H \ G / K`. We also prove that `G` can be written as a disjoint
union of the double cosets and that if one of `H` or `K` is the trivial group (i.e. `⊥` ) then
this is the usual left or right quotient of a group by a subgroup.

## Main definitions

* `setoid`: The double coset relation defined by two subgroups `H K` of `G`.
* `DoubleCoset.quotient`: The quotient of `G` by the double coset relation, i.e, `H \ G / K`.
-/

@[expose] public section

assert_not_exists MonoidWithZero

variable {G : Type*} [Group G] {α : Type*} [Mul α]

open MulOpposite
open scoped Pointwise

namespace DoubleCoset

/-- The double coset as an element of `Set α` corresponding to `s a t` -/
def doubleCoset (a : α) (s t : Set α) : Set α :=
  s * {a} * t

lemma doubleCoset_eq_image2 (a : α) (s t : Set α) :
    doubleCoset a s t = Set.image2 (· * a * ·) s t := by
  simp_rw [doubleCoset, Set.mul_singleton, ← Set.image2_mul, Set.image2_image_left]

lemma mem_doubleCoset {s t : Set α} {a b : α} :
    b ∈ doubleCoset a s t ↔ ∃ x ∈ s, ∃ y ∈ t, b = x * a * y := by
  simp only [doubleCoset_eq_image2, Set.mem_image2, eq_comm]

lemma mem_doubleCoset_self (H K : Subgroup G) (a : G) : a ∈ doubleCoset a H K :=
  mem_doubleCoset.mpr ⟨1, H.one_mem, 1, K.one_mem, (one_mul a).symm.trans (mul_one (1 * a)).symm⟩

lemma doubleCoset_eq_of_mem {H K : Subgroup G} {a b : G} (hb : b ∈ doubleCoset a H K) :
    doubleCoset b H K = doubleCoset a H K := by
  obtain ⟨h, hh, k, hk, rfl⟩ := mem_doubleCoset.1 hb
  rw [doubleCoset, doubleCoset, ← Set.singleton_mul_singleton, ← Set.singleton_mul_singleton,
    mul_assoc, mul_assoc, Subgroup.singleton_mul_subgroup hk, ← mul_assoc, ← mul_assoc,
    Subgroup.subgroup_mul_singleton hh]

lemma doubleCoset_mul_left {H : Subgroup G} (K : Subgroup G) {h : G} (hh : h ∈ H) (a : G) :
    doubleCoset (h * a) H K = doubleCoset a H K :=
  doubleCoset_eq_of_mem (mem_doubleCoset.mpr ⟨h, hh, 1, K.one_mem, (mul_one _).symm⟩)

lemma doubleCoset_mul_right (H : Subgroup G) {K : Subgroup G} {k : G} (hk : k ∈ K) (a : G) :
    doubleCoset (a * k) H K = doubleCoset a H K :=
  doubleCoset_eq_of_mem (mem_doubleCoset.mpr ⟨1, H.one_mem, k, hk, by rw [one_mul]⟩)

lemma mem_doubleCoset_of_not_disjoint {H K : Subgroup G} {a b : G}
    (h : ¬Disjoint (doubleCoset a H K) (doubleCoset b H K)) : b ∈ doubleCoset a H K := by
  rw [Set.not_disjoint_iff] at h
  simp only [mem_doubleCoset] at *
  obtain ⟨x, ⟨l, hl, r, hr, hrx⟩, y, hy, ⟨r', hr', rfl⟩⟩ := h
  refine ⟨y⁻¹ * l, H.mul_mem (H.inv_mem hy) hl, r * r'⁻¹, K.mul_mem hr (K.inv_mem hr'), ?_⟩
  rwa [mul_assoc, mul_assoc, eq_inv_mul_iff_mul_eq, ← mul_assoc, ← mul_assoc, eq_mul_inv_iff_mul_eq]

lemma eq_of_not_disjoint {H K : Subgroup G} {a b : G}
    (h : ¬Disjoint (doubleCoset a H K) (doubleCoset b H K)) :
    doubleCoset a H K = doubleCoset b H K := by
  rw [disjoint_comm] at h
  have ha : a ∈ doubleCoset b H K := mem_doubleCoset_of_not_disjoint h
  apply doubleCoset_eq_of_mem ha

/-- The setoid defined by the `doubleCoset` relation -/
@[implicit_reducible]
def setoid (H K : Set G) : Setoid G :=
  Setoid.ker fun x => doubleCoset x H K

/-- Quotient of `G` by the double coset relation, i.e. `H \ G / K` -/
def Quotient (H K : Set G) : Type _ :=
  _root_.Quotient (setoid H K)

lemma rel_iff {H K : Subgroup G} {x y : G} :
    setoid ↑H ↑K x y ↔ ∃ a ∈ H, ∃ b ∈ K, y = a * x * b :=
  Iff.trans
    ⟨fun (hxy : doubleCoset x H K = doubleCoset y H K) => hxy ▸ mem_doubleCoset_self H K y,
      fun hxy => (doubleCoset_eq_of_mem hxy).symm⟩ mem_doubleCoset

lemma bot_rel_eq_leftRel (H : Subgroup G) :
    ⇑(setoid ↑(⊥ : Subgroup G) ↑H) = ⇑(QuotientGroup.leftRel H) := by
  ext a b
  rw [rel_iff, QuotientGroup.leftRel_apply]
  constructor
  · rintro ⟨a, rfl : a = 1, b, hb, rfl⟩
    rwa [one_mul, inv_mul_cancel_left]
  · rintro (h : a⁻¹ * b ∈ H)
    exact ⟨1, rfl, a⁻¹ * b, h, by rw [one_mul, mul_inv_cancel_left]⟩

lemma rel_bot_eq_right_group_rel (H : Subgroup G) :
    ⇑(setoid ↑H ↑(⊥ : Subgroup G)) = ⇑(QuotientGroup.rightRel H) := by
  ext a b
  rw [rel_iff, QuotientGroup.rightRel_apply]
  constructor
  · rintro ⟨b, hb, a, rfl : a = 1, rfl⟩
    rwa [mul_one, mul_inv_cancel_right]
  · rintro (h : b * a⁻¹ ∈ H)
    exact ⟨b * a⁻¹, h, 1, rfl, by rw [mul_one, inv_mul_cancel_right]⟩

/-- Create a double coset out of an element of `H \ G / K` -/
def quotToDoubleCoset (H K : Subgroup G) (q : Quotient (H : Set G) K) : Set G :=
  doubleCoset q.out H K

/-- Map from `G` to `H \ G / K` -/
abbrev mk (H K : Subgroup G) (a : G) : Quotient (H : Set G) K :=
  Quotient.mk'' a

instance (H K : Subgroup G) : Inhabited (Quotient (H : Set G) K) :=
  ⟨mk H K (1 : G)⟩

lemma eq'' {a b : G} (H K : Subgroup G) : mk H K a = mk H K b ↔ setoid H K a b :=
  Quotient.eq

lemma eq (H K : Subgroup G) (a b : G) :
    mk H K a = mk H K b ↔ ∃ h ∈ H, ∃ k ∈ K, b = h * a * k := by
  rw [eq'']
  exact rel_iff

lemma out_eq' (H K : Subgroup G) (q : Quotient ↑H ↑K) : mk H K q.out = q :=
  Quotient.out_eq' q

lemma mk_out_eq_mul (H K : Subgroup G) (g : G) :
    ∃ h k : G, h ∈ H ∧ k ∈ K ∧ (mk H K g : Quotient ↑H ↑K).out = h * g * k := by
  have := eq H K (mk H K g : Quotient ↑H ↑K).out g
  rw [out_eq'] at this
  obtain ⟨h, h_h, k, hk, T⟩ := this.1 rfl
  refine ⟨h⁻¹, k⁻¹, H.inv_mem h_h, K.inv_mem hk, eq_mul_inv_of_mul_eq (eq_inv_mul_of_mul_eq ?_)⟩
  rw [← mul_assoc, ← T]

lemma mk_eq_of_doubleCoset_eq {H K : Subgroup G} {a b : G}
    (h : doubleCoset a H K = doubleCoset b H K) : mk H K a = mk H K b := by
  rw [eq]
  exact mem_doubleCoset.mp (h.symm ▸ mem_doubleCoset_self H K b)

lemma mem_quotToDoubleCoset_iff {H K : Subgroup G} (i : Quotient (H : Set G) K) (a : G) :
    a ∈ quotToDoubleCoset H K i ↔ mk H K a = i := by
  refine ⟨fun hg ↦ by simp [mk_eq_of_doubleCoset_eq (doubleCoset_eq_of_mem hg)], fun hg ↦ ?_⟩
  rw [← out_eq' _ _ i] at hg
  exact mem_doubleCoset.mpr ((eq _ _ _ a).mp hg.symm)

lemma disjoint_out {H K : Subgroup G} {a b : Quotient H K} :
    a ≠ b → Disjoint (doubleCoset a.out H K) (doubleCoset b.out (H : Set G) K) := by
  contrapose
  intro h
  simpa [out_eq'] using mk_eq_of_doubleCoset_eq (eq_of_not_disjoint h)

lemma iUnion_quotToDoubleCoset (H K : Subgroup G) : ⋃ q, quotToDoubleCoset H K q = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, quotToDoubleCoset, mem_doubleCoset, SetLike.mem_coe, Set.mem_univ,
    iff_true]
  use mk H K x
  obtain ⟨h, k, h3, h4, h5⟩ := mk_out_eq_mul H K x
  refine ⟨h⁻¹, H.inv_mem h3, k⁻¹, K.inv_mem h4, ?_⟩
  simp only [h5, ← mul_assoc, one_mul, inv_mul_cancel, mul_inv_cancel_right]

@[deprecated (since := "2026-04-03")]
alias union_quotToDoubleCoset := iUnion_quotToDoubleCoset

lemma doubleCoset_union_rightCoset (H K : Subgroup G) (a : G) :
    ⋃ k : K, op (a * k) • ↑H = doubleCoset a H K := by
  ext x
  simp only [mem_rightCoset_iff, mul_inv_rev, Set.mem_iUnion, mem_doubleCoset,
    SetLike.mem_coe]
  constructor
  · rintro ⟨y, h_h⟩
    refine ⟨x * (y⁻¹ * a⁻¹), h_h, y, y.2, ?_⟩
    simp only [← mul_assoc, inv_mul_cancel_right, InvMemClass.coe_inv]
  · rintro ⟨x, hx, y, hy, hxy⟩
    refine ⟨⟨y, hy⟩, ?_⟩
    simp only [hxy, ← mul_assoc, hx, mul_inv_cancel_right]

lemma doubleCoset_union_leftCoset (H K : Subgroup G) (a : G) :
    ⋃ h : H, (h * a : G) • ↑K = doubleCoset a H K := by
  ext x
  simp only [mem_leftCoset_iff, mul_inv_rev, Set.mem_iUnion, mem_doubleCoset]
  constructor
  · rintro ⟨y, h_h⟩
    refine ⟨y, y.2, a⁻¹ * y⁻¹ * x, h_h, ?_⟩
    simp only [← mul_assoc, one_mul, mul_inv_cancel, mul_inv_cancel_right, InvMemClass.coe_inv]
  · rintro ⟨x, hx, y, hy, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    simp only [hxy, ← mul_assoc, hy, one_mul, inv_mul_cancel, inv_mul_cancel_right]

open Quotient QuotientGroup

/-- A double coset `HaK` is the union of the left cosets `(h * a) • K` where `h` ranges over
representatives of the quotient of `H` by the stabiliser `H ∩ aKa⁻¹`. -/
lemma doubleCoset_eq_iUnion_leftCosets (H K : Subgroup G) (a : G) :
    doubleCoset a H K =
      ⋃ i : H ⧸ (ConjAct.toConjAct a • K).subgroupOf H, ((i.out : G) * a) • (K : Set G) := by
  ext x
  simp only [Set.mem_iUnion, mem_doubleCoset, mem_leftCoset_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨h, hh, k, hk, rfl⟩
    refine ⟨QuotientGroup.mk ⟨h, hh⟩, ?_⟩
    obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul ((ConjAct.toConjAct a • K).subgroupOf H) ⟨h, hh⟩
    have hn' : a⁻¹ * ((n : H) : G) * a ∈ K :=
      Subgroup.mem_conjAct_pointwise_smul_iff.mp (Subgroup.mem_subgroupOf.mp n.2)
    rw [hn, show (((⟨h, hh⟩ : H) * (n : H) : H) : G) = h * ((n : H) : G) from rfl,
      show (h * ((n : H) : G) * a)⁻¹ * (h * a * k) = (a⁻¹ * ((n : H) : G) * a)⁻¹ * k by
        simp [mul_assoc]]
    exact K.mul_mem (K.inv_mem hn') hk
  · rintro ⟨i, hx⟩
    exact ⟨(i.out : G), i.out.2, ((i.out : G) * a)⁻¹ * x, hx, (mul_inv_cancel_left _ _).symm⟩

lemma left_bot_eq_left_quot (H : Subgroup G) :
    Quotient (⊥ : Subgroup G) (H : Set G) = (G ⧸ H) := by
  unfold Quotient
  congr
  ext
  simp_rw [← bot_rel_eq_leftRel H]

lemma right_bot_eq_right_quot (H : Subgroup G) :
    Quotient (H : Set G) (⊥ : Subgroup G) = _root_.Quotient (rightRel H) := by
  unfold Quotient
  congr
  ext
  simp_rw [← rel_bot_eq_right_group_rel H]

lemma finite_quotient_iff_exists_finset_iUnion_eq_univ (H K : Subgroup G) :
    Finite (Quotient (H : Set G) K) ↔
    ∃ I : Finset (Quotient (H : Set G) K), ⋃ i ∈ I, quotToDoubleCoset H K i = .univ := by
  constructor
  · intro _
    cases nonempty_fintype (Quotient (H : Set G) K)
    exact ⟨Finset.univ, by simpa using! iUnion_quotToDoubleCoset _ _⟩
  · rintro ⟨I, hI⟩
    suffices (I : Set (Quotient (H : Set G) K)) = Set.univ by
      simp_rw [← Set.finite_univ_iff, ← this, I.finite_toSet]
    rw [Set.eq_univ_iff_forall] at hI ⊢
    rintro ⟨g⟩
    obtain ⟨_, ⟨i, _, rfl⟩, T, ⟨hi, rfl⟩, hT : g ∈ quotToDoubleCoset H K i⟩ := hI g
    simpa [← (mem_quotToDoubleCoset_iff _ _).mp hT] using! hi

lemma iUnion_image_mk_leftRel {H K : Subgroup G} :
    ⋃ q : Quotient H K, Quot.mk (leftRel K) '' doubleCoset (out q : G) H K = Set.univ := by
  have cover := iUnion_quotToDoubleCoset H K
  rw [Set.iUnion_eq_univ_iff]
  intro x
  obtain ⟨y, hy⟩ := exists_rep x
  have ⟨i, hi⟩ : ∃ i : Quotient H K, y ∈ doubleCoset (out i) H K := by
    contrapose cover
    exact (Set.ne_univ_iff_exists_notMem _).mpr ⟨y, by simpa using! cover⟩
  exact ⟨i, y, hi, hy⟩

lemma iUnion_image_mk_rightRel {H K : Subgroup G} :
    ⋃ q : Quotient H K, Quot.mk (rightRel H) '' doubleCoset (out q : G) H K = Set.univ := by
  have cover := iUnion_quotToDoubleCoset H K
  rw [Set.iUnion_eq_univ_iff]
  intro x
  obtain ⟨y, hy⟩ := exists_rep x
  have ⟨i, hi⟩ : ∃ i : Quotient H K, y ∈ doubleCoset (out i) H K := by
    contrapose cover
    exact (Set.ne_univ_iff_exists_notMem _).mpr ⟨y, by simpa using! cover⟩
  exact ⟨i, y, hi, hy⟩

lemma iUnion_finset_leftRel_eq_univ_of_leftRel {H K : Subgroup G} {t : Finset (Quotient H K)}
    (ht : Set.univ ⊆ ⋃ i ∈ t, Quot.mk (leftRel K) '' doubleCoset (out i) H K) :
    ⋃ q ∈ t, doubleCoset (out q) H K = Set.univ := by
  contrapose ht
  simp only [Set.univ_subset_iff, ← ne_eq] at ⊢ ht
  obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem _).mp ht
  refine (Set.ne_univ_iff_exists_notMem _).mpr ⟨Quot.mk (leftRel K) x, ?_⟩
  simp only [Set.mem_iUnion, Set.mem_image, exists_prop, not_exists, not_and]
  intro y hy q hq
  contrapose hx
  simp only [Set.mem_iUnion, exists_prop]
  refine ⟨y, hy, ?_⟩
  rw [← doubleCoset_eq_of_mem hq, mem_doubleCoset]
  obtain ⟨a', ha'⟩ := Quotient.eq.mp hx
  exact ⟨1, one_mem H, MulOpposite.unop a'⁻¹, Subgroup.mem_op.mp (by simp), by simpa
    using (eq_mul_inv_of_mul_eq ha')⟩

lemma iUnion_finset_rightRel_eq_univ_of_rightRel {H K : Subgroup G} {t : Finset (Quotient H K)}
    (ht : Set.univ ⊆ ⋃ i ∈ t, Quot.mk (rightRel H) '' doubleCoset (out i) H K) :
    ⋃ q ∈ t, doubleCoset (out q) H K = Set.univ := by
  contrapose ht
  simp only [Set.univ_subset_iff, ← ne_eq] at ⊢ ht
  obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem _).mp ht
  refine (Set.ne_univ_iff_exists_notMem _).mpr ⟨Quot.mk (rightRel H) x, ?_⟩
  simp only [Set.mem_iUnion, Set.mem_image, exists_prop, not_exists, not_and]
  intro y hy q hq
  contrapose hx
  simp only [Set.mem_iUnion, exists_prop]
  refine ⟨y, hy, ?_⟩
  rw [← doubleCoset_eq_of_mem hq, mem_doubleCoset]
  obtain ⟨a, ha⟩ : ∃ a : H, x = a * q := by
    obtain ⟨a, ha⟩ : ∃ a : H, a * x = q := Quotient.eq.mp hx
    exact ⟨⟨a⁻¹, by simp⟩, eq_inv_mul_of_mul_eq ha⟩
  exact ⟨a.1, a.2, ⟨1, Subgroup.one_mem K, by simpa using ha⟩⟩

end DoubleCoset
