/-
Copyright (c) 2021 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.Coset.Basic

/-!
# Double cosets

This file defines double cosets for two subgroups `H K` of a group `G` and the quotient of `G` by
the double coset relation, i.e. `H \ G / K`. We also prove that `G` can be written as a disjoint
union of the double cosets and that if one of `H` or `K` is the trivial group (i.e. `⊥` ) then
this is the usual left or right quotient of a group by a subgroup.

## Main definitions

* `rel`: The double coset relation defined by two subgroups `H K` of `G`.
* `Doset.quotient`: The quotient of `G` by the double coset relation, i.e, `H \ G / K`.
-/

assert_not_exists MonoidWithZero

variable {G : Type*} [Group G] {α : Type*} [Mul α]

open MulOpposite
open scoped Pointwise

namespace Doset

/-- The double coset as an element of `Set α` corresponding to `s a t` -/
def doset (a : α) (s t : Set α) : Set α :=
  s * {a} * t

lemma doset_eq_image2 (a : α) (s t : Set α) : doset a s t = Set.image2 (· * a * ·) s t := by
  simp_rw [doset, Set.mul_singleton, ← Set.image2_mul, Set.image2_image_left]

theorem mem_doset {s t : Set α} {a b : α} : b ∈ doset a s t ↔ ∃ x ∈ s, ∃ y ∈ t, b = x * a * y := by
  simp only [doset_eq_image2, Set.mem_image2, eq_comm]

theorem mem_doset_self (H K : Subgroup G) (a : G) : a ∈ doset a H K :=
  mem_doset.mpr ⟨1, H.one_mem, 1, K.one_mem, (one_mul a).symm.trans (mul_one (1 * a)).symm⟩

theorem doset_eq_of_mem {H K : Subgroup G} {a b : G} (hb : b ∈ doset a H K) :
    doset b H K = doset a H K := by
  obtain ⟨h, hh, k, hk, rfl⟩ := mem_doset.1 hb
  rw [doset, doset, ← Set.singleton_mul_singleton, ← Set.singleton_mul_singleton, mul_assoc,
    mul_assoc, Subgroup.singleton_mul_subgroup hk, ← mul_assoc, ← mul_assoc,
    Subgroup.subgroup_mul_singleton hh]

theorem mem_doset_of_not_disjoint {H K : Subgroup G} {a b : G}
    (h : ¬Disjoint (doset a H K) (doset b H K)) : b ∈ doset a H K := by
  rw [Set.not_disjoint_iff] at h
  simp only [mem_doset] at *
  obtain ⟨x, ⟨l, hl, r, hr, hrx⟩, y, hy, ⟨r', hr', rfl⟩⟩ := h
  refine ⟨y⁻¹ * l, H.mul_mem (H.inv_mem hy) hl, r * r'⁻¹, K.mul_mem hr (K.inv_mem hr'), ?_⟩
  rwa [mul_assoc, mul_assoc, eq_inv_mul_iff_mul_eq, ← mul_assoc, ← mul_assoc, eq_mul_inv_iff_mul_eq]

theorem eq_of_not_disjoint {H K : Subgroup G} {a b : G}
    (h : ¬Disjoint (doset a H K) (doset b H K)) : doset a H K = doset b H K := by
  rw [disjoint_comm] at h
  have ha : a ∈ doset b H K := mem_doset_of_not_disjoint h
  apply doset_eq_of_mem ha

/-- The setoid defined by the double_coset relation -/
def setoid (H K : Set G) : Setoid G :=
  Setoid.ker fun x => doset x H K

/-- Quotient of `G` by the double coset relation, i.e. `H \ G / K` -/
def Quotient (H K : Set G) : Type _ :=
  _root_.Quotient (setoid H K)

theorem rel_iff {H K : Subgroup G} {x y : G} :
    setoid ↑H ↑K x y ↔ ∃ a ∈ H, ∃ b ∈ K, y = a * x * b :=
  Iff.trans
    ⟨fun (hxy : doset x H K = doset y H K) => hxy ▸ mem_doset_self H K y,
      fun hxy => (doset_eq_of_mem hxy).symm⟩ mem_doset

theorem bot_rel_eq_leftRel (H : Subgroup G) :
    ⇑(setoid ↑(⊥ : Subgroup G) ↑H) = ⇑(QuotientGroup.leftRel H) := by
  ext a b
  rw [rel_iff, QuotientGroup.leftRel_apply]
  constructor
  · rintro ⟨a, rfl : a = 1, b, hb, rfl⟩
    rwa [one_mul, inv_mul_cancel_left]
  · rintro (h : a⁻¹ * b ∈ H)
    exact ⟨1, rfl, a⁻¹ * b, h, by rw [one_mul, mul_inv_cancel_left]⟩

theorem rel_bot_eq_right_group_rel (H : Subgroup G) :
    ⇑(setoid ↑H ↑(⊥ : Subgroup G)) = ⇑(QuotientGroup.rightRel H) := by
  ext a b
  rw [rel_iff, QuotientGroup.rightRel_apply]
  constructor
  · rintro ⟨b, hb, a, rfl : a = 1, rfl⟩
    rwa [mul_one, mul_inv_cancel_right]
  · rintro (h : b * a⁻¹ ∈ H)
    exact ⟨b * a⁻¹, h, 1, rfl, by rw [mul_one, inv_mul_cancel_right]⟩

/-- Create a doset out of an element of `H \ G / K` -/
def quotToDoset (H K : Subgroup G) (q : Quotient (H : Set G) K) : Set G :=
  doset q.out H K

/-- Map from `G` to `H \ G / K` -/
abbrev mk (H K : Subgroup G) (a : G) : Quotient (H : Set G) K :=
  Quotient.mk'' a

instance (H K : Subgroup G) : Inhabited (Quotient (H : Set G) K) :=
  ⟨mk H K (1 : G)⟩

theorem eq (H K : Subgroup G) (a b : G) :
    mk H K a = mk H K b ↔ ∃ h ∈ H, ∃ k ∈ K, b = h * a * k := by
  rw [Quotient.eq'']
  apply rel_iff

theorem out_eq' (H K : Subgroup G) (q : Quotient ↑H ↑K) : mk H K q.out = q :=
  Quotient.out_eq' q

theorem mk_out_eq_mul (H K : Subgroup G) (g : G) :
    ∃ h k : G, h ∈ H ∧ k ∈ K ∧ (mk H K g : Quotient ↑H ↑K).out = h * g * k := by
  have := eq H K (mk H K g : Quotient ↑H ↑K).out g
  rw [out_eq'] at this
  obtain ⟨h, h_h, k, hk, T⟩ := this.1 rfl
  refine ⟨h⁻¹, k⁻¹, H.inv_mem h_h, K.inv_mem hk, eq_mul_inv_of_mul_eq (eq_inv_mul_of_mul_eq ?_)⟩
  rw [← mul_assoc, ← T]

theorem mk_eq_of_doset_eq {H K : Subgroup G} {a b : G} (h : doset a H K = doset b H K) :
    mk H K a = mk H K b := by
  rw [eq]
  exact mem_doset.mp (h.symm ▸ mem_doset_self H K b)

theorem mem_quotToDoset_iff (H K : Subgroup G) (i : Quotient (H : Set G) K) (a : G) :
    a ∈ quotToDoset H K i ↔ mk H K a = i := by
   constructor
   · intro hg
     simp_rw [mk_eq_of_doset_eq (doset_eq_of_mem hg), Quotient.out_eq]
   · intro hg
     rw [← out_eq' _ _ i] at hg
     exact mem_doset.mpr ((eq _ _ _ a).mp hg.symm)

theorem disjoint_out {H K : Subgroup G} {a b : Quotient H K} :
    a ≠ b → Disjoint (doset a.out H K) (doset b.out (H : Set G) K) := by
  contrapose!
  intro h
  simpa [out_eq'] using mk_eq_of_doset_eq (eq_of_not_disjoint h)

theorem union_quotToDoset (H K : Subgroup G) : ⋃ q, quotToDoset H K q = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, quotToDoset, mem_doset, SetLike.mem_coe, Set.mem_univ,
    iff_true]
  use mk H K x
  obtain ⟨h, k, h3, h4, h5⟩ := mk_out_eq_mul H K x
  refine ⟨h⁻¹, H.inv_mem h3, k⁻¹, K.inv_mem h4, ?_⟩
  simp only [h5, ← mul_assoc, one_mul, inv_mul_cancel, mul_inv_cancel_right]

theorem doset_union_rightCoset (H K : Subgroup G) (a : G) :
    ⋃ k : K, op (a * k) • ↑H = doset a H K := by
  ext x
  simp only [mem_rightCoset_iff, mul_inv_rev, Set.mem_iUnion, mem_doset,
    SetLike.mem_coe]
  constructor
  · rintro ⟨y, h_h⟩
    refine ⟨x * (y⁻¹ * a⁻¹), h_h, y, y.2, ?_⟩
    simp only [← mul_assoc, inv_mul_cancel_right, InvMemClass.coe_inv]
  · rintro ⟨x, hx, y, hy, hxy⟩
    refine ⟨⟨y, hy⟩, ?_⟩
    simp only [hxy, ← mul_assoc, hx, mul_inv_cancel_right]

theorem doset_union_leftCoset (H K : Subgroup G) (a : G) :
    ⋃ h : H, (h * a : G) • ↑K = doset a H K := by
  ext x
  simp only [mem_leftCoset_iff, mul_inv_rev, Set.mem_iUnion, mem_doset]
  constructor
  · rintro ⟨y, h_h⟩
    refine ⟨y, y.2, a⁻¹ * y⁻¹ * x, h_h, ?_⟩
    simp only [← mul_assoc, one_mul, mul_inv_cancel, mul_inv_cancel_right, InvMemClass.coe_inv]
  · rintro ⟨x, hx, y, hy, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    simp only [hxy, ← mul_assoc, hy, one_mul, inv_mul_cancel, inv_mul_cancel_right]

theorem left_bot_eq_left_quot (H : Subgroup G) :
    Quotient (⊥ : Subgroup G) (H : Set G) = (G ⧸ H) := by
  unfold Quotient
  congr
  ext
  simp_rw [← bot_rel_eq_leftRel H]

theorem right_bot_eq_right_quot (H : Subgroup G) :
    Quotient (H : Set G) (⊥ : Subgroup G) = _root_.Quotient (QuotientGroup.rightRel H) := by
  unfold Quotient
  congr
  ext
  simp_rw [← rel_bot_eq_right_group_rel H]

theorem iUnion_finset_quotToDoset (H K : Subgroup G) :
    (∃ I : Finset (Quotient (H : Set G) K), ⋃ i ∈ I, quotToDoset H K i = .univ) ↔
    Finite (Quotient (H : Set G) K) := by
  constructor
  · intro ⟨I, hI⟩
    suffices (I : Set (Quotient (H : Set G) K)) = Set.univ by
      rw [← Set.finite_univ_iff, ← this]
      exact I.finite_toSet
    rw [Set.eq_univ_iff_forall] at hI ⊢
    rintro ⟨g⟩
    obtain ⟨_, ⟨i, _, rfl⟩, T, ⟨hi, rfl⟩, hT : g ∈ quotToDoset H K i⟩ := hI g
    rw [Doset.mem_quotToDoset_iff] at hT
    simpa [← hT] using hi
  · intro _
    cases nonempty_fintype (Quotient (H : Set G) K)
    use Finset.univ
    simpa using Doset.union_quotToDoset H K

theorem union_image_mk_leftRel (H K : Subgroup G) :
    ⋃ (q : Doset.Quotient H K), Quot.mk (QuotientGroup.leftRel K) ''
    (Doset.doset (Quotient.out q : G) H K) = Set.univ := by
  have Cover_Dfx := Doset.union_quotToDoset H K
  refine Eq.symm (Set.Subset.antisymm ?_ fun ⦃a⦄ a ↦ trivial)
  intro x hx
  simp only [Set.mem_iUnion, Set.mem_image]
  obtain ⟨y, hy⟩ := Quot.exists_rep x
  have ⟨i, hi⟩ : ∃ i : Doset.Quotient H K, y ∈ Doset.doset (Quotient.out i) H K  := by
    contrapose Cover_Dfx
    refine (Set.ne_univ_iff_exists_notMem (⋃ q, quotToDoset H K q)).mpr ?_
    exact ⟨y, by simpa using Cover_Dfx⟩
  exact ⟨i, y, hi, hy⟩

theorem union_image_mk_rightRel (H K : Subgroup G) :
    ⋃ (q : Doset.Quotient H K), Quot.mk (QuotientGroup.rightRel H) ''
    (Doset.doset (Quotient.out q : G) H K) = Set.univ := by
  have Cover_Dfx := Doset.union_quotToDoset H K
  refine Eq.symm (Set.Subset.antisymm ?_ fun ⦃a⦄ a ↦ trivial)
  intro x hx
  simp only [Set.mem_iUnion, Set.mem_image]
  obtain ⟨y, hy⟩ := Quot.exists_rep x
  have ⟨i, hi⟩ : ∃ i : Doset.Quotient H K, y ∈ Doset.doset (Quotient.out i) H K  := by
    contrapose Cover_Dfx
    refine (Set.ne_univ_iff_exists_notMem (⋃ q, quotToDoset H K q)).mpr ?_
    exact ⟨y, by simpa using Cover_Dfx⟩
  exact ⟨i, y, hi, hy⟩

theorem union_finset_leftRel_cover (H K : Subgroup G)
    (t : Finset (Doset.Quotient H K)) (ht : Set.univ ⊆ ⋃ i ∈ t,
    Quot.mk ⇑(QuotientGroup.leftRel K) '' Doset.doset (Quotient.out i)
    H K) : ⋃ q ∈ t, Doset.doset (Quotient.out q) H K = Set.univ := by
  contrapose ht
  simp only [Set.univ_subset_iff, ← ne_eq] at ⊢ ht
  obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem
    (⋃ q ∈ t, Doset.doset (Quotient.out q) H K)).mp ht
  refine (Set.ne_univ_iff_exists_notMem (⋃ i ∈ t,
    Quot.mk ⇑(QuotientGroup.leftRel K) '' Doset.doset (Quotient.out i)
    H K)).mpr ⟨Quot.mk (⇑(QuotientGroup.leftRel K)) x, ?_⟩
  simp only [Set.mem_iUnion, Set.mem_image, exists_prop, not_exists, not_and]
  intro y hy q hq
  contrapose hx
  simp only [Set.mem_iUnion, exists_prop, not_exists, not_and, not_forall, not_not]
  simp only [not_not] at hx
  refine ⟨y, hy, ?_⟩
  rw [← Doset.doset_eq_of_mem hq]
  apply Doset.mem_doset.mpr
  obtain ⟨a', ha'⟩ := (Quotient.eq).mp hx
  refine ⟨1, one_mem H, (MulOpposite.unop a'⁻¹), Subgroup.mem_op.mp (by simp), by simpa
    using (eq_mul_inv_of_mul_eq ha')⟩

theorem union_finset_rightRel_cover (H K : Subgroup G)
    (t : Finset (Doset.Quotient H K)) (ht : Set.univ ⊆ ⋃ i ∈ t,
    Quot.mk ⇑(QuotientGroup.rightRel H) '' Doset.doset (Quotient.out i)
    H K) : ⋃ q ∈ t, Doset.doset (Quotient.out q) H K = Set.univ := by
  contrapose ht
  simp only [Set.univ_subset_iff, ← ne_eq] at ⊢ ht
  obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem
    (⋃ q ∈ t, Doset.doset (Quotient.out q) H K)).mp ht
  refine (Set.ne_univ_iff_exists_notMem (⋃ i ∈ t,
    Quot.mk ⇑(QuotientGroup.rightRel H) '' Doset.doset (Quotient.out i)
    H K)).mpr ⟨Quot.mk (⇑(QuotientGroup.rightRel H)) x, ?_⟩
  simp only [Set.mem_iUnion, Set.mem_image, exists_prop, not_exists, not_and]
  intro y hy q hq
  contrapose hx
  simp only [Set.mem_iUnion, exists_prop, not_exists, not_and, not_forall, not_not]
  simp only [not_not] at hx
  refine ⟨y, hy, ?_⟩
  rw [← Doset.doset_eq_of_mem hq]
  apply Doset.mem_doset.mpr
  obtain ⟨a, ha⟩ : ∃ a : H, x = a * q := by
    obtain ⟨a, ha⟩  : ∃ a : H, a * x = q := by
      obtain ⟨a', ha'⟩ := (Quotient.eq).mp hx
      exact ⟨a', by simpa using ha'⟩
    exact ⟨⟨ a⁻¹, by simp only [inv_mem_iff, SetLike.coe_mem]⟩, eq_inv_mul_of_mul_eq ha⟩
  refine ⟨a.1, ?_⟩
  simp only [Subtype.coe_prop, SetLike.mem_coe, true_and]
  exact ⟨1, Subgroup.one_mem K, by simpa using ha⟩

end Doset
