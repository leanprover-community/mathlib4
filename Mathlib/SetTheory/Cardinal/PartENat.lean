/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.SetTheory.Cardinal.ToNat
import Mathlib.Data.Nat.PartENat

#align_import set_theory.cardinal.basic from "leanprover-community/mathlib"@"3ff3f2d6a3118b8711063de7111a0d77a53219a8"

/-!
# Projection from cardinal numbers to `PartENat`

In this file we define the projection `Cardinal.toPartENat`
and prove basic properties of this projection.
-/

universe u v

open Function

variable {α : Type u}

namespace Cardinal

/-- This function sends finite cardinals to the corresponding natural, and infinite cardinals
  to `⊤`. -/
noncomputable def toPartENat : Cardinal →+ PartENat where
  toFun c := if c < ℵ₀ then toNat c else ⊤
  map_zero' := by simp [if_pos (zero_lt_one.trans one_lt_aleph0)]
  map_add' x y := by
    by_cases hx : x < ℵ₀
    · obtain ⟨x0, rfl⟩ := lt_aleph0.1 hx
      by_cases hy : y < ℵ₀
      · obtain ⟨y0, rfl⟩ := lt_aleph0.1 hy
        simp only [add_lt_aleph0 hx hy, hx, hy, toNat_cast, if_true]
        rw [← Nat.cast_add, toNat_cast, Nat.cast_add]
      · simp_rw [if_neg hy, PartENat.add_top]
        contrapose! hy
        simp only [ne_eq, ite_eq_right_iff, PartENat.natCast_ne_top, not_forall, exists_prop,
          and_true, not_false_eq_true] at hy
        exact le_add_self.trans_lt hy
    · simp_rw [if_neg hx, PartENat.top_add]
      contrapose! hx
      simp only [ne_eq, ite_eq_right_iff, PartENat.natCast_ne_top, not_forall, exists_prop,
        and_true, not_false_eq_true] at hx
      exact le_self_add.trans_lt hx
#align cardinal.to_part_enat Cardinal.toPartENat

theorem toPartENat_apply_of_lt_aleph0 {c : Cardinal} (h : c < ℵ₀) : toPartENat c = toNat c :=
  if_pos h
#align cardinal.to_part_enat_apply_of_lt_aleph_0 Cardinal.toPartENat_apply_of_lt_aleph0

theorem toPartENat_apply_of_aleph0_le {c : Cardinal} (h : ℵ₀ ≤ c) : toPartENat c = ⊤ :=
  if_neg h.not_lt
#align cardinal.to_part_enat_apply_of_aleph_0_le Cardinal.toPartENat_apply_of_aleph0_le

@[simp]
theorem toPartENat_cast (n : ℕ) : toPartENat n = n := by
  rw [toPartENat_apply_of_lt_aleph0 (nat_lt_aleph0 n), toNat_cast]
#align cardinal.to_part_enat_cast Cardinal.toPartENat_cast

@[simp]
theorem mk_toPartENat_of_infinite [h : Infinite α] : toPartENat #α = ⊤ :=
  toPartENat_apply_of_aleph0_le (infinite_iff.1 h)
#align cardinal.mk_to_part_enat_of_infinite Cardinal.mk_toPartENat_of_infinite

@[simp]
theorem aleph0_toPartENat : toPartENat ℵ₀ = ⊤ :=
  toPartENat_apply_of_aleph0_le le_rfl
#align cardinal.aleph_0_to_part_enat Cardinal.aleph0_toPartENat

theorem toPartENat_surjective : Surjective toPartENat := fun x =>
  PartENat.casesOn x ⟨ℵ₀, toPartENat_apply_of_aleph0_le le_rfl⟩ fun n => ⟨n, toPartENat_cast n⟩
#align cardinal.to_part_enat_surjective Cardinal.toPartENat_surjective

theorem toPartENat_eq_top_iff_le_aleph0 {c : Cardinal} :
    toPartENat c = ⊤ ↔ ℵ₀ ≤ c := by
  cases lt_or_ge c ℵ₀ with
  | inl hc =>
    simp only [toPartENat_apply_of_lt_aleph0 hc, PartENat.natCast_ne_top, false_iff, not_le, hc]
  | inr hc => simp only [toPartENat_apply_of_aleph0_le hc, eq_self_iff_true, true_iff]; exact hc
#align to_part_enat_eq_top_iff_le_aleph_0 Cardinal.toPartENat_eq_top_iff_le_aleph0

lemma toPartENat_le_iff_of_le_aleph0 {c c' : Cardinal} (h : c ≤ ℵ₀) :
    toPartENat c ≤ toPartENat c' ↔ c ≤ c' := by
  cases lt_or_ge c ℵ₀ with
  | inl hc =>
    rw [toPartENat_apply_of_lt_aleph0 hc]
    cases lt_or_ge c' ℵ₀ with
    | inl hc' =>
      rw [toPartENat_apply_of_lt_aleph0 hc', PartENat.coe_le_coe]
      exact toNat_le_iff_le_of_lt_aleph0 hc hc'
    | inr hc' =>
      simp only [toPartENat_apply_of_aleph0_le hc',
      le_top, true_iff]
      exact le_trans h hc'
  | inr hc =>
    rw [toPartENat_apply_of_aleph0_le hc]
    simp only [top_le_iff, toPartENat_eq_top_iff_le_aleph0,
    le_antisymm h hc]
#align to_part_enat_le_iff_le_of_le_aleph_0 Cardinal.toPartENat_le_iff_of_le_aleph0

lemma toPartENat_le_iff_of_lt_aleph0 {c c' : Cardinal} (hc' : c' < ℵ₀) :
    toPartENat c ≤ toPartENat c' ↔ c ≤ c' := by
  cases lt_or_ge c ℵ₀ with
  | inl hc =>
    rw [toPartENat_apply_of_lt_aleph0 hc]
    rw [toPartENat_apply_of_lt_aleph0 hc', PartENat.coe_le_coe]
    exact toNat_le_iff_le_of_lt_aleph0 hc hc'
  | inr hc =>
    rw [toPartENat_apply_of_aleph0_le hc]
    simp only [top_le_iff, toPartENat_eq_top_iff_le_aleph0]
    rw [← not_iff_not, not_le, not_le]
    simp only [hc', lt_of_lt_of_le hc' hc]
#align to_part_enat_le_iff_le_of_lt_aleph_0 Cardinal.toPartENat_le_iff_of_lt_aleph0

lemma toPartENat_eq_iff_of_le_aleph0 {c c' : Cardinal} (hc : c ≤ ℵ₀) (hc' : c' ≤ ℵ₀) :
    toPartENat c = toPartENat c' ↔ c = c' := by
  rw [le_antisymm_iff, le_antisymm_iff, toPartENat_le_iff_of_le_aleph0 hc,
    toPartENat_le_iff_of_le_aleph0 hc']
#align to_part_enat_eq_iff_eq_of_le_aleph_0 Cardinal.toPartENat_eq_iff_of_le_aleph0

theorem toPartENat_mono {c c' : Cardinal} (h : c ≤ c') :
    toPartENat c ≤ toPartENat c' := by
  cases lt_or_ge c ℵ₀ with
  | inl hc =>
    rw [toPartENat_apply_of_lt_aleph0 hc]
    cases lt_or_ge c' ℵ₀ with
    | inl hc' =>
      rw [toPartENat_apply_of_lt_aleph0 hc', PartENat.coe_le_coe]
      exact toNat_le_of_le_of_lt_aleph0 hc' h
    | inr hc' =>
        rw [toPartENat_apply_of_aleph0_le hc']
        exact le_top
  | inr hc =>
      rw [toPartENat_apply_of_aleph0_le hc,
      toPartENat_apply_of_aleph0_le (le_trans hc h)]
#align cardinal.to_part_enat_mono Cardinal.toPartENat_mono

theorem toPartENat_lift (c : Cardinal.{v}) : toPartENat (lift.{u, v} c) = toPartENat c := by
  cases' lt_or_ge c ℵ₀ with hc hc
  · rw [toPartENat_apply_of_lt_aleph0 hc, Cardinal.toPartENat_apply_of_lt_aleph0 _]
    simp only [toNat_lift]
    rw [lift_lt_aleph0]
    exact hc
  · rw [toPartENat_apply_of_aleph0_le hc, toPartENat_apply_of_aleph0_le _]
    rw [aleph0_le_lift]
    exact hc
#align cardinal.to_part_enat_lift Cardinal.toPartENat_lift

theorem toPartENat_congr {β : Type v} (e : α ≃ β) : toPartENat #α = toPartENat #β := by
  rw [← toPartENat_lift, lift_mk_eq.{_, _,v}.mpr ⟨e⟩, toPartENat_lift]
#align cardinal.to_part_enat_congr Cardinal.toPartENat_congr

theorem mk_toPartENat_eq_coe_card [Fintype α] : toPartENat #α = Fintype.card α := by
  simp
#align cardinal.mk_to_part_enat_eq_coe_card Cardinal.mk_toPartENat_eq_coe_card

end Cardinal
