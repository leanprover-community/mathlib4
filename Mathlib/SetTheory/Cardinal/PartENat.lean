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
noncomputable def toPartENat : Cardinal →+o PartENat :=
  .comp
    { (PartENat.withTopAddEquiv.symm : ℕ∞ →+ PartENat),
      (PartENat.withTopOrderIso.symm : ℕ∞ →o PartENat) with }
    toENat
#align cardinal.to_part_enat Cardinal.toPartENat

@[simp]
theorem partENatOfENat_toENat (c : Cardinal) : (toENat c : PartENat) = toPartENat c := rfl

@[simp]
theorem toPartENat_natCast (n : ℕ) : toPartENat n = n := by
  simp only [← partENatOfENat_toENat, toENat_nat, PartENat.ofENat_coe]
#align cardinal.to_part_enat_cast Cardinal.toPartENat_natCast

theorem toPartENat_apply_of_lt_aleph0 {c : Cardinal} (h : c < ℵ₀) : toPartENat c = toNat c := by
  lift c to ℕ using h; simp
#align cardinal.to_part_enat_apply_of_lt_aleph_0 Cardinal.toPartENat_apply_of_lt_aleph0

theorem toPartENat_eq_top {c : Cardinal} :
    toPartENat c = ⊤ ↔ ℵ₀ ≤ c := by
  rw [← partENatOfENat_toENat, ← PartENat.withTopEquiv_symm_top, ← toENat_eq_top,
    ← PartENat.withTopEquiv.symm.injective.eq_iff]
  simp
#align to_part_enat_eq_top_iff_le_aleph_0 Cardinal.toPartENat_eq_top

theorem toPartENat_apply_of_aleph0_le {c : Cardinal} (h : ℵ₀ ≤ c) : toPartENat c = ⊤ :=
  congr_arg PartENat.ofENat (toENat_eq_top.2 h)
#align cardinal.to_part_enat_apply_of_aleph_0_le Cardinal.toPartENat_apply_of_aleph0_le

@[deprecated (since := "2024-02-15")]
alias toPartENat_cast := toPartENat_natCast

@[simp]
theorem mk_toPartENat_of_infinite [h : Infinite α] : toPartENat #α = ⊤ :=
  toPartENat_apply_of_aleph0_le (infinite_iff.1 h)
#align cardinal.mk_to_part_enat_of_infinite Cardinal.mk_toPartENat_of_infinite

@[simp]
theorem aleph0_toPartENat : toPartENat ℵ₀ = ⊤ :=
  toPartENat_apply_of_aleph0_le le_rfl
#align cardinal.aleph_0_to_part_enat Cardinal.aleph0_toPartENat

theorem toPartENat_surjective : Surjective toPartENat := fun x =>
  PartENat.casesOn x ⟨ℵ₀, toPartENat_apply_of_aleph0_le le_rfl⟩ fun n => ⟨n, toPartENat_natCast n⟩
#align cardinal.to_part_enat_surjective Cardinal.toPartENat_surjective

@[deprecated (since := "2024-02-15")] alias toPartENat_eq_top_iff_le_aleph0 := toPartENat_eq_top

theorem toPartENat_strictMonoOn : StrictMonoOn toPartENat (Set.Iic ℵ₀) :=
  PartENat.withTopOrderIso.symm.strictMono.comp_strictMonoOn toENat_strictMonoOn

lemma toPartENat_le_iff_of_le_aleph0 {c c' : Cardinal} (h : c ≤ ℵ₀) :
    toPartENat c ≤ toPartENat c' ↔ c ≤ c' := by
  lift c to ℕ∞ using h
  simp_rw [← partENatOfENat_toENat, toENat_ofENat, enat_gc _,
   ← PartENat.withTopOrderIso.symm.le_iff_le, PartENat.ofENat_le, map_le_map_iff]
#align to_part_enat_le_iff_le_of_le_aleph_0 Cardinal.toPartENat_le_iff_of_le_aleph0

lemma toPartENat_le_iff_of_lt_aleph0 {c c' : Cardinal} (hc' : c' < ℵ₀) :
    toPartENat c ≤ toPartENat c' ↔ c ≤ c' := by
  lift c' to ℕ using hc'
  simp_rw [← partENatOfENat_toENat, toENat_nat, ← toENat_le_nat,
   ← PartENat.withTopOrderIso.symm.le_iff_le, PartENat.ofENat_le, map_le_map_iff]
#align to_part_enat_le_iff_le_of_lt_aleph_0 Cardinal.toPartENat_le_iff_of_lt_aleph0

lemma toPartENat_eq_iff_of_le_aleph0 {c c' : Cardinal} (hc : c ≤ ℵ₀) (hc' : c' ≤ ℵ₀) :
    toPartENat c = toPartENat c' ↔ c = c' :=
  toPartENat_strictMonoOn.injOn.eq_iff hc hc'
#align to_part_enat_eq_iff_eq_of_le_aleph_0 Cardinal.toPartENat_eq_iff_of_le_aleph0

theorem toPartENat_mono {c c' : Cardinal} (h : c ≤ c') :
    toPartENat c ≤ toPartENat c' :=
  OrderHomClass.mono _ h
#align cardinal.to_part_enat_mono Cardinal.toPartENat_mono

theorem toPartENat_lift (c : Cardinal.{v}) : toPartENat (lift.{u, v} c) = toPartENat c := by
  simp only [← partENatOfENat_toENat, toENat_lift]
#align cardinal.to_part_enat_lift Cardinal.toPartENat_lift

theorem toPartENat_congr {β : Type v} (e : α ≃ β) : toPartENat #α = toPartENat #β := by
  rw [← toPartENat_lift, lift_mk_eq.{_, _,v}.mpr ⟨e⟩, toPartENat_lift]
#align cardinal.to_part_enat_congr Cardinal.toPartENat_congr

theorem mk_toPartENat_eq_coe_card [Fintype α] : toPartENat #α = Fintype.card α := by
  simp
#align cardinal.mk_to_part_enat_eq_coe_card Cardinal.mk_toPartENat_eq_coe_card

end Cardinal
