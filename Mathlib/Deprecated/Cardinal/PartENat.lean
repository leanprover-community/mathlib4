/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.SetTheory.Cardinal.ToNat
import Mathlib.Data.Nat.PartENat

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

@[simp]
theorem partENatOfENat_toENat (c : Cardinal) : (toENat c : PartENat) = toPartENat c := rfl

@[simp]
theorem toPartENat_natCast (n : ℕ) : toPartENat n = n := by
  simp only [← partENatOfENat_toENat, toENat_nat, PartENat.ofENat_coe]

theorem toPartENat_apply_of_lt_aleph0 {c : Cardinal} (h : c < ℵ₀) : toPartENat c = toNat c := by
  lift c to ℕ using h; simp

theorem toPartENat_eq_top {c : Cardinal} :
    toPartENat c = ⊤ ↔ ℵ₀ ≤ c := by
  rw [← partENatOfENat_toENat, ← PartENat.withTopEquiv_symm_top, ← toENat_eq_top,
    ← PartENat.withTopEquiv.symm.injective.eq_iff]
  simp

theorem toPartENat_apply_of_aleph0_le {c : Cardinal} (h : ℵ₀ ≤ c) : toPartENat c = ⊤ :=
  congr_arg PartENat.ofENat (toENat_eq_top.2 h)

@[simp]
theorem mk_toPartENat_of_infinite [h : Infinite α] : toPartENat #α = ⊤ :=
  toPartENat_apply_of_aleph0_le (infinite_iff.1 h)

@[simp]
theorem aleph0_toPartENat : toPartENat ℵ₀ = ⊤ :=
  toPartENat_apply_of_aleph0_le le_rfl

theorem toPartENat_surjective : Surjective toPartENat := fun x =>
  PartENat.casesOn x ⟨ℵ₀, toPartENat_apply_of_aleph0_le le_rfl⟩ fun n => ⟨n, toPartENat_natCast n⟩


theorem toPartENat_strictMonoOn : StrictMonoOn toPartENat (Set.Iic ℵ₀) :=
  PartENat.withTopOrderIso.symm.strictMono.comp_strictMonoOn toENat_strictMonoOn

lemma toPartENat_le_iff_of_le_aleph0 {c c' : Cardinal} (h : c ≤ ℵ₀) :
    toPartENat c ≤ toPartENat c' ↔ c ≤ c' := by
  lift c to ℕ∞ using h
  simp_rw [← partENatOfENat_toENat, toENat_ofENat, enat_gc _,
   ← PartENat.withTopOrderIso.symm.le_iff_le, PartENat.ofENat_le, map_le_map_iff]

lemma toPartENat_le_iff_of_lt_aleph0 {c c' : Cardinal} (hc' : c' < ℵ₀) :
    toPartENat c ≤ toPartENat c' ↔ c ≤ c' := by
  lift c' to ℕ using hc'
  simp_rw [← partENatOfENat_toENat, toENat_nat, ← toENat_le_nat,
   ← PartENat.withTopOrderIso.symm.le_iff_le, PartENat.ofENat_le, map_le_map_iff]

lemma toPartENat_inj_of_le_aleph0 {c c' : Cardinal} (hc : c ≤ ℵ₀) (hc' : c' ≤ ℵ₀) :
    toPartENat c = toPartENat c' ↔ c = c' :=
  toPartENat_strictMonoOn.injOn.eq_iff hc hc'

@[deprecated (since := "2024-12-29")] alias toPartENat_eq_iff_of_le_aleph0 :=
  toPartENat_inj_of_le_aleph0

theorem toPartENat_mono {c c' : Cardinal} (h : c ≤ c') :
    toPartENat c ≤ toPartENat c' :=
  OrderHomClass.mono _ h

theorem toPartENat_lift (c : Cardinal.{v}) : toPartENat (lift.{u, v} c) = toPartENat c := by
  simp only [← partENatOfENat_toENat, toENat_lift]

theorem toPartENat_congr {β : Type v} (e : α ≃ β) : toPartENat #α = toPartENat #β := by
  rw [← toPartENat_lift, lift_mk_eq.{_, _,v}.mpr ⟨e⟩, toPartENat_lift]

theorem mk_toPartENat_eq_coe_card [Fintype α] : toPartENat #α = Fintype.card α := by
  simp

end Cardinal
