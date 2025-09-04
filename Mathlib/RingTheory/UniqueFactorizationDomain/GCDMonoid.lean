/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Aaron Anderson
-/
import Mathlib.RingTheory.UniqueFactorizationDomain.FactorSet
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

/-!
# Building GCD out of unique factorization

## Main results
* `UniqueFactorizationMonoid.toGCDMonoid`: choose a GCD monoid structure given unique factorization.
-/

variable {α : Type*}

local infixl:50 " ~ᵤ " => Associated

section

open Associates UniqueFactorizationMonoid

/-- `toGCDMonoid` constructs a GCD monoid out of a unique factorization domain. -/
noncomputable def UniqueFactorizationMonoid.toGCDMonoid (α : Type*) [CancelCommMonoidWithZero α]
    [UniqueFactorizationMonoid α] : GCDMonoid α where
  gcd a b := Quot.out (Associates.mk a ⊓ Associates.mk b : Associates α)
  lcm a b := Quot.out (Associates.mk a ⊔ Associates.mk b : Associates α)
  gcd_dvd_left a b := by
    rw [← mk_dvd_mk, Associates.quot_out, congr_fun₂ dvd_eq_le]
    exact inf_le_left
  gcd_dvd_right a b := by
    rw [← mk_dvd_mk, Associates.quot_out, congr_fun₂ dvd_eq_le]
    exact inf_le_right
  dvd_gcd {a b c} hac hab := by
    rw [← mk_dvd_mk, Associates.quot_out, congr_fun₂ dvd_eq_le, le_inf_iff,
      mk_le_mk_iff_dvd, mk_le_mk_iff_dvd]
    exact ⟨hac, hab⟩
  lcm_zero_left a := by simp
  lcm_zero_right a := by simp
  gcd_mul_lcm a b := by
    rw [← mk_eq_mk_iff_associated, ← Associates.mk_mul_mk, ← associated_iff_eq, Associates.quot_out,
      Associates.quot_out, mul_comm, sup_mul_inf, Associates.mk_mul_mk]

/-- `toNormalizedGCDMonoid` constructs a GCD monoid out of a normalization on a
  unique factorization domain. -/
noncomputable def UniqueFactorizationMonoid.toNormalizedGCDMonoid (α : Type*)
    [CancelCommMonoidWithZero α] [UniqueFactorizationMonoid α] [NormalizationMonoid α] :
    NormalizedGCDMonoid α :=
  { ‹NormalizationMonoid α› with
    gcd := fun a b => (Associates.mk a ⊓ Associates.mk b).out
    lcm := fun a b => (Associates.mk a ⊔ Associates.mk b).out
    gcd_dvd_left := fun a b => (out_dvd_iff a (Associates.mk a ⊓ Associates.mk b)).2 <| inf_le_left
    gcd_dvd_right := fun a b =>
      (out_dvd_iff b (Associates.mk a ⊓ Associates.mk b)).2 <| inf_le_right
    dvd_gcd := fun {a} {b} {c} hac hab =>
      show a ∣ (Associates.mk c ⊓ Associates.mk b).out by
        rw [dvd_out_iff, le_inf_iff, mk_le_mk_iff_dvd, mk_le_mk_iff_dvd]
        exact ⟨hac, hab⟩
    lcm_zero_left := fun a => show (⊤ ⊔ Associates.mk a).out = 0 by simp
    lcm_zero_right := fun a => show (Associates.mk a ⊔ ⊤).out = 0 by simp
    gcd_mul_lcm := fun a b => by
      rw [← out_mul, mul_comm, sup_mul_inf, mk_mul_mk, out_mk]
      exact normalize_associated (a * b)
    normalize_gcd := fun a b => by apply normalize_out _
    normalize_lcm := fun a b => by apply normalize_out _ }

instance (α) [CancelCommMonoidWithZero α] [UniqueFactorizationMonoid α] :
    Nonempty (NormalizedGCDMonoid α) := by
  letI := UniqueFactorizationMonoid.normalizationMonoid (α := α)
  classical exact ⟨UniqueFactorizationMonoid.toNormalizedGCDMonoid α⟩

end
