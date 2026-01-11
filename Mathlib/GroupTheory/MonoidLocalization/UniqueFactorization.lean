/-
Copyright (c) 2026 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Algebra.Ring.Regular
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-! # Localization preserves unique factorization -/

@[expose] public section

variable {M N : Type*}

namespace Submonoid.LocalizationMap

section CommMonoidWithZero
variable [CommMonoidWithZero M] [CommMonoidWithZero N] {S : Submonoid M}

theorem map_prime (f : S.LocalizationMap N) {m : M} (prime : Prime m)
    (n0 : f m ≠ 0) (nu : ¬ IsUnit (f m)) : Prime (f m) := by
  refine ⟨n0, nu, fun n₁ n₂ dvd ↦ ?_⟩
  have ⟨⟨m₁, s₁⟩, eq₁⟩ := f.surj n₁
  have ⟨⟨m₂, s₂⟩, eq₂⟩ := f.surj n₂
  have := (f.map_units (s₁ * s₂)).dvd_mul_right.mpr dvd
  rw [Submonoid.mul_def, map_mul, mul_mul_mul_comm, eq₁, eq₂, ← map_mul, f.map_dvd_map] at this
  have ⟨s, hs, dvd⟩ := this
  rw [← mul_assoc] at dvd
  obtain dvd | dvd := prime.dvd_or_dvd dvd
  all_goals have := map_dvd f dvd
  · rw [map_mul, (f.map_units ⟨s, hs⟩).dvd_mul_left, ← eq₁, (f.map_units s₁).dvd_mul_right] at this
    exact .inl this
  · rw [← eq₂, (f.map_units s₂).dvd_mul_right] at this; exact .inr this

theorem irreducible_of_map_wfDvdMonoid [WfDvdMonoid M] (f : S.LocalizationMap N) {m : M}
    (hm : Irreducible (f m)) : ∃ u m' : M, IsUnit (f u) ∧ Irreducible m' ∧ m = u * m' := by
  induction m using WfDvdMonoid.induction_on_irreducible with
  | zero => exact (hm.ne_zero f.map_zero).elim
  | unit u hu => exact (hm.not_isUnit (hu.map f)).elim
  | mul a i ha0 hi ha =>
    rw [map_mul, irreducible_mul_iff] at hm
    obtain hia | hai := hm
    · exact ⟨a, i, hia.2, hi, mul_comm ..⟩
    · obtain ⟨u, m', hu, hm', rfl⟩ := ha hai.1
      exact ⟨u * i, m', by simpa using hu.mul hai.2, hm', by ac_rfl⟩

end CommMonoidWithZero

open UniqueFactorizationMonoid in
theorem uniquFactorizationMonoid [CancelCommMonoidWithZero M] [CancelCommMonoidWithZero N]
    {S : Submonoid M} (f : S.LocalizationMap N)
    [UniqueFactorizationMonoid M] : UniqueFactorizationMonoid N :=
  .of_exists_prime_factors fun n hn ↦ by
    classical
    have ⟨⟨m, s⟩, eq⟩ := f.surj n
    use ((factors m).map f).filter (¬ IsUnit ·)
    rw [Ne, ← (f.map_units s).mul_left_eq_zero, eq] at hn
    refine ⟨fun x hx ↦ ?_, .trans (eq ▸ ?_) ((associated_mul_unit_left _ _ (f.map_units s)))⟩
    · rw [Multiset.mem_filter, Multiset.mem_map] at hx
      obtain ⟨p, hp, rfl⟩ := hx.1
      exact f.map_prime (prime_of_factor _ hp)
        (mt (fun h ↦ eq_zero_of_zero_dvd <| h ▸ map_dvd f (dvd_of_mem_factors hp)) hn) hx.2
    · exact .trans (.trans (associated_unit_mul_right _ _ <|
        IsUnit.multisetProd_iff.mpr fun x hx ↦ (Multiset.mem_filter.mp hx).2) <| .of_eq <|
        (Multiset.prod_filter_mul_prod_filter_not _).trans (f.toMonoidHom.map_multiset_prod _).symm)
        ((factors_prod (mt (by simp [·]) hn)).map f)

end Submonoid.LocalizationMap

variable (N) in
theorem IsLocalization.uniqueFactorizationMonoid [CommSemiring M] [CommSemiring N] [Algebra M N]
    (S : Submonoid M) [IsLocalization S N] [IsCancelMulZero M] [UniqueFactorizationMonoid M] :
    letI := (toLocalizationMap S N).isCancelMulZero
    UniqueFactorizationMonoid N :=
  letI := (toLocalizationMap S N).isCancelMulZero
  (toLocalizationMap S N).uniquFactorizationMonoid
