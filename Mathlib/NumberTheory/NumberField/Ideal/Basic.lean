/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.NumberTheory.NumberField.Units.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

import Mathlib.Sandbox

/-!
# Basic results on integral ideals of a number field

## Main definitions and results

*
-/

section torsionMapQuot

open Ideal NumberField Units

variable {K : Type*} [Field K] (I : Ideal (𝓞 K))

def Ideal.torsionMapQuot : (Units.torsion K) →* ((𝓞 K) ⧸ I)ˣ :=
  (Units.map (Ideal.Quotient.mk I).toMonoidHom).restrict (torsion K)

@[simp]
theorem Ideal.torsionMapQuot_apply {x : (𝓞 K)ˣ} (hx : x ∈ torsion K) :
    torsionMapQuot I ⟨x, hx⟩ = Ideal.Quotient.mk I x := rfl

variable [NumberField K]

theorem Ideal.torsionMapQuot_injective (hI₁ : absNorm I ≠ 1)
    (hI₂ : (absNorm I).Coprime (torsionOrder K)) :
    Function.Injective (torsionMapQuot I) := by
  refine (injective_iff_map_eq_one _).mpr fun ⟨ζ, hζ⟩ h ↦ ?_
  rw [← rootsOfUnity_eq_torsion] at hζ
  obtain ⟨t, ht₀, ht, hζ⟩ := isPrimitiveRoot_of_mem_rootsOfUnity hζ
  by_cases ht' : 2 ≤ t
  · exfalso
    rw [Units.ext_iff, torsionMapQuot_apply, Units.val_one, show 1 = Quotient.mk I 1 by rfl,
      Quotient.eq] at h
    obtain ⟨p, hp, h₁⟩ := Nat.exists_prime_and_dvd hI₁
    have h₂ : (p : ℤ) ∣ (Algebra.norm ℤ) ((ζ : 𝓞 K) - 1) :=
      Int.dvd_trans (Int.natCast_dvd_natCast.mpr h₁) (absNorm_dvd_norm_of_mem h)
    
#exit


    have h₁ := Ideal.absNorm_dvd_norm_of_mem h

    have h₃ : (p : ℤ) ∣ (Algebra.norm ℤ) ((ζ.val : 𝓞 K) - 1) := by
      rw [← Int.natCast_dvd_natCast] at h₂
      exact Int.dvd_trans h₂ h₁
    have : Fact (Nat.Prime p) := { out := hp }
    have h₄ := IsPrimitiveRoot.prime_dvd_of_dvd_norm_sub_one (K := K) ht' (by simpa using hζ) h₃
    have h₅ : p ∣ n := by exact dvd_trans h₄ ht
    have h₆ := Nat.dvd_gcd h₂ h₅
    rw [hI₂] at h₆
    exact (hp.not_dvd_one h₆).elim
  · have : t = 1 := le_antisymm (Nat.le_of_lt_succ (not_le.mp ht')) (Nat.pos_of_ne_zero ht₀)
    simpa [this] using hζ
