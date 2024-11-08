/-
Copyright (c) 2024 Daniel Weber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Weber
-/
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Multiplicity
import Mathlib.Algebra.Squarefree.Basic

/-!
# Multiplicity and derivations

--/

variable {M : Type*} [CommSemiring M] {F : Type*} [CommRing F] [Algebra M F]

lemma multiplicity_deriv [IsDomain F] [WfDvdMonoid F] (D : Derivation M F F)
    [Algebra ℚ F] (p : F) (hp : Prime p) (hp2 : ¬p ∣ D p) (a : F) (h : p ∣ a) :
    emultiplicity p (D a) + 1 = emultiplicity p a := by
  by_cases ha : a = 0
  · simp [ha]
  have mf : multiplicity.Finite p a := multiplicity.finite_prime_left hp ha
  rw [mf.emultiplicity_eq_multiplicity]
  have mne0 : multiplicity p a ≠ 0 := multiplicity_ne_zero.mpr h
  obtain ⟨c, h1, h2⟩ := mf.exists_eq_pow_mul_and_not_dvd
  nth_rw 1 [h1]
  simp only [Derivation.leibniz, smul_eq_mul, nsmul_eq_mul]
  have : emultiplicity p (c * D (p ^ multiplicity p a)) = multiplicity p a - 1 := by
    simp only [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, hp, emultiplicity_mul, h2,
      not_false_eq_true, emultiplicity_eq_zero.mpr, emultiplicity_pow_self_of_prime, ENat.coe_sub,
      Nat.cast_one, hp2, add_zero, zero_add]
    rw [emultiplicity_eq_zero.mpr, zero_add]
    refine fun nh ↦ hp.not_unit (isUnit_of_dvd_unit nh ?_)
    rw [← map_natCast (algebraMap ℚ F)]
    exact IsUnit.map _ (.mk0 _ <| mod_cast mne0)
  rw [emultiplicity_add_of_gt, this]
  · norm_cast; omega
  rw [this]
  simp only [hp, emultiplicity_mul, emultiplicity_pow_self_of_prime]
  norm_cast
  cases emultiplicity p (D c)
  · simp only [add_top, ENat.coe_lt_top]
  · norm_cast
    omega
