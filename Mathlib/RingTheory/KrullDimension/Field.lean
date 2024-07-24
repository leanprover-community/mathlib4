/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li, Jujian Zhang
-/
import Mathlib.RingTheory.KrullDimension.Basic

/-!
# The Krull dimension of a field

This file proves that the Krull dimension of a field is zero and that the Krull dimension of an
integral domain is zero if and only if it is a field.
-/

@[simp]
theorem ringKrullDim_eq_zero_of_field (F : Type*) [Field F] : ringKrullDim F = 0 :=
  krullDim_eq_zero_of_unique

theorem ringKrullDim_eq_zero_of_isField {F : Type*} [CommRing F] (hF : IsField F) :
    ringKrullDim F = 0 :=
  @krullDim_eq_zero_of_unique _ _ <| @PrimeSpectrum.instUnique _ hF.toField

attribute [local instance] Ideal.bot_prime

theorem ringKrullDim_eq_zero_iff_isField_of_isDomain (R : Type*) [CommRing R] [IsDomain R] :
    ringKrullDim R = 0 ↔ IsField R := by
  simp only [ringKrullDim_eq_zero_iff_forall_mem_minimalPrimes, minimalPrimes,
    Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff,
    ← not_iff_comm.mp Ring.not_isField_iff_exists_prime, ne_eq, not_exists, not_and, not_imp_not]
