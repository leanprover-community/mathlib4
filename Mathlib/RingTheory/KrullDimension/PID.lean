/-
Copyright (c) 2025 Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang
-/
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# The Krull dimension of a principal ideal domain

In this file, we proved some results about the dimension of a principal ideal domain.
-/

instance IsPrincipalIdealRing.krullDimLE_one (R : Type*) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] : Ring.KrullDimLE 1 R := by
  rw [Ring.krullDimLE_one_iff]
  apply fun I hI ↦ Classical.or_iff_not_imp_left.mpr fun hI' ↦
    IsPrime.to_maximal_ideal (hpi := hI) ?_
  simp_all [IsDomain.minimalPrimes_eq_singleton_bot]

theorem IsPrincipalIdealRing.ringKrullDim_eq_one (R : Type*) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] (h : ¬ IsField R) : ringKrullDim R = 1 := by
  apply eq_of_le_of_not_lt ?_ fun h' ↦ h ?_
  · rw [← Nat.cast_one, ← Ring.krullDimLE_iff]
    infer_instance
  · have h'' : ringKrullDim R ≤ 0 := Order.le_of_lt_succ h'
    rw [← Nat.cast_zero, ← Ring.krullDimLE_iff] at h''
    exact Ring.KrullDimLE.isField_of_isDomain
