/-
Copyright (c) 2025 Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang
-/
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# The Krull dimension of a principal ideal domain

In this file, we proved some results about the dimension of a principal ideal domain.
-/

instance IsPrincipalIdealRing.krullDimLE_one (R : Type*) [CommRing R]
    [IsPrincipalIdealRing R] : Ring.KrullDimLE 1 R := by
  refine Ring.krullDimLE_one_iff.2 fun I hI ↦ or_iff_not_imp_left.2 fun hI' ↦ ?_
  rw [minimalPrimes_eq_minimals, Set.notMem_setOf_iff, not_minimal_iff_exists_lt hI] at hI'
  obtain ⟨P, hlt, hP⟩ := hI'
  have := IsPrincipalIdealRing.of_surjective (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  have : (I.map (Ideal.Quotient.mk P)).IsMaximal := by
    have := Ideal.map_isPrime_of_surjective (f := Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
      (I := I) (by simpa using hlt.le)
    refine IsPrime.to_maximal_ideal ?_
    rw [ne_eq, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    exact hlt.not_ge
  have := Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
    (K := I.map (Ideal.Quotient.mk P))
  simpa [Ideal.comap_map_of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective,
    hlt.le] using this

theorem IsPrincipalIdealRing.ringKrullDim_eq_one (R : Type*) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] (h : ¬ IsField R) : ringKrullDim R = 1 := by
  apply eq_of_le_of_not_lt ?_ fun h' ↦ h ?_
  · rw [← Nat.cast_one, ← Ring.krullDimLE_iff]
    infer_instance
  · have h'' : ringKrullDim R ≤ 0 := Order.le_of_lt_succ h'
    rw [← Nat.cast_zero, ← Ring.krullDimLE_iff] at h''
    exact Ring.KrullDimLE.isField_of_isDomain

/-- In a PID that is not a field, every maximal ideal has height one. -/
lemma IsPrincipalIdealRing.height_eq_one_of_isMaximal {R : Type*} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] (m : Ideal R) [m.IsMaximal] (h : ¬ IsField R) :
    m.height = 1 := by
  refine le_antisymm ?_ ?_
  · suffices h : (m.height : WithBot ℕ∞) ≤ 1 by norm_cast at h
    rw [← IsPrincipalIdealRing.ringKrullDim_eq_one _ h]
    exact Ideal.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'
  · rw [Order.one_le_iff_pos, Ideal.height_eq_primeHeight, Ideal.primeHeight, Order.height_pos]
    exact not_isMin_of_lt (b := ⊥) (Ideal.bot_lt_of_maximal m h)
