/-
Copyright (c) 2025 Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang
-/
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Zero

/-!
# The Krull dimension of a local ring

In this file, we proved some results about the Krull dimension of a local ring.
-/

lemma ringKrullDim_eq_one_iff_of_isLocalRing_isDomain {R : Type*}
    [CommRing R] [IsLocalRing R] [IsDomain R] : ringKrullDim R = 1 ↔ ¬ IsField R ∧
    ∀ (x : R), x ≠ 0 → IsLocalRing.maximalIdeal R ≤ Ideal.radical (Ideal.span {x}) := by
  refine ⟨fun h ↦ ⟨fun h' ↦ ?_, ?_⟩, fun ⟨hn, h⟩ ↦ ?_⟩
  · exact zero_ne_one ((ringKrullDim_eq_zero_of_isField h') ▸ h)
  · intro x hx
    rw [Ideal.radical_eq_sInf]
    refine le_sInf (fun J ⟨hJ1, hJ2⟩ ↦ ?_)
    have : J.IsMaximal :=
      Ring.krullDimLE_one_iff_of_noZeroDivisors.mp (Ring.krullDimLE_iff.mpr (by simp [h]))
        J (fun hJ3 ↦ hx (by simp_all)) hJ2
    exact le_of_eq (IsLocalRing.eq_maximalIdeal this).symm
  · have : ¬ ringKrullDim R ≤ 0 := fun h ↦ by
      have : Ring.KrullDimLE 0 R := Ring.krullDimLE_iff.mpr h
      exact hn Ring.KrullDimLE.isField_of_isDomain
    suffices h : Ring.KrullDimLE 1 R by
      rw [Ring.krullDimLE_iff] at h
      exact le_antisymm h (Order.succ_le_of_lt (lt_of_not_ge this))
    refine Ring.krullDimLE_one_iff_of_noZeroDivisors.mpr fun I hI hI_prime ↦ ?_
    obtain ⟨x, hI, hx⟩ : ∃ (x : R), x ∈ I ∧ x ≠ 0 := by
      apply by_contradiction fun h ↦ (hI (le_antisymm (fun x ↦ ?_) bot_le))
      simp only [ne_eq, not_exists, not_and, not_not] at h
      exact fun hx ↦ h x hx
    have : IsLocalRing.maximalIdeal R ≤ I := le_trans (h x hx)
      ((Ideal.IsRadical.radical_le_iff hI_prime.isRadical).mpr
        ((Ideal.span_singleton_le_iff_mem I).mpr hI))
    have := Ideal.IsMaximal.eq_of_le (IsLocalRing.maximalIdeal.isMaximal R) hI_prime.ne_top this
    exact this ▸ (IsLocalRing.maximalIdeal.isMaximal R)
