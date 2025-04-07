/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wanyi He, Jiedong Jiang, Jingting Wang, Andrew Yang, Shouxin Zhang
-/
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.Artinian.Ring

/-!
# Corollaries of Hopkins-Levitzki

In this file, we prove several corollaries of the Hopkins-Levitzki theorem.
-/
variable {R : Type*} [CommRing R]

theorem isArtinianRing_iff_krullDimLE_zero [IsNoetherianRing R] :
    IsArtinianRing R ↔ Ring.KrullDimLE 0 R := by
  rwa [isArtinianRing_iff_isNoetherianRing_krullDimLE_zero, and_iff_right]

lemma IsArtinianRing.eq_maximalIdeal_of_isPrime [IsArtinianRing R] [IsLocalRing R]
    (I : Ideal R) [I.IsPrime] : I = IsLocalRing.maximalIdeal R := by
  have : Ring.KrullDimLE 0 R := by rwa [← isArtinianRing_iff_krullDimLE_zero]
  exact Ring.KrullDimLE.eq_maximalIdeal_of_isPrime I

lemma IsArtinianRing.radical_eq_maximalIdeal [IsArtinianRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I ≠ ⊤) : I.radical = IsLocalRing.maximalIdeal R := by
  rw [Ideal.radical_eq_sInf]
  refine (sInf_le ?_).antisymm (le_sInf ?_)
  · exact ⟨IsLocalRing.le_maximalIdeal hI, inferInstance⟩
  · rintro J ⟨h₁, h₂⟩
    exact (eq_maximalIdeal_of_isPrime J).ge

lemma isArtinianRing_iff_isNilpotent_maximalIdeal [IsNoetherianRing R] [IsLocalRing R]:
    IsArtinianRing R ↔ IsNilpotent (IsLocalRing.maximalIdeal R) := by
  constructor
  · intro h
    rw [← IsArtinianRing.radical_eq_maximalIdeal (⊥ : Ideal R) bot_ne_top]
    exact IsArtinianRing.isNilpotent_nilradical
  · rintro ⟨n, hn⟩
    rcases eq_or_ne n 0 with (rfl|hn')
    · rw [pow_zero] at hn
      exact (one_ne_zero hn).elim
    · rw [isArtinianRing_iff_krullDimLE_zero]
      refine Ring.KrullDimLE.mk₀ (fun I hI ↦ ?_)
      suffices IsLocalRing.maximalIdeal R ≤ I by
        rw [← (IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hI.ne_top this]
        infer_instance
      rw [← hI.pow_le_iff hn', hn]
      exact bot_le
