/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.LinearAlgebra.RootSystem.Base
import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas

/-!
# Cartan matrices for root systems

This file contains definitions and basic results about Cartan matrices of root pairings / systems.

## Main definitions:
 * `RootPairing.Base.cartanMatrix`: the Cartan matrix of a crystallographic root pairing, with
   respect to a base `b`.

-/

noncomputable section

open Function Set

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace RootPairing.Base

variable (S : Type*) [CommRing S] [Algebra S R]
  {P : RootPairing ι R M N} [P.IsValuedIn S] (b : P.Base)

/-- The Cartan matrix of a root pairing, taking values in `S`, with respect to a base `b`.

See also `RootPairing.Base.cartanMatrix`. -/
def cartanMatrixIn :
    Matrix b.support b.support S :=
  .of fun i j ↦ P.pairingIn S i j

lemma cartanMatrixIn_def (i j : b.support) :
    b.cartanMatrixIn S i j = P.pairingIn S i j :=
  rfl

@[simp]
lemma cartanMatrixIn_apply_same [FaithfulSMul S R] (i : b.support) :
    b.cartanMatrixIn S i i = 2 :=
  FaithfulSMul.algebraMap_injective S R <| by simp [cartanMatrixIn_def, map_ofNat]

section IsCrystallographic

variable [P.IsCrystallographic]

/-- The Cartan matrix of a crystallographic root pairing, with respect to a base `b`. -/
abbrev cartanMatrix :
    Matrix b.support b.support ℤ :=
  b.cartanMatrixIn ℤ

variable [CharZero R]

lemma cartanMatrix_apply_same (i : b.support) :
    b.cartanMatrix i i = 2 :=
  b.cartanMatrixIn_apply_same ℤ i

lemma cartanMatrix_le_zero_of_ne [Finite ι] [NoZeroDivisors R]
    [NoZeroSMulDivisors R M] [NoZeroSMulDivisors R N]
    (i j : b.support) (h : i ≠ j) :
    b.cartanMatrix i j ≤ 0 :=
  b.pairingIn_le_zero_of_ne (by rwa [ne_eq, ← Subtype.ext_iff]) i.property j.property

lemma neg_four_lt_cartanMatrix [Finite ι] [NoZeroDivisors R]
    [NoZeroSMulDivisors R M] [NoZeroSMulDivisors R N] (i j : b.support) :
    -4 < b.cartanMatrix i j := by
  simp only [Int.reduceNeg, cartanMatrix, cartanMatrixIn_def]
  have hcW := P.coxeterWeightIn_mem_set_of_isCrystallographic i j
  have hcWle := coxeterWeightIn_le_four P ℤ i j
  rw [coxeterWeightIn] at hcW hcWle
  by_contra h
  rw [Int.not_gt_eq] at h
  have hnij : P.pairingIn ℤ i j ≠ 0 := by omega
  have hne : i ≠ j := by
    intro he
    rw [he, pairingIn_same] at h
    omega
  have hnji : P.pairingIn ℤ j i ≠ 0 := fun hz ↦ hnij ((pairingIn_zero_iff P ℤ).mp hz)
  have hcW := mem_of_mem_insert_of_ne hcW (Int.mul_ne_zero hnij hnji)
  have hjilt : P.pairingIn ℤ j i < 0 := by
    refine lt_of_le_of_ne ?_ hnji
    simpa [cartanMatrix, cartanMatrixIn_def] using (cartanMatrix_le_zero_of_ne b j i hne.symm)
  by_cases h4 : P.pairingIn ℤ i j = -4
  · have hji := (Prod.mk_inj.mp (Int.neg_four_neg_one_iff.mpr ⟨hcW, h4⟩)).2
    have hsc := (P.pairingIn_neg_one_neg_four_iff ℤ j i).mp ⟨hji, h4⟩
    have hl := b.linInd_root
    refine (not_linearIndependent_iff.mpr ?_) hl
    use ⟨{i, j}, (by aesop)⟩
    use indicator {i} 1 + indicator {j} 2
    simp [hsc, hne, hne.symm]
  · have hlt : P.pairingIn ℤ ↑i ↑j < -4 := lt_of_le_of_ne h h4
    nlinarith

end IsCrystallographic

end RootPairing.Base
