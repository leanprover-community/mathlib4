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

lemma cartanMatrix_ne_neg_four [Finite ι] [NoZeroDivisors R]
    [NoZeroSMulDivisors R M] [NoZeroSMulDivisors R N] (i j : b.support) :
    -4 ≠ b.cartanMatrix i j := by
  simp only [Int.reduceNeg, cartanMatrix, cartanMatrixIn_def, Matrix.of_apply]
  have h := b.linInd_root
  contrapose! h
  have hnz : P.pairingIn ℤ i j * P.pairingIn ℤ j i ≠ 0 := by
    have : P.pairingIn ℤ i j ≠ 0 := by omega
    exact Int.mul_ne_zero this fun hz ↦ this ((pairingIn_zero_iff P ℤ).mp hz)
  have hcW : P.pairingIn ℤ i j * P.pairingIn ℤ j i ∈ ({1, 2, 3, 4} : Set ℤ):= by
    have hcW := P.coxeterWeightIn_mem_set_of_isCrystallographic i j
    rw [coxeterWeightIn] at hcW
    exact mem_of_mem_insert_of_ne hcW hnz
  have hji := (Prod.mk_inj.mp (Int.neg_four_neg_one_iff.mpr ⟨hcW, h.symm⟩)).2
  have hsc := (P.pairingIn_neg_one_neg_four_iff ℤ j i).mp ⟨hji, h.symm⟩
  have hij : i ≠ j := by
    intro hij
    rw [← hij, pairingIn_same] at h
    omega
  refine not_linearIndependent_iff.mpr ?_
  use ⟨{i, j}, (by aesop)⟩
  let g : b.support → R := indicator {i} 1 + indicator {j} 2
  use g
  simp [hsc, hij, hij.symm, g]

end IsCrystallographic

end RootPairing.Base
