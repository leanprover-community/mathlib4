/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate
import Mathlib.LinearAlgebra.RootSystem.Irreducible
import Mathlib.LinearAlgebra.RootSystem.WeylGroup


/-!
# Classification of crystallographic root systems whose Dynkin diagram contains a triple edge.
We show that if `P` is a crystallographic root system over a characteristic zero ring, and `b` is a
base whose Cartan matrix has a `-3` entry, then `P` is the `G2` root system.

-/

noncomputable section

open Function Set
open Submodule (span)
open FaithfulSMul (algebraMap_injective)

variable {ι R M N : Type*} [CommRing R] [CharZero R] [AddCommGroup M] [Module R M] [AddCommGroup N]
[Module R N]

namespace RootPairing

variable {P : RootPairing ι R M N} [P.IsValuedIn ℤ] (b : P.Base)

open Base

lemma pairingIn_neg_one_of_neg_three [Finite ι] [NoZeroDivisors R] (i j : b.support)
    (h3 : P.pairingIn ℤ i j = -3) :
    P.pairingIn ℤ j i = -1 := by
  have hcW := P.coxeterWeightIn_mem_set_of_isCrystallographic i j
  have hnij : P.pairingIn ℤ i j ≠ 0 := by omega
  rw [coxeterWeightIn] at hcW
  have hnji : P.pairingIn ℤ j i ≠ 0 := fun hz ↦ hnij ((pairingIn_zero_iff P ℤ).mp hz)
  have hcW := mem_of_mem_insert_of_ne hcW (Int.mul_ne_zero hnij hnji)
  rw [h3] at hcW
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hcW
  omega
/-!

lemma pairingIn_left_zero_of_pairingIn_neg_three [Finite ι] [NoZeroDivisors R]
    [NoZeroSMulDivisors R M] [NoZeroSMulDivisors R N] (i j k : b.support) (hik : i ≠ k)
    (hjk : j ≠ k) (h3 : P.pairingIn ℤ i j = -3) :
    P.pairingIn ℤ i k = 0 := by
  by_contra h
  have hij : i ≠ j := by
    intro hij
    rw [hij, pairingIn_same] at h3
    omega
  have hleik := lt_of_le_of_ne (cartanMatrix_le_zero_of_ne b i k hik) h
  have hlejk := cartanMatrix_le_zero_of_ne b j k hjk
  simp only [Int.reduceNeg, cartanMatrix, cartanMatrixIn_def] at hleik hlejk
  let v := P.root i + P.root j + P.root k
  have hne : v ≠ 0 := by
    have := b.linInd_root
    contrapose! this
    rw [not_linearIndependent_iff]
    use ⟨{i, j, k}, (by aesop)⟩
    use indicator {i} 1 + indicator {j} 1 + indicator {k} 1
    simp [hij, hij.symm, hjk, hjk.symm, hik, hik.symm, this, v, ← add_assoc]
  have hsp : v ∈ P.rootSpan := by
    refine Submodule.add_mem P.rootSpan ?_ <| Submodule.subset_span (mem_range_self (f := P.root) k)
    exact Submodule.add_mem P.rootSpan (Submodule.subset_span (mem_range_self (f := P.root) i))
      <| Submodule.subset_span (mem_range_self (f := P.root) j)
  have hp := P.rootForm_pos_of_ne_zero hsp
  sorry

lemma pairingIn_right_zero_of_pairingIn_neg_three [Finite ι] [NoZeroDivisors R]
    [NoZeroSMulDivisors R M] [NoZeroSMulDivisors R N] {i j k : b.support} (hik : i ≠ k)
    (hjk : j ≠ k) (h3 : P.pairingIn ℤ i j = -3) :
    P.pairingIn ℤ j k = 0 := by
  sorry

lemma card_eq_two_of_pairingIn_three [Finite ι] [NoZeroDivisors R]
    [NoZeroSMulDivisors R M] [NoZeroSMulDivisors R N] (hI : IsIrreducible P)
    (i j : b.support) (h3 : P.pairingIn ℤ i j = -3) :
    Nat.card b.support = 2 := by
  sorry
-/


end RootPairing
