/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
import Mathlib.LinearAlgebra.RootSystem.WeylGroup
import Mathlib.LinearAlgebra.RootSystem.Irreducible


/-!
# Classification of crystallographic root systems whose Dynkin diagram contains a triple edge.
We show that if `P` is a crystallographic root system over a characteristic zero ring, and `b` is a
base whose Cartan matrix has a `-3` entry, then `P` is the `G2` root system.

-/

noncomputable section

open Function Set
open Submodule (span)
open FaithfulSMul (algebraMap_injective)

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace RootPairing

variable   {P : RootPairing ι R M N} [P.IsValuedIn ℤ] (b : P.Base)

/-!
lemma pairingIn_left_zero_of_pairingIn_neg_three [Finite ι] [NoZeroDivisors R]
    [NoZeroSMulDivisors R M] [NoZeroSMulDivisors R N]
    (i j k : b.support) (h3 : P.pairingIn ℤ i j = -3) :
    P.pairingIn ℤ i k = 0 := by
  by_contra h

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
