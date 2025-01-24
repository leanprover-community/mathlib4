/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.LinearAlgebra.RootSystem.Base

/-!
# Cartan matrices for root systems

This file contains definitions and basic results about Cartan matrices of root pairings / systems.

## Main definitions:
 * `RootPairing.cartanMatrix`: the Cartan matrix of a crystallographic root pairing, with respect to
   a base `b`.

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

/-- The Cartan matrix of a crystallographic root pairing, with respect to a base `b`. -/
abbrev cartanMatrix [P.IsCrystallographic] :
    Matrix b.support b.support ℤ :=
  b.cartanMatrixIn ℤ

lemma cartanMatrixIn_def (i j : b.support) :
    b.cartanMatrixIn S i j = P.pairingIn S i j :=
  rfl

variable [Nontrivial R] [NoZeroSMulDivisors S R]

@[simp]
lemma cartanMatrixIn_apply_same (i : b.support) :
    b.cartanMatrixIn S i i = 2 :=
  NoZeroSMulDivisors.algebraMap_injective S R <| by simp [cartanMatrixIn_def, map_ofNat]

end RootPairing.Base
