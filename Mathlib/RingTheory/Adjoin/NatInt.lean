/-

Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.Algebra.Subalgebra.Nat
import Mathlib.Algebra.Algebra.Subalgebra.Int
import Mathlib.RingTheory.Adjoin.Basic

/-!
# Adjoining elements to form subalgebras

-/

open Algebra

theorem Algebra.adjoin_nat {R : Type*} [Semiring R] (s : Set R) :
    adjoin ℕ s = subalgebraOfSubsemiring (Subsemiring.closure s) :=
  le_antisymm (adjoin_le Subsemiring.subset_closure)
    (Subsemiring.closure_le.2 subset_adjoin : Subsemiring.closure s ≤ (adjoin ℕ s).toSubsemiring)

theorem Algebra.adjoin_int {R : Type*} [Ring R] (s : Set R) :
    adjoin ℤ s = subalgebraOfSubring (Subring.closure s) :=
  le_antisymm (adjoin_le Subring.subset_closure)
    (Subring.closure_le.2 subset_adjoin : Subring.closure s ≤ (adjoin ℤ s).toSubring)
#align algebra.adjoin_int Algebra.adjoin_int

/-- The `ℕ`-algebra equivalence between `Subsemiring.closure s` and `Algebra.adjoin ℕ s` given
by the identity map. -/
def Subsemiring.closureEquivAdjoinNat {R : Type*} [Semiring R] (s : Set R) :
    Subsemiring.closure s ≃ₐ[ℕ] Algebra.adjoin ℕ s :=
  Subalgebra.equivOfEq (subalgebraOfSubsemiring <| Subsemiring.closure s) _ (adjoin_nat s).symm

/-- The `ℤ`-algebra equivalence between `Subring.closure s` and `Algebra.adjoin ℤ s` given by
the identity map. -/
def Subring.closureEquivAdjoinInt {R : Type*} [Ring R] (s : Set R) :
    Subring.closure s ≃ₐ[ℤ] Algebra.adjoin ℤ s :=
  Subalgebra.equivOfEq (subalgebraOfSubring <| Subring.closure s) _ (adjoin_int s).symm


