/-
Copyright (c) 2025 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.RingTheory.Perfection
import Mathlib.RingTheory.Perfectoid.Untilt

/-!
# Integral Perfectoid Rings


-/

section IsPerfectoidPsU

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/--
Fix a (prime) number `p`. Let `A` be a topological commutative ring.
A non-zero-divisor `π : A` is a perfectoid pseudo-uniformizer of `A`
if the following conditions hold,

1. The topology on `A` is `π`-adical and `A` is `π`-adically complete;

2. `p ∈ (π^p)`

-/
structure IsPerfectoidPsU (p : ℕ) (π : A) : Prop where
  mem_nonZeroDivisor : π ∈ nonZeroDivisors A
  isAdic : IsAdic (Ideal.span {π})
  isAdicComplete : IsAdicComplete (Ideal.span {π}) A
  p_mem_pow_p : π ^ p ∣ (p : A)
  frob_inj : ∀ x, π ^ p ∣ x ^ p → π ∣ x
  frob_surj : ∀ x, ∃ y, π ^ p ∣ x - y ^ p

end IsPerfectoidPsU

class IntegralPerfectoid (A : Type*) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] (p : outParam ℕ) : Prop where
  exists_isPerfectoidPsU : ∃ π : A, IsPerfectoidPsU p π
#check Tilt
namespace IntegralPerfectoid

variable (A : Type*) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] (p : ℕ) [Fact p.Prime] [IntegralPerfectoid A p]

end IntegralPerfectoid
