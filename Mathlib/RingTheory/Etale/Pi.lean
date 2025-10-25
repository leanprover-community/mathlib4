/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.Smooth.Pi
import Mathlib.RingTheory.Unramified.Pi
import Mathlib.RingTheory.Etale.Basic

/-!

# Formal-étaleness of finite products of rings

## Main result

- `Algebra.FormallyEtale.pi_iff`: If `I` is finite, `Π i : I, A i` is `R`-formally-étale
  if and only if each `A i` is `R`-formally-étale.

-/

namespace Algebra.FormallyEtale

variable {R : Type*} {I : Type*} (A : I → Type*)
variable [CommRing R] [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]

theorem pi_iff [Finite I] :
    FormallyEtale R (Π i, A i) ↔ ∀ i, FormallyEtale R (A i) := by
  simp_rw [FormallyEtale.iff_unramified_and_smooth, forall_and]
  rw [FormallyUnramified.pi_iff A, FormallySmooth.pi_iff A]

instance [Finite I] [∀ i, FormallyEtale R (A i)] : FormallyEtale R (Π i, A i) :=
  .of_unramified_and_smooth

end Algebra.FormallyEtale
