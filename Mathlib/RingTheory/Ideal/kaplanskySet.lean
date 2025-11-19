/-
Copyright (c) 2025 Emilie Uthaiwat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emilie Uthaiwat, Riccardo Brasca
-/
import Mathlib.RingTheory.UniqueFactorizationDomain.Ideal

/-!
# Kaplansky's sets

This file contains the definition of a `kaplanskySet`.

Let `S` be a subsemigroup of a semiring `R`. The `kaplanskySet` associated to `S` is the set of
ideals of `R` which do not intersect `S`.

## Tags

kaplansky, Kaplansky, ideal
-/

variable {R : Type*}

/-! ### Definition -/

/-- The set of ideals of a semiring R which do not intersect a given subsemigroup S -/
def kaplanskySet [Semiring R] (S : Subsemigroup R) :=
  { I : Ideal R | (I : Set R) ∩ S = ∅ }

theorem mem_kaplanskySet_iff_inter_eq_empty [Semiring R] (S : Subsemigroup R) (P : Ideal R) :
    P ∈ kaplanskySet S ↔ (P : Set R) ∩ S = ∅ := Iff.rfl
