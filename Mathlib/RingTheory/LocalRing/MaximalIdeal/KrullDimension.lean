/-
Copyright (c) 2026 Haoming Ning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haoming Ning
-/
module

public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Nakayama

/-!
# Krull dimension and the maximal ideal of a local ring

In this file, we prove results relating the Krull dimension of a local ring
to properties of its maximal ideal.

## Main results

* `IsLocalRing.ringKrullDim_eq_zero_of_maximalIdeal_eq_bot`:
  A local ring whose maximal ideal is the zero ideal has Krull dimension zero.
* `IsLocalRing.exists_mem_maximalIdeal_not_mem_sq`:
  In a Noetherian local ring of positive Krull dimension,
  there exists an element in the maximal ideal not in its square.

## Acknowledgements

Thanks to Dora Kassabova and Leopold Mayer for edit suggestions.
-/

@[expose] public section

namespace IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- A local ring whose maximal ideal is `⊥` has Krull dimension zero. -/
theorem ringKrullDim_eq_zero_of_maximalIdeal_eq_bot
    (h : maximalIdeal R = ⊥) : ringKrullDim R = 0 := by
  rw [← maximalIdeal_height_eq_ringKrullDim, h,
    Ideal.height_bot, WithBot.coe_zero]

/-- In a Noetherian local ring of positive Krull dimension,
there exists an element in the maximal ideal not in its square. -/
theorem exists_mem_maximalIdeal_not_mem_sq
    [IsNoetherianRing R] (h : 0 < ringKrullDim R) :
    ∃ x ∈ maximalIdeal R, x ∉ (maximalIdeal R) ^ 2 := by
  by_contra h_contra
  push_neg at h_contra
  have := le_antisymm h_contra (Ideal.pow_le_self two_ne_zero)
  exact h.ne' (ringKrullDim_eq_zero_of_maximalIdeal_eq_bot
    (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _
      (IsNoetherian.noetherian _)
      (by rwa [Ideal.smul_eq_mul, ← sq])
      (maximalIdeal_le_jacobson ⊥)))

end IsLocalRing
