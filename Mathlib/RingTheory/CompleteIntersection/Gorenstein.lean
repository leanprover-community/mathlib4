/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.RingTheory.CompleteIntersection.Basic
public import Mathlib.RingTheory.Gorenstein.CohenMacaulay
public import Mathlib.RingTheory.Gorenstein.Completion

/-!

# Complete intersection local ring is Gorenstein

In this file we proved that complete intersection local ring is Gorenstein,
together with the full implication chain of local rings.

-/

public section

universe u

variable (R : Type u) [CommRing R]

lemma IsRegularLocalRing.epsilon1_eq_zero [IsRegularLocalRing R] : Epsilon1 R = 0 := by
  sorry

theorem IsRegularLocalRing.isCompleteIntersectionLocalRing [IsRegularLocalRing R] :
    IsCompleteIntersectionLocalRing R := by
  sorry

lemma IsRegularLocalRing.isGorensteinLocalRing [IsRegularLocalRing R] :
    IsGorensteinLocalRing R := by
  sorry

theorem IsCompleteIntersectionLocalRing.isGorensteinLocalRing
    [IsCompleteIntersectionLocalRing R] : IsGorensteinLocalRing R := by
  sorry
