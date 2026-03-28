/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-!
# Transcendental separable extensions
-/

universe u v

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]

@[expose] public section

class Algebra.IsSeparablyGenerated : Prop where
  isSeparable' : ∃ (ι : Type v) (f : ι → A),
    IsTranscendenceBasis R f ∧
    Algebra.IsSeparable (Algebra.adjoin R (Set.range f)) A

class Algebra.IsTranscendentalSeparable : Prop where
  forall_isSeparablyGenerated : ∀ (A' : Subalgebra R A),
    Algebra.EssFiniteType R A' → Algebra.IsSeparablyGenerated R A'

lemma tensorProduct_of_isSeparablyGenerated {k : Type*} [Field k]
    {S : Type*} [CommRing S] [IsReduced S] [Algebra k S] {K : Type*} [Field K] [Algebra k K] :
    IsReduced (TensorProduct k K S) := by
  sorry
