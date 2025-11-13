/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.RingTheory.Noetherian.Defs

/-!

# Compact submodules

-/

variable {R M : Type*} [CommSemiring R] [TopologicalSpace R] [AddCommMonoid M] [Module R M]
variable [TopologicalSpace M] [ContinuousAdd M] [ContinuousSMul R M]

lemma Submodule.isCompact_of_fg [CompactSpace R] {N : Submodule R M} (hN : N.FG) :
    IsCompact (X := M) N := by
  obtain ⟨s, hs⟩ := hN
  have : LinearMap.range (Fintype.linearCombination R (α := s) Subtype.val) = N := by
    simp [hs]
  rw [← this]
  refine isCompact_range ?_
  simp only [Fintype.linearCombination, Finset.univ_eq_attach, LinearMap.coe_mk,
    AddHom.coe_mk]
  fun_prop

lemma Ideal.isCompact_of_fg [IsTopologicalSemiring R] [CompactSpace R]
    {I : Ideal R} (hI : I.FG) : IsCompact (X := R) I :=
  Submodule.isCompact_of_fg hI

variable (R M) in
lemma Module.Finite.compactSpace [CompactSpace R] [Module.Finite R M] : CompactSpace M :=
  ⟨Submodule.isCompact_of_fg (Module.Finite.fg_top (R := R))⟩

instance (priority := low) IsNoetherianRing.isClosed_ideal
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsNoetherianRing R] [CompactSpace R] [T2Space R] (I : Ideal R) :
    IsClosed (X := R) I :=
  (Ideal.isCompact_of_fg (IsNoetherian.noetherian I)).isClosed
