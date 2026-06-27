/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.RingTheory.CompleteIntersection.Basic
public import Mathlib.RingTheory.Gorenstein.CohenMacaulay
public import Mathlib.RingTheory.Gorenstein.Completion
public import Mathlib.RingTheory.RegularLocalRing.GlobalDimension

/-!

# Complete intersection local ring is Gorenstein

In this file we proved that complete intersection local ring is Gorenstein,
together with the full implication chain of local rings.

-/

public section

universe u

open IsLocalRing

variable (R : Type u) [CommRing R]

lemma IsRegularLocalRing.epsilon1_eq_zero [IsRegularLocalRing R] : Epsilon1 R = 0 := by
  let l := (Submodule.FG.finite_generators (maximalIdeal R).fg_of_isNoetherianRing).toFinset.toList
  have eq : Ideal.ofList l = maximalIdeal R := by
    simp [l, Ideal.ofList, Submodule.span_generators]
  have len : l.length = ringKrullDim R := by
    simp [← (isRegularLocalRing_iff R).mp ‹_›, l, ← Set.ncard_eq_toFinset_card,
      Submodule.FG.generators_ncard (maximalIdeal R).fg_of_isNoetherianRing]
  have regl := isRegular_of_span_eq_maximalIdeal R l eq len
  have : (koszulAlgebra R).ExactAt 1 :=
    koszulComplex.exactAt_of_isRegular l regl 1 Nat.one_ne_zero
  rw [HomologicalComplex.exactAt_iff_isZero_homology, ModuleCat.isZero_iff_subsingleton] at this
  simpa [Epsilon1, Module.finrank_eq_zero_iff_of_free]

theorem IsRegularLocalRing.isCompleteIntersectionLocalRing [IsRegularLocalRing R] :
    IsCompleteIntersectionLocalRing R := by
  simp [isCompleteIntersectionLocalRing_def, IsRegularLocalRing.epsilon1_eq_zero,
    (isRegularLocalRing_iff R).mp ‹_›]

lemma IsRegularLocalRing.isGorensteinLocalRing [IsRegularLocalRing R] :
    IsGorensteinLocalRing R := by
  rw [isGorensteinLocalRing_def]
  have : globalDimension.{u} R ≠ ⊤ := by
    simpa [IsRegularLocalRing.globalDimension_eq_ringKrullDim] using ringKrullDim_ne_top
  apply ne_top_of_le_ne_top this
  rw [globalDimension_eq_sup_injectiveDimension]
  exact le_iSup _ _

theorem IsCompleteIntersectionLocalRing.isGorensteinLocalRing
    [IsCompleteIntersectionLocalRing R] : IsGorensteinLocalRing R := by
  obtain ⟨S, _, _, f, rs, surj, ker, reg⟩ := (isCompleteIntersectionLocalRing_iff R).mp ‹_›
  have : IsGorensteinLocalRing (S ⧸ Ideal.ofList rs) :=
    (quotient_regular_isGorenstein_iff_isGorenstein S rs reg).mp
      (IsRegularLocalRing.isGorensteinLocalRing S)
  let R' := AdicCompletion (maximalIdeal R) R
  let e : S ⧸ Ideal.ofList rs ≃+* R' :=
    (Ideal.quotEquivOfEq ker.symm).trans (f.quotientKerEquivOfSurjective surj)
  rw [IsGorensteinLocalRing.iff_adicCompletion]
  exact IsGorensteinLocalRing.of_ringEquiv e
