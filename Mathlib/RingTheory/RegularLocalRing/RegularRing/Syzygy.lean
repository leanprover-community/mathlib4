/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.KrullDimension.PID
public import Mathlib.RingTheory.RegularLocalRing.RegularRing.GlobalDimension
public import Mathlib.RingTheory.RegularLocalRing.RegularRing.Polynomial

/-!

# Hilbert's Syzygy Theorem

-/

@[expose] public section

universe u v

variable (R : Type u) [CommRing R]

open IsLocalRing

set_option backward.isDefEq.respectTransparency false in
lemma IsRegularRing.of_isField (h : IsField R) : IsRegularRing R := by
  let _ : Field R := h.toField
  refine (isRegularRing_iff R).mpr (fun p hp ↦ ?_)
  have nmem : 0 ∉ p.primeCompl := by simp
  exact IsRegularLocalRing.of_ringEquiv (RingEquiv.ofBijective
    (algebraMap R (Localization.AtPrime p)) (Field.localization_map_bijective nmem))

lemma IsRegularLocalRing.of_isRegularRing [IsLocalRing R] [IsRegularRing R] :
    IsRegularLocalRing R := by
  have := (isRegularRing_iff R).mp ‹_› (maximalIdeal R) (Ideal.IsMaximal.isPrime' _)
  let e : R ≃ₐ[R] (Localization.AtPrime (maximalIdeal R)) :=
    IsLocalization.atUnits R (maximalIdeal R).primeCompl (fun x ↦ by simpa using fun a ↦ a)
  exact IsRegularLocalRing.of_ringEquiv e.toRingEquiv.symm

set_option backward.isDefEq.respectTransparency false in
theorem Hilberts_Syzygy (k : Type u) [Field k] [Small.{v, u} k] {ι : Type*} [Finite ι] :
    globalDimension.{v} (MvPolynomial ι k) = Nat.card ι := by
  let _ : IsRegularRing k := IsRegularRing.of_isField k (Field.toIsField k)
  let _ : IsRegularRing (MvPolynomial ι k) := MvPolynomial.isRegularRing_of_isRegularRing k
  simp [IsRegularRing.globalDimension_eq_ringKrullDim,
    MvPolynomial.ringKrullDim_of_isNoetherianRing]
