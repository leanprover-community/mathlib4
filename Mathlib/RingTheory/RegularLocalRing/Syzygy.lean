/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.KrullDimension.PID
public import Mathlib.RingTheory.RegularLocalRing.GlobalDimension
public import Mathlib.RingTheory.RegularLocalRing.Polynomial

/-!

# Hilbert's Syzygy Theorem

-/

@[expose] public section

universe u v

variable (R : Type u) [CommRing R]

open IsLocalRing

theorem Hilberts_Syzygy (k : Type u) [Field k] [Small.{v, u} k] {ι : Type*} [Finite ι] :
    globalDimension.{v} (MvPolynomial ι k) = Nat.card ι := by
  have : IsRegularRing (MvPolynomial ι k) := MvPolynomial.isRegularRing_of_isRegularRing k
  simp [IsRegularRing.globalDimension_eq_ringKrullDim,
    MvPolynomial.ringKrullDim_of_isNoetherianRing]
