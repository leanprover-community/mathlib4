/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Order.Northcott
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Defs

/-! # `Northcott` instances for rings with finite quotients

For a ring with finite quotients, there are only finitely many ideals of bounded norm
(`Ring.HasFiniteQuotients.finite_cardQuot_le`). This file records the resulting `Northcott`
instances for `Submodule.cardQuot` and `Ideal.absNorm`.
-/

public section

namespace Ring.HasFiniteQuotients

variable {R : Type*} [CommRing R] [HasFiniteQuotients R]

instance : Northcott fun p : Ideal R ↦ p.cardQuot :=
  ⟨Ring.HasFiniteQuotients.finite_cardQuot_le⟩

instance [IsDedekindDomain R] [Infinite R] :
    Northcott fun p : IsDedekindDomain.HeightOneSpectrum R ↦ p.asIdeal.absNorm :=
  ⟨Ring.HasFiniteQuotients.finite_absNorm_heightOneSpectrum_le⟩

end Ring.HasFiniteQuotients
