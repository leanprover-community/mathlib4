/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.IntegralDomain

/-! # Rings with finite quotients

A commutative ring is said to have finite quotients if, for any nonzero ideal `I` of `R`, the
quotient `R ⧸ I` is finite.

This class and some of its properties are found elsewhere, but we collect here results that need
heavy imports or do not fit elsewhere.

-/

@[expose] public section

namespace Ring

variable {R : Type*} [CommRing R]

theorem HasFiniteQuotients.MaximalOfPrime [HasFiniteQuotients R] {P : Ideal R} [P.IsPrime]
    (hp : P ≠ ⊥) : P.IsMaximal :=
  have : IsDomain (R ⧸ P) := Ideal.Quotient.isDomain P
  have : Finite (R ⧸ P) := finiteQuotient hp
  Ideal.Quotient.maximal_of_isField P <| Finite.isField_of_domain (R ⧸ P)

instance [HasFiniteQuotients R] : DimensionLEOne R :=
  ⟨fun h _ ↦ HasFiniteQuotients.MaximalOfPrime h⟩

instance [HasFiniteQuotients R] : IsNoetherianRing R := by
  refine (isNoetherianRing_iff_ideal_fg R).mpr fun I ↦ ?_
  by_cases hI : I = 0
  · exact hI ▸ Submodule.fg_bot
  obtain ⟨x, hx₁, hx₂⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  refine Submodule.fg_of_fg_map_of_fg_inf_ker (Submodule.mkQ (Ideal.span {x})) ?_ ?_
  · have := HasFiniteQuotients.finiteQuotient (I := Ideal.span {x}) (by simp [hx₂])
    exact Submodule.FG.of_finite
  · rw [Submodule.ker_mkQ, inf_eq_right.mpr ((Ideal.span_singleton_le_iff_mem I).mpr hx₁)]
    exact Ideal.fg_span {x}

end Ring
