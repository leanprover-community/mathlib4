/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.IntegralDomain

/-! # Rings with finite quotients

A commutative ring is said to have finite quotients if, for any nonzero ideal `I` of `R`, the
quotient `R ⧸ I` is finite.

## Main results
- `Ring.HasFiniteQuotients.instDimensionLEOne`: A ring with finite quotients has dimension `≤ 1`.
- `Ring.HasFiniteQuotients.instIsNoetherianRing` : A ring with finite quotients is noetherian.
- `Ring.HasFiniteQuotients.of_module_finite`: Assume that `R` a finite quotients and that `S` is
a domain and a finite `R`-module. Then `S` has finite quotients.
- `Ring.HasFiniteQuotients.instOfIsDomainOfFiniteInt`: A domain that is also a finite `ℤ`-module
has finite quotients.

-/

@[expose] public section

variable {R : Type*} [CommRing R]

/--
A ring `R` has finite quotients if the quotient `R ⧸ I` is finite for all nonzero ideals of `R`.
-/
class Ring.HasFiniteQuotients (R : Type*) [CommRing R] : Prop where
  finiteQuotient {I : Ideal R} : I ≠ ⊥ → Finite (R ⧸ I)

namespace Ring.HasFiniteQuotients

/-- A finite ring has finite quotients. -/
instance (R : Type*) [CommRing R] [Finite R] : Ring.HasFiniteQuotients R :=
  ⟨fun _ ↦ Quotient.finite _⟩

/-- A nonzero prime ideal of a ring with finite quotients is maximal. -/
theorem maximalOfPrime [HasFiniteQuotients R] {P : Ideal R} [P.IsPrime] (hp : P ≠ ⊥) :
    P.IsMaximal :=
  have : Finite (R ⧸ P) := finiteQuotient hp
  Ideal.Quotient.maximal_of_isField P <| Finite.isField_of_domain (R ⧸ P)

/-- A ring with finite quotients has dimension `≤ 1`. -/
instance [HasFiniteQuotients R] : DimensionLEOne R :=
  ⟨fun h _ ↦ maximalOfPrime h⟩

/-- A ring with finite quotients is noetherian. -/
instance [HasFiniteQuotients R] : IsNoetherianRing R := by
  refine (isNoetherianRing_iff_ideal_fg R).mpr fun I ↦ ?_
  by_cases hI : I = 0
  · exact hI ▸ Submodule.fg_bot
  obtain ⟨x, hx₁, hx₂⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  refine Submodule.fg_of_fg_map_of_fg_inf_ker (Submodule.mkQ (Ideal.span {x})) ?_ ?_
  · have := finiteQuotient (I := Ideal.span {x}) (by simp [hx₂])
    exact Submodule.FG.of_finite
  · rw [Submodule.ker_mkQ, inf_eq_right.mpr ((Ideal.span_singleton_le_iff_mem I).mpr hx₁)]
    exact Submodule.fg_span_singleton x

variable (R) in
/--
Assume that `R` a finite quotients and that `S` is a domain and a finite `R`-module. Then
`S` has finite quotients.
-/
theorem of_module_finite [h : HasFiniteQuotients R] (S : Type*) [CommRing S] [IsDomain S]
    [Algebra R S] [Module.Finite R S] :
    HasFiniteQuotients S := ⟨fun {I} hI ↦ by
  classical
  obtain hR | hR := subsingleton_or_nontrivial R
  · have : Finite S := Module.finite_of_finite R
    exact Quotient.finite _
  let J : Ideal R := Ideal.under R I
  have : Finite (R ⧸ J) := h.finiteQuotient <| Ideal.under_ne_bot R hI
  have : Module.Finite (R ⧸ J) (S ⧸ I) := Module.Finite.of_restrictScalars_finite R (R ⧸ J) (S ⧸ I)
  exact Module.finite_of_finite (R ⧸ J)⟩

/-- The ring `ℤ` has finite quotients. -/
instance : HasFiniteQuotients ℤ := ⟨fun {I} hI ↦ by
  obtain ⟨n, rfl⟩ := Submodule.IsPrincipal.principal I
  have : NeZero n := ⟨by simpa using hI⟩
  exact inferInstanceAs <| Finite (ℤ ⧸ Ideal.span {n})⟩

/-- A domain that is also a finite `ℤ`-module has finite quotients. -/
instance [IsDomain R] [Module.Finite ℤ R] :
    HasFiniteQuotients R := of_module_finite ℤ R

end Ring.HasFiniteQuotients
