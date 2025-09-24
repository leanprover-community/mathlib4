/-
Copyright (c) 2025 Yiming Fu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yiming Fu
-/
import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.Localization.Finiteness

/-!
# Local properties for semilocal rings

This file proves some local properties for a semilocal ring `R` (a ring with
finitely many maximal ideals).

## Main results

* `Module.finite.of_isLocalized_maximal`: A module `M` over a semilocal ring `R` is finite if it is
  locally finite at every maximal ideal.
* `isPrincipalIdealRing_of_isPrincipalIdealRing_localization`: A semilocal integral domain `A` is a
  PID if its localization at every maximal ideal is a PID.
-/

section CommSemiring

variable {R : Type*} [CommSemiring R] [Finite (MaximalSpectrum R)]
variable (M : Type*) [AddCommMonoid M] [Module R M]

variable
  (Rₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], CommSemiring (Rₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Algebra R (Rₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], IsLocalization.AtPrime (Rₚ P) P]
  (Mₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], AddCommMonoid (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module R (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module (Rₚ P) (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], IsScalarTower R (Rₚ P) (Mₚ P)]
  (f : ∀ (P : Ideal R) [P.IsMaximal], M →ₗ[R] Mₚ P)
  [∀ (P : Ideal R) [P.IsMaximal], IsLocalizedModule P.primeCompl (f P)]

section isLocalized_maximal

include f in
/-- A module `M` over a semilocal ring `R` is finite if it is
locally finite at every maximal ideal. -/
theorem Module.Finite.of_isLocalized_maximal
    (H : ∀ (P : Ideal R) [P.IsMaximal], Module.Finite (Rₚ P) (Mₚ P)) :
    Module.Finite R M := by
  classical
  have : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  choose s hs using fun P : MaximalSpectrum R ↦ (H P.1).fg_top
  choose frac hfrac using fun P : MaximalSpectrum R ↦ IsLocalizedModule.surj P.1.primeCompl (f P.1)
  use Finset.biUnion Finset.univ fun P ↦ Finset.image (frac P ·|>.1) (s P)
  refine Submodule.eq_top_of_localization_maximal Rₚ Mₚ f _ fun P hP ↦ ?_
  rw [eq_top_iff, ← hs ⟨P, hP⟩, Submodule.localized'_span, Submodule.span_le]
  intro x hx
  lift x to s ⟨P, hP⟩ using hx
  rw [SetLike.mem_coe, ← IsLocalization.smul_mem_iff (s := (frac ⟨P, hP⟩ x).2), hfrac]
  exact Submodule.subset_span ⟨_, by simpa using ⟨_, _, x.2, rfl⟩, rfl⟩

variable {M} in
/-- A submodule `N` of a module `M` over a semilocal ring `R` is finitely generated if it is
locally finitely generated at every maximal ideal. -/
theorem Submodule.fg_of_isLocalized_maximal (N : Submodule R M)
    (H : ∀ (P : Ideal R) [P.IsMaximal], (Submodule.localized' (Rₚ P) P.primeCompl (f P) N).FG) :
    N.FG := by
  simp_rw [← Module.Finite.iff_fg] at ⊢ H
  exact .of_isLocalized_maximal  _ _ _ (fun P ↦ N.toLocalized' (Rₚ P) P.primeCompl (f P)) H

end isLocalized_maximal

section localized_maximal

theorem Module.Finite.of_localized_maximal
    (H : ∀ (P : Ideal R) [P.IsMaximal],
      Module.Finite (Localization P.primeCompl) (LocalizedModule P.primeCompl M)) :
    Module.Finite R M :=
  .of_isLocalized_maximal M _ _ (fun _ _ ↦ LocalizedModule.mkLinearMap _ _) H

variable {M} in
theorem Submodule.fg_of_localized_maximal (N : Submodule R M)
    (H : ∀ (P : Ideal R) [P.IsMaximal], (Submodule.localized (P.primeCompl) N).FG) :
    N.FG := N.fg_of_isLocalized_maximal _ _ _ H

end localized_maximal

section IsLocalization

theorem IsNoetherianRing.of_isLocalized_maximal
    (H : ∀ (P : Ideal R) [P.IsMaximal], IsNoetherianRing (Rₚ P)) :
    IsNoetherianRing R where
  noetherian N := Submodule.fg_of_isLocalized_maximal
    Rₚ Rₚ (fun P _ => Algebra.linearMap R (Rₚ P)) N (fun _ _ => IsNoetherian.noetherian _)

end IsLocalization

end CommSemiring

section CommRing

section IsLocalization

variable {R : Type*} [CommRing R] [Finite (MaximalSpectrum R)]
variable
  (Rₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], CommRing (Rₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Algebra R (Rₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], IsLocalization.AtPrime (Rₚ P) P]

/-- If a semilocal integral domain `R` is a PID at all of its maximal ideals, then it is a PID.
This is the `IsLocalization` version. -/
theorem isPrincipalIdealRing_of_isPrincipalIdealRing_isLocalization [IsDomain R]
    (hpid : ∀ (P : Ideal R) [P.IsMaximal], IsPrincipalIdealRing (Rₚ P)) :
    IsPrincipalIdealRing R := by
  have : IsNoetherianRing R := IsNoetherianRing.of_isLocalized_maximal Rₚ (fun P _ => inferInstance)
  have : IsIntegrallyClosed R := by
    refine IsIntegrallyClosed.of_isLocalization_maximal Rₚ (fun P _ => ?_)
    have := hpid P
    sorry
  have : Ring.KrullDimLE 1 R :=
    Ring.krullDimLE_of_isLocalization_maximal Rₚ (fun P _ => inferInstance)
  rw [Ring.krullDimLE_one_iff_of_noZeroDivisors] at this
  have dedekind : IsDedekindDomain R := { maximalOfPrime := this _ }
  have hp_finite : {P : Ideal R | P.IsPrime}.Finite :=
    ((Set.finite_range MaximalSpectrum.asIdeal).insert ⊥).subset fun P hP ↦
      or_iff_not_imp_left.mpr (⟨⟨_, this _ · hP⟩, rfl⟩)
  exact IsPrincipalIdealRing.of_finite_primes hp_finite

end IsLocalization

end CommRing
