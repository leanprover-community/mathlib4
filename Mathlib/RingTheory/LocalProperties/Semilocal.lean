/-
Copyright (c) 2025 Yiming Fu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yiming Fu
-/
module

public import Mathlib.RingTheory.KrullDimension.PID

import Mathlib.RingTheory.DedekindDomain.PID

/-!
# Local properties for semilocal rings

This file proves some local properties for a semilocal ring `R` (a ring with
finitely many maximal ideals).

## Main results

* `Module.Finite.of_isLocalized_maximal`: A module `M` over a semilocal ring `R` is finite if its
  localization at every maximal ideal is finite.
* `IsNoetherianRing.of_isLocalization_maximal`: A semilocal ring `R` is Noetherian if its
  localization at every maximal ideal is a Noetherian ring.
* `isPrincipalIdealRing_of_isPrincipalIdealRing_isLocalization_maximal`: A semilocal
  integral domain `A` is a PID if its localization at every maximal ideal is a PID.
* `IsCoprime.exists_isUnit_add_mul`: A semilocal ring has stable range one.
-/

public section

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

section IsLocalized

include f in
/-- A module `M` over a semilocal ring `R` is finite if
its localization at every maximal ideal is finite. -/
theorem Module.Finite.of_isLocalized_maximal
    (H : ∀ (P : Ideal R) [P.IsMaximal], Module.Finite (Rₚ P) (Mₚ P)) :
    Module.Finite R M := by
  classical
  have : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  choose s hs using fun P : MaximalSpectrum R ↦ (H P.1).fg_top
  choose frac hfrac using fun P : MaximalSpectrum R ↦ IsLocalizedModule.surj P.1.primeCompl (f P.1)
  use Finset.biUnion Finset.univ fun P ↦ Finset.image (frac P · |>.1) (s P)
  refine Submodule.eq_top_of_localization_maximal Rₚ Mₚ f _ fun P hP ↦ ?_
  rw [eq_top_iff, ← hs ⟨P, hP⟩, Submodule.localized'_span, Submodule.span_le]
  intro x hx
  lift x to s ⟨P, hP⟩ using hx
  rw [SetLike.mem_coe, ← IsLocalization.smul_mem_iff (s := (frac ⟨P, hP⟩ x).2), hfrac]
  exact Submodule.subset_span ⟨_, by simpa using ⟨_, _, x.2, rfl⟩, rfl⟩

variable {M} in
/-- A submodule `N` of a module `M` over a semilocal ring `R` is finitely generated if
its localization at every maximal ideal is finitely generated. -/
theorem Submodule.fg_of_isLocalized_maximal (N : Submodule R M)
    (H : ∀ (P : Ideal R) [P.IsMaximal], (Submodule.localized' (Rₚ P) P.primeCompl (f P) N).FG) :
    N.FG := by
  simp_rw [← Module.Finite.iff_fg] at ⊢ H
  exact .of_isLocalized_maximal _ _ _ (fun P ↦ N.toLocalized' (Rₚ P) P.primeCompl (f P)) H

end IsLocalized

section Localized

theorem Module.Finite.of_localized_maximal
    (H : ∀ (P : Ideal R) [P.IsMaximal],
      Module.Finite (Localization P.primeCompl) (LocalizedModule P.primeCompl M)) :
    Module.Finite R M :=
  .of_isLocalized_maximal M _ _ (fun _ _ ↦ LocalizedModule.mkLinearMap _ _) H

variable {M} in
theorem Submodule.fg_of_localized_maximal (N : Submodule R M)
    (H : ∀ (P : Ideal R) [P.IsMaximal], (N.localized P.primeCompl).FG) :
    N.FG := N.fg_of_isLocalized_maximal _ _ _ H

end Localized

section IsLocalization

/-- A semilocal ring `R` is Noetherian if
its localization at every maximal ideal is a Noetherian ring. -/
theorem IsNoetherianRing.of_isLocalization_maximal
    (H : ∀ (P : Ideal R) [P.IsMaximal], IsNoetherianRing (Rₚ P)) :
    IsNoetherianRing R where
  noetherian N := Submodule.fg_of_isLocalized_maximal
    Rₚ Rₚ (fun P _ => Algebra.linearMap R (Rₚ P)) N fun _ _ ↦ IsNoetherian.noetherian _

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

/-- A semilocal integral domain `A` is a PID if its localization at every maximal ideal is a PID. -/
theorem isPrincipalIdealRing_of_isPrincipalIdealRing_isLocalization_maximal [IsDomain R]
    (hpid : ∀ (P : Ideal R) [P.IsMaximal], IsPrincipalIdealRing (Rₚ P)) :
    IsPrincipalIdealRing R := by
  have : IsNoetherianRing R :=
    IsNoetherianRing.of_isLocalization_maximal Rₚ fun P _ => inferInstance
  have : IsIntegrallyClosed R := by
    refine IsIntegrallyClosed.of_isLocalization_maximal Rₚ fun P hP => ?_
    have : IsDomain (Rₚ P) := IsLocalization.isDomain_of_atPrime (Rₚ P) P
    infer_instance
  have : Ring.KrullDimLE 1 R :=
    Ring.krullDimLE_of_isLocalization_maximal Rₚ fun P _ => inferInstance
  rw [Ring.krullDimLE_one_iff_of_noZeroDivisors] at this
  have dedekind : IsDedekindDomain R := { maximalOfPrime := this _ }
  have hp_finite : {P : Ideal R | P.IsMaximal}.Finite := by
    rw [← MaximalSpectrum.range_asIdeal]
    exact Set.finite_range MaximalSpectrum.asIdeal
  exact IsPrincipalIdealRing.of_finite_maximals hp_finite

end IsLocalization

variable {R : Type*} [CommRing R] [Finite (MaximalSpectrum R)]

/-- A semilocal ring has stable range one: if `a` and `b` are coprime, then `a + t * b` is a
unit for some `t`. This is due to Bass, see [Bass, *K-theory and stable algebra*][bass1964]. -/
theorem IsCoprime.exists_isUnit_add_mul {a b : R} (h : IsCoprime a b) :
    ∃ t : R, IsUnit (a + t * b) := by
  classical
  have hcop : Pairwise (Function.onFun IsCoprime fun m : MaximalSpectrum R ↦ m.asIdeal) :=
    fun m n hmn ↦ Ideal.isCoprime_of_isMaximal fun e ↦ hmn (MaximalSpectrum.ext e)
  -- modulo `m`, take `t = 0` if `b ∈ m`, and `t = b⁻¹ (1 - a)` otherwise
  let x : MaximalSpectrum R → R := fun m ↦
    if hb : b ∈ m.asIdeal then 0 else (m.isMaximal.exists_inv hb).choose * (1 - a)
  obtain ⟨t, ht⟩ := Ideal.exists_forall_sub_mem_ideal hcop x
  refine ⟨t, by_contra fun hu ↦ ?_⟩
  obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits hu
  have htm := ht ⟨m, hm⟩
  obtain ⟨u, v, huv⟩ := h
  refine hm.ne_top <| (Ideal.eq_top_iff_one _).2 ?_
  by_cases hb : b ∈ m
  · simp only [x, hb, ↓reduceDIte, sub_zero] at htm
    have ha : a ∈ m := by simpa using m.sub_mem hmem (m.mul_mem_left t hb)
    rw [← huv]
    exact m.add_mem (m.mul_mem_left _ ha) (m.mul_mem_left _ hb)
  · obtain ⟨k, hk, hy⟩ := (hm.exists_inv hb).choose_spec
    simp only [x, hb, ↓reduceDIte] at htm
    have e : (1 : R) = (a + t * b) - (t - (hm.exists_inv hb).choose * (1 - a)) * b
        + (1 - a) * k := by
      linear_combination (-(1 - a)) * hy
    rw [e]
    exact m.add_mem (m.sub_mem hmem (m.mul_mem_right _ htm)) (m.mul_mem_left _ hk)

end CommRing
