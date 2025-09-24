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

variable {R : Type*} [CommSemiring R] [Finite (MaximalSpectrum R)]
variable (M : Type*) [AddCommMonoid M] [Module R M]

lemma Ring.krullDimLE_one_of_localization_maximal {A : Type*} [CommRing A] {n : ℕ}
    (h : ∀ (P : Ideal A) [P.IsMaximal], Ring.KrullDimLE n (Localization P.primeCompl)) :
    Ring.KrullDimLE n A := by
  by_cases hA : Nontrivial A
  · simp_rw [Ring.krullDimLE_iff] at h ⊢
    rw [← Ideal.sup_primeHeight_of_maximal_eq_ringKrullDim]
    refine (WithBot.coe_le_coe).2 (iSup₂_le_iff.mpr fun P hP ↦ ?_)
    rw [← Ideal.height_eq_primeHeight, ← WithBot.coe_le_coe]
    rw [← IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization P.primeCompl)]
    exact h P
  · rw [not_nontrivial_iff_subsingleton] at hA
    simp only [Ring.krullDimLE_iff, ringKrullDim_eq_bot_of_subsingleton, bot_le]

section isLocalized_maximal

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
  let fN : ∀ (P : Ideal R) [P.IsMaximal], ↥N →ₗ[R]
    Submodule.localized' (Rₚ P) P.primeCompl (f P) N :=
    fun P _ => N.toLocalized' (Rₚ P) P.primeCompl (f P)
  exact Module.Finite.of_isLocalized_maximal  _ _ _ fN H

end isLocalized_maximal

section localized_maximal

theorem Module.Finite.of_localized_maximal
    (H : ∀ (P : Ideal R) [P.IsMaximal],
      Module.Finite (Localization P.primeCompl) (LocalizedModule P.primeCompl M)) :
    Module.Finite R M :=
  Module.Finite.of_isLocalized_maximal  M _ _
    (fun _ _ ↦ LocalizedModule.mkLinearMap _ _) H

variable {M} in
theorem Submodule.fg_of_localized_maximal (N : Submodule R M)
    (H : ∀ (P : Ideal R) [P.IsMaximal], (Submodule.localized (P.primeCompl) N).FG) :
    N.FG := Submodule.fg_of_isLocalized_maximal  _ _ _ N H

end localized_maximal

variable
  (Rₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], CommSemiring (Rₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Algebra R (Rₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], IsLocalization.AtPrime (Rₚ P) P]
/-- If a semilocal integral domain satisfies that it localized at all
maximal ideals is a PID, then itself is a PID. -/
theorem isPrincipalIdealRing_of_isPrincipalIdealRing_localization
    (A : Type*) [CommRing A] [IsDomain A] [Finite (MaximalSpectrum A)]
    (hpid : ∀ (P : Ideal A) [P.IsMaximal], IsPrincipalIdealRing (Localization P.primeCompl)) :
    IsPrincipalIdealRing A := by
  have : IsNoetherianRing A := by
    constructor
    intro N
    refine Submodule.fg_of_localized_maximal N (fun P hP => ?_)
    exact IsNoetherian.noetherian (Submodule.localized P.primeCompl N)
  have : IsIntegrallyClosed A := by
    refine IsIntegrallyClosed.of_localization_maximal (fun P _ hP => ?_)
    let p : MaximalSpectrum A := ⟨P, hP⟩
    change IsIntegrallyClosed (Localization p.1.primeCompl)
    infer_instance
  have : Ring.KrullDimLE 1 A :=
    Ring.krullDimLE_one_of_localization_maximal (fun _ _ => by infer_instance)
  rw [Ring.krullDimLE_one_iff_of_noZeroDivisors] at this
  have : IsDedekindDomain A := {maximalOfPrime := this _}
  have hp_sub : {P : Ideal A | P.IsPrime} ⊆ {P : Ideal A | P.IsMaximal} ∪ {⊥} := by
    simp only [Set.union_singleton]
    intro P hP
    obtain rfl | hbot := eq_or_ne P ⊥
    · simp
    · simp only [Set.mem_insert_iff, hbot, Set.mem_setOf_eq, false_or]
      exact this.maximalOfPrime hbot hP
  have hp_finite : {P : Ideal A | P.IsPrime}.Finite := by
    refine Set.Finite.subset (Set.Finite.union ?_ (Set.finite_singleton ⊥)) hp_sub
    rw [← MaximalSpectrum.range_asIdeal]
    exact Set.finite_range MaximalSpectrum.asIdeal
  exact IsPrincipalIdealRing.of_finite_primes hp_finite
