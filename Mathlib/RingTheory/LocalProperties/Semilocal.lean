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
theorem Module.finite.of_isLocalized_maximal
    (H : ∀ (P : Ideal R) [P.IsMaximal], Module.Finite (Rₚ P) (Mₚ P)) :
    Module.Finite R M := by
  classical
  let : Fintype ({ P : Ideal R | P.IsMaximal }) := by
    rw [← MaximalSpectrum.range_asIdeal]
    exact Fintype.ofFinite (Set.range MaximalSpectrum.asIdeal)
  constructor
  let {P : { P : Ideal R | P.IsMaximal }} : P.1.IsMaximal := P.2
  choose s₁ s₂ using (fun P : { P : Ideal R | P.IsMaximal } ↦ (H P.1).1)
  let getNum (P : { P : Ideal R | P.IsMaximal }) (x : Mₚ P) :=
    (IsLocalizedModule.surj P.1.primeCompl (f P.1) x).choose.1
  let sf := fun P : { P : Ideal R | P.IsMaximal } ↦ Finset.image (getNum P) (s₁ P)
  use Finset.biUnion (Finset.univ) sf
  let N : Submodule R M := Submodule.span R (Finset.univ.biUnion sf)
  refine Submodule.eq_top_of_localization_maximal Rₚ Mₚ f _ (fun P hP ↦ ?_)
  rw [← top_le_iff, ← s₂ ⟨P, hP⟩, Submodule.localized'_span]
  refine Submodule.span_le.2 fun x hx ↦ ?_
  lift x to s₁ ⟨P, hP⟩ using hx
  rw [SetLike.mem_coe]
  let Num := getNum ⟨P, hP⟩ x
  let denom := (IsLocalizedModule.surj P.primeCompl (f P) x).choose.2
  have h : denom • x = f P Num := (IsLocalizedModule.surj P.primeCompl (f P) x).choose_spec
  rw [← IsLocalization.smul_mem_iff (s := denom), h]
  refine Submodule.mem_span.mpr fun p a => a ?_
  simp only [Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true, Set.mem_image,
    Set.mem_iUnion, Finset.mem_coe, Finset.mem_image, sf]
  exact ⟨Num, ⟨⟨P, hP⟩, ⟨x, ⟨x.2, rfl⟩⟩⟩, rfl⟩

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
  exact Module.finite.of_isLocalized_maximal  _ _ _ fN H

end isLocalized_maximal

section localized_maximal

theorem Module.finite.of_localized_maximal
    (H : ∀ (P : Ideal R) [P.IsMaximal],
      Module.Finite (Localization P.primeCompl) (LocalizedModule P.primeCompl M)) :
    Module.Finite R M :=
  Module.finite.of_isLocalized_maximal  M _ _
    (fun _ _ ↦ LocalizedModule.mkLinearMap _ _) H

variable {M} in
theorem Submodule.fg_of_localized_maximal (N : Submodule R M)
    (H : ∀ (P : Ideal R) [P.IsMaximal], (Submodule.localized (P.primeCompl) N).FG) :
    N.FG := Submodule.fg_of_isLocalized_maximal  _ _ _ N H

end localized_maximal

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
