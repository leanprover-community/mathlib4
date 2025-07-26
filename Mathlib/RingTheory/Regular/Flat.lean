/-
Copyright (c) 2025 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu, Nailin Guan
-/
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Regular.RegularSequence

/-!
# `RingTheory.Sequence.IsWeaklyRegular` is stable under flat base change

## Main results
* `RingTheory.Sequence.IsWeaklyRegular.of_flat_isBaseChange`: Let `R` be a commutative ring,
  `M` be an `R`-module, `S` be a flat `R`-algebra, `N` be the base change of `M` to `S`.
  If `[r₁, …, rₙ]` is a weakly regular `M`-sequence, then its image in `N` is a weakly regular
  `N`-sequence.
-/

open RingTheory.Sequence Module

section Flat

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S] [Flat R S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- Let `R` be a commutative ring, `M` be an `R`-module, `S` be a flat `R`-algebra, `N` be the base
  change of `M` to `S`. If `[r₁, …, rₙ]` is a weakly regular `M`-sequence, then its image in `N` is
  a weakly regular `N`-sequence. -/
theorem RingTheory.Sequence.IsWeaklyRegular.of_flat_of_isBaseChange
    {f : M →ₗ[R] N} (hf : IsBaseChange S f) {rs : List R} (reg : IsWeaklyRegular M rs) :
    IsWeaklyRegular N (rs.map (algebraMap R S)) := by
  induction rs generalizing M N with
  | nil => simp
  | cons x _ ih =>
    simp only [List.map_cons, isWeaklyRegular_cons_iff] at reg ⊢
    have e := (QuotSMulTop.algebraMapTensorEquivTensorQuotSMulTop x M S).symm ≪≫ₗ
      QuotSMulTop.congr ((algebraMap R S) x) hf.equiv
    have hg : IsBaseChange S <|
        e.toLinearMap.restrictScalars R ∘ₗ TensorProduct.mk R S (QuotSMulTop x M) 1 :=
      IsBaseChange.of_equiv e (fun _ ↦ by simp)
    exact ⟨reg.1.of_flat_of_isBaseChange hf, ih hg reg.2⟩

theorem RingTheory.Sequence.IsWeaklyRegular.of_flat {rs : List R} (reg : IsWeaklyRegular R rs) :
    IsWeaklyRegular S (rs.map (algebraMap R S)) :=
  reg.of_flat_of_isBaseChange (IsBaseChange.linearMap R S)

end Flat

section FaithfullyFlat

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S] [FaithfullyFlat R S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- Let `R` be a commutative ring, `M` be an `R`-module, `S` be a faithfully flat `R`-algebra,
  `N` be the base change of `M` to `S`. If `[r₁, …, rₙ]` is a regular `M`-sequence, then its image
  in `N` is a regular `N`-sequence. -/
theorem RingTheory.Sequence.IsRegular.of_faithfullyFlat_of_isBaseChange
    {f : M →ₗ[R] N} (hf : IsBaseChange S f) {rs : List R} (reg : IsRegular M rs) :
    IsRegular N (rs.map (algebraMap R S)) := by
  refine ⟨reg.1.of_flat_of_isBaseChange hf, ?_⟩
  rw [← Ideal.map_ofList]
  exact (FaithfullyFlat.smul_top_ne_top_of_isBaseChange R M hf reg.2.symm).symm

theorem RingTheory.Sequence.IsRegular.of_faithfullyFlat {rs : List R} (reg : IsRegular R rs) :
    IsRegular S (rs.map (algebraMap R S)) :=
  reg.of_faithfullyFlat_of_isBaseChange (IsBaseChange.linearMap R S)

end FaithfullyFlat

section IsLocalizedModule

variable {R : Type*} [CommRing R] (S : Submonoid R) (R' : Type*) [CommRing R'] [Algebra R R']
  [IsLocalization S R']

include S

theorem RingTheory.Sequence.IsWeaklyRegular.of_isLocalizedModule
    {M : Type*} [AddCommGroup M] [Module R M] {M' : Type*} [AddCommGroup M'] [Module R M']
    [Module R' M'] [IsScalarTower R R' M'] (f : M →ₗ[R] M') [IsLocalizedModule S f] {rs : List R}
    (reg : IsWeaklyRegular M rs) : IsWeaklyRegular M' (rs.map (algebraMap R R')) :=
  have : Flat R R' := IsLocalization.flat R' S
  reg.of_flat_of_isBaseChange (IsLocalizedModule.isBaseChange S R' f)

theorem RingTheory.Sequence.IsWeaklyRegular.of_isLocalization {rs : List R}
    (reg : IsWeaklyRegular R rs) : IsWeaklyRegular R' (rs.map (algebraMap R R')) :=
  reg.of_isLocalizedModule S R' (Algebra.linearMap R R')

end IsLocalizedModule

section AtPrime

variable {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime]
  (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p]

theorem RingTheory.Sequence.IsWeaklyRegular.isRegular_of_isLocalizedModule_of_mem_prime
    {M Mₚ : Type*} [AddCommGroup M] [Module R M] [Nontrivial Mₚ] [AddCommGroup Mₚ] [Module Rₚ Mₚ]
    [Module.Finite Rₚ Mₚ] [Module R Mₚ] [IsScalarTower R Rₚ Mₚ]
    (f : M →ₗ[R] Mₚ) [IsLocalizedModule.AtPrime p f] {rs : List R} (reg : IsWeaklyRegular M rs)
    (mem : ∀ r ∈ rs, r ∈ p) : IsRegular Mₚ (rs.map (algebraMap R Rₚ)) := by
  have : IsLocalRing Rₚ := IsLocalization.AtPrime.isLocalRing Rₚ p
  refine (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal (fun _ hr ↦ ?_)).mpr <|
    reg.of_isLocalizedModule p.primeCompl Rₚ f
  rcases List.mem_map.mp hr with ⟨r, hr, eq⟩
  simpa only [← eq, IsLocalization.AtPrime.to_map_mem_maximal_iff Rₚ p] using mem r hr

theorem RingTheory.Sequence.IsWeaklyRegular.isRegular_of_isLocalization_of_mem_prime
    {rs : List R} (reg : IsWeaklyRegular R rs) (mem : ∀ r ∈ rs, r ∈ p) :
    IsRegular Rₚ (rs.map (algebraMap R Rₚ)) :=
  have : Nontrivial Rₚ := IsLocalization.AtPrime.Nontrivial Rₚ p
  reg.isRegular_of_isLocalizedModule_of_mem_prime p Rₚ (Algebra.linearMap R Rₚ) mem

end AtPrime
