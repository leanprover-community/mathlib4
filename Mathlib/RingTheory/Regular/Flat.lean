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
* `RingTheory.Sequence.IsWeaklyRegular.of_flat_of_isBaseChange`: Let `R` be a commutative ring,
  `M` be an `R`-module, `S` be a flat `R`-algebra, `N` be the base change of `M` to `S`.
  If `[r₁, …, rₙ]` is a weakly regular `M`-sequence, then its image in `N` is a weakly regular
  `N`-sequence.
-/

namespace RingTheory.Sequence

open Module

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- Let `R` be a commutative ring, `M` be an `R`-module, `S` be a flat `R`-algebra, `N` be the base
  change of `M` to `S`. If `[r₁, …, rₙ]` is a weakly regular `M`-sequence, then its image in `N` is
  a weakly regular `N`-sequence. -/
theorem IsWeaklyRegular.of_flat_of_isBaseChange [Flat R S] {f : M →ₗ[R] N} (hf : IsBaseChange S f)
    {rs : List R} (reg : IsWeaklyRegular M rs) : IsWeaklyRegular N (rs.map (algebraMap R S)) := by
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

theorem IsWeaklyRegular.of_flat [Flat R S] {rs : List R} (reg : IsWeaklyRegular R rs) :
    IsWeaklyRegular S (rs.map (algebraMap R S)) :=
  reg.of_flat_of_isBaseChange (IsBaseChange.linearMap R S)

variable (S) (T : Submonoid R) [IsLocalization T S]

theorem IsWeaklyRegular.of_isLocalizedModule (f : M →ₗ[R] N) [IsLocalizedModule T f]
    {rs : List R} (reg : IsWeaklyRegular M rs) : IsWeaklyRegular N (rs.map (algebraMap R S)) :=
  have : Flat R S := IsLocalization.flat S T
  reg.of_flat_of_isBaseChange (IsLocalizedModule.isBaseChange T S f)

include T in
theorem IsWeaklyRegular.of_isLocalization {rs : List R} (reg : IsWeaklyRegular R rs) :
    IsWeaklyRegular S (rs.map (algebraMap R S)) :=
  reg.of_isLocalizedModule S T (Algebra.linearMap R S)

variable (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime S p]

theorem IsWeaklyRegular.isRegular_of_isLocalizedModule_of_mem
    [Nontrivial N] [Module.Finite S N] (f : M →ₗ[R] N) [IsLocalizedModule.AtPrime p f]
    {rs : List R} (reg : IsWeaklyRegular M rs) (mem : ∀ r ∈ rs, r ∈ p) :
    IsRegular N (rs.map (algebraMap R S)) := by
  have : IsLocalRing S := IsLocalization.AtPrime.isLocalRing S p
  refine (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal (fun _ hr ↦ ?_)).mpr <|
    reg.of_isLocalizedModule S p.primeCompl f
  rcases List.mem_map.mp hr with ⟨r, hr, eq⟩
  simpa only [← eq, IsLocalization.AtPrime.to_map_mem_maximal_iff S p] using mem r hr

theorem IsWeaklyRegular.isRegular_of_isLocalization_of_mem
    {rs : List R} (reg : IsWeaklyRegular R rs) (mem : ∀ r ∈ rs, r ∈ p) :
    IsRegular S (rs.map (algebraMap R S)) :=
  have : Nontrivial S := IsLocalization.AtPrime.nontrivial S p
  reg.isRegular_of_isLocalizedModule_of_mem S p (Algebra.linearMap R S) mem

variable {S} [FaithfullyFlat R S]

/-- Let `R` be a commutative ring, `M` be an `R`-module, `S` be a faithfully flat `R`-algebra,
  `N` be the base change of `M` to `S`. If `[r₁, …, rₙ]` is a regular `M`-sequence, then its image
  in `N` is a regular `N`-sequence. -/
theorem IsRegular.of_faithfullyFlat_of_isBaseChange {f : M →ₗ[R] N} (hf : IsBaseChange S f)
    {rs : List R} (reg : IsRegular M rs) : IsRegular N (rs.map (algebraMap R S)) := by
  refine ⟨reg.1.of_flat_of_isBaseChange hf, ?_⟩
  rw [← Ideal.map_ofList]
  exact ((hf.map_smul_top_ne_top_iff_of_faithfullyFlat R M _).mpr reg.2.symm).symm

theorem IsRegular.of_faithfullyFlat {rs : List R} (reg : IsRegular R rs) :
    IsRegular S (rs.map (algebraMap R S)) :=
  reg.of_faithfullyFlat_of_isBaseChange (IsBaseChange.linearMap R S)

end RingTheory.Sequence
