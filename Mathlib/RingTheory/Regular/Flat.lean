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

open RingTheory.Sequence Pointwise Module TensorProduct

section Flat

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S] [Flat R S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N]
  [IsScalarTower R S N] {f : M →ₗ[R] N} (hf : IsBaseChange S f)

include hf

theorem IsSMulRegular.of_flat_isBaseChange {x : R} (reg : IsSMulRegular M x) :
    IsSMulRegular N (algebraMap R S x) := by
  have h := Flat.isBaseChange_preserves_injective_linearMap hf hf ((LinearMap.lsmul R M) x) reg
  rwa [show hf.lift (f ∘ₗ (LinearMap.lsmul R M) x) = (LinearMap.lsmul S N) (algebraMap R S x)
    from hf.algHom_ext _ _ (fun _ ↦ by simp [hf.lift_eq])] at h

/-- Let `R` be a commutative ring, `M` be an `R`-module, `S` be a flat `R`-algebra, `N` be the base
  change of `M` to `S`. If `[r₁, …, rₙ]` is a weakly regular `M`-sequence, then its image in `N` is
  a weakly regular `N`-sequence. -/
theorem RingTheory.Sequence.IsWeaklyRegular.of_flat_isBaseChange {rs : List R}
    (reg : IsWeaklyRegular M rs) : IsWeaklyRegular N (rs.map (algebraMap R S)) := by
  generalize len : rs.length = n
  induction' n with n ih generalizing M N rs
  · simp [List.length_eq_zero_iff.mp len]
  · match rs with
    | [] => simp at len
    | x :: rs' =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at len
      simp only [isWeaklyRegular_cons_iff, List.map_cons] at reg ⊢
      have e := (QuotSMulTop.algebraMapTensorEquivTensorQuotSMulTop x M S).symm ≪≫ₗ
        QuotSMulTop.congr ((algebraMap R S) x) hf.equiv
      have hg : IsBaseChange S <|
          e.toLinearMap.restrictScalars R ∘ₗ TensorProduct.mk R S (QuotSMulTop x M) 1 :=
        IsBaseChange.of_equiv e (fun _ ↦ by simp)
      exact ⟨reg.1.of_flat_isBaseChange hf, ih hg reg.2 len⟩

end Flat

section FaithfullyFlat

/-- Let `R` be a commutative ring, `M` be an `R`-module, `S` be a faithfully flat `R`-algebra,
  `N` be the base change of `M` to `S`. If `[r₁, …, rₙ]` is a regular `M`-sequence, then its image
  in `N` is a regular `N`-sequence. -/
theorem RingTheory.Sequence.IsRegular.of_faithfullyFlat_isBaseChange {R S M N : Type*} [CommRing R]
  [CommRing S] [Algebra R S] [FaithfullyFlat R S] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] [Module S N] [IsScalarTower R S N] {f : M →ₗ[R] N} (hf : IsBaseChange S f)
  {rs : List R} (reg : IsRegular M rs) : IsRegular N (rs.map (algebraMap R S)) := by
  refine ⟨reg.1.of_flat_isBaseChange hf, ?_⟩
  rw [← Ideal.map_ofList]
  exact (FaithfullyFlat.smul_top_ne_top_of_isBaseChange R M hf reg.2.symm).symm

end FaithfullyFlat

section IsLocalizedModule

variable {R : Type*} [CommRing R] (S : Submonoid R)
  (R' : Type*) [CommRing R'] [Algebra R R'] [IsLocalization S R']
  {M : Type*} [AddCommGroup M] [Module R M]
  {M' : Type*} [AddCommGroup M'] [Module R M'] [Module R' M'] [IsScalarTower R R' M']
  (f : M →ₗ[R] M') [IsLocalizedModule S f]

include S f

theorem IsSMulRegular.of_isLocalizedModule {x : R} (reg : IsSMulRegular M x) :
    IsSMulRegular M' (algebraMap R R' x) :=
  have : Flat R R' := IsLocalization.flat R' S
  reg.of_flat_isBaseChange (IsLocalizedModule.isBaseChange S R' f)

theorem RingTheory.Sequence.IsWeaklyRegular.of_isLocalizedModule {rs : List R}
    (reg : IsWeaklyRegular M rs) : IsWeaklyRegular M' (rs.map (algebraMap R R')) :=
  have : Flat R R' := IsLocalization.flat R' S
  reg.of_flat_isBaseChange (IsLocalizedModule.isBaseChange S R' f)

end IsLocalizedModule

section AtPrime

theorem RingTheory.Sequence.IsWeaklyRegular.isRegular_of_isLocalizedModule_of_mem_prime
    {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime] (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ]
    [IsLocalization.AtPrime Rₚ p]
    {M Mₚ : Type*} [AddCommGroup M] [Module R M] [Nontrivial Mₚ] [AddCommGroup Mₚ] [Module Rₚ Mₚ]
    [Module.Finite Rₚ Mₚ] [Module R Mₚ] [IsScalarTower R Rₚ Mₚ]
    (f : M →ₗ[R] Mₚ) [IsLocalizedModule.AtPrime p f] {rs : List R} (reg : IsWeaklyRegular M rs)
    (mem : ∀ r ∈ rs, r ∈ p) : IsRegular Mₚ (rs.map (algebraMap R Rₚ)) := by
  have : IsLocalRing Rₚ := IsLocalization.AtPrime.isLocalRing Rₚ p
  refine (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal ?_).mpr <|
    reg.of_isLocalizedModule p.primeCompl Rₚ f
  intro _ hr
  rcases List.mem_map.mp hr with ⟨r, hr, eq⟩
  simpa only [← eq, IsLocalization.AtPrime.to_map_mem_maximal_iff Rₚ p] using mem r hr

end AtPrime
