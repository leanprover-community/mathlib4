/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.RingTheory.Support

/-!

# The free locus of a module

## Main definitions and results

Let `M` be a finitely presented `R`-module.
- `Module.freeLocus`: The set of points `x` in `Spec R` such that `Mₓ` is free over `Rₓ`.
- `Module.freeLocus_eq_univ_iff`:
  The free locus is the whole `Spec R` if and only if `M` is projective.
- `Module.basicOpen_subset_freeLocus_iff`: `D(f)` is contained in the free locus if and only if
  `M_f` is projective over `R_f`.
- `Module.rankAtStalk`: The function `Spec R → ℕ` sending `x` to `rank_{Rₓ} Mₓ`.
- `Module.isLocallyConstant_rankAtStalk`:
  If `M` is flat over `R`, then `rankAtStalk` is locally constant.

-/

universe uR uM

variable (R : Type uR) (M : Type uM) [CommRing R] [AddCommGroup M] [Module R M]

namespace Module

open PrimeSpectrum TensorProduct

/-- The free locus of a module, i.e. the set of primes `p` such that `Mₚ` is free over `Rₚ`. -/
def freeLocus : Set (PrimeSpectrum R) :=
  { p | Module.Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) }

variable {R M}

lemma mem_freeLocus {p} : p ∈ freeLocus R M ↔
    Module.Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) :=
  Iff.rfl

attribute [local instance] RingHomInvPair.of_ringEquiv in
lemma mem_freeLocus_of_isLocalization (p : PrimeSpectrum R)
    (Rₚ Mₚ) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p.asIdeal]
    [AddCommGroup Mₚ] [Module R Mₚ] (f : M →ₗ[R] Mₚ) [IsLocalizedModule p.asIdeal.primeCompl f]
    [Module Rₚ Mₚ] [IsScalarTower R Rₚ Mₚ] :
    p ∈ freeLocus R M ↔ Module.Free Rₚ Mₚ := by
  apply Module.Free.iff_of_ringEquiv (IsLocalization.algEquiv p.asIdeal.primeCompl
      (Localization.AtPrime p.asIdeal) Rₚ).toRingEquiv
  refine { __ := IsLocalizedModule.iso p.asIdeal.primeCompl f, map_smul' := ?_ }
  intro r x
  obtain ⟨r, s, rfl⟩ := IsLocalization.mk'_surjective p.asIdeal.primeCompl r
  apply ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units f s)).1
  simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
    algebraMap_end_apply, AlgEquiv.toRingEquiv_eq_coe,
    AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_coe, IsLocalization.algEquiv_apply,
    IsLocalization.map_id_mk']
  simp only [← map_smul, ← smul_assoc, IsLocalization.smul_mk'_self, algebraMap_smul]

attribute [local instance] RingHomInvPair.of_ringEquiv in
lemma mem_freeLocus_iff_tensor (p : PrimeSpectrum R)
    (Rₚ) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p.asIdeal] :
    p ∈ freeLocus R M ↔ Module.Free Rₚ (Rₚ ⊗[R] M) := by
  have := (isLocalizedModule_iff_isBaseChange p.asIdeal.primeCompl _ _).mpr
    (TensorProduct.isBaseChange R M Rₚ)
  exact mem_freeLocus_of_isLocalization p Rₚ (f := TensorProduct.mk R Rₚ M 1)

lemma freeLocus_congr {M'} [AddCommGroup M'] [Module R M'] (e : M ≃ₗ[R] M') :
    freeLocus R M = freeLocus R M' := by
  ext p
  exact mem_freeLocus_of_isLocalization _ _ _
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M' ∘ₗ e.toLinearMap)

open TensorProduct in
lemma comap_freeLocus_le {A} [CommRing A] [Algebra R A] :
    comap (algebraMap R A) ⁻¹' freeLocus R M ≤ freeLocus A (A ⊗[R] M) := by
  intro p hp
  let Rₚ := Localization.AtPrime (comap (algebraMap R A) p).asIdeal
  let Aₚ := Localization.AtPrime p.asIdeal
  rw [Set.mem_preimage, mem_freeLocus_iff_tensor _ Rₚ] at hp
  rw [mem_freeLocus_iff_tensor _ Aₚ]
  letI algebra : Algebra Rₚ Aₚ := (Localization.localRingHom
    (comap (algebraMap R A) p).asIdeal p.asIdeal (algebraMap R A) rfl).toAlgebra
  have : IsScalarTower R Rₚ Aₚ := IsScalarTower.of_algebraMap_eq'
    (by simp [Rₚ, Aₚ, algebra, RingHom.algebraMap_toAlgebra, Localization.localRingHom,
        ← IsScalarTower.algebraMap_eq])
  let e := AlgebraTensorModule.cancelBaseChange R Rₚ Aₚ Aₚ M ≪≫ₗ
    (AlgebraTensorModule.cancelBaseChange R A Aₚ Aₚ M).symm
  exact .of_equiv e

lemma freeLocus_localization (S : Submonoid R) :
    freeLocus (Localization S) (LocalizedModule S M) =
      comap (algebraMap R _) ⁻¹' freeLocus R M := by
  ext p
  simp only [Set.mem_preimage]
  let p' := p.asIdeal.comap (algebraMap R _)
  have hp' : S ≤ p'.primeCompl := fun x hx H ↦
    p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ H (IsLocalization.map_units _ ⟨x, hx⟩))
  let Rₚ := Localization.AtPrime p'
  let Mₚ := LocalizedModule p'.primeCompl M
  letI : Algebra (Localization S) Rₚ :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ S p'.primeCompl hp'
  have : IsScalarTower R (Localization S) Rₚ :=
    IsLocalization.localization_isScalarTower_of_submonoid_le ..
  have : IsLocalization.AtPrime Rₚ p.asIdeal := by
    have := IsLocalization.isLocalization_of_submonoid_le (Localization S) Rₚ _ _ hp'
    apply IsLocalization.isLocalization_of_is_exists_mul_mem _
      (Submonoid.map (algebraMap R (Localization S)) p'.primeCompl)
    · rintro _ ⟨x, hx, rfl⟩; exact hx
    · rintro ⟨x, hx⟩
      obtain ⟨x, s, rfl⟩ := IsLocalization.mk'_surjective S x
      refine ⟨algebraMap _ _ s.1, x, fun H ↦ hx ?_, by simp⟩
      rw [IsLocalization.mk'_eq_mul_mk'_one]
      exact Ideal.mul_mem_right _ _ H
  letI : Module (Localization S) Mₚ := Module.compHom Mₚ (algebraMap _ Rₚ)
  have : IsScalarTower R (Localization S) Mₚ :=
    ⟨fun r r' m ↦ show algebraMap _ Rₚ (r • r') • m = _ by
      simp [p', Rₚ, Mₚ, Algebra.smul_def, ← IsScalarTower.algebraMap_apply, mul_smul]; rfl⟩
  have : IsScalarTower (Localization S) Rₚ Mₚ :=
    ⟨fun r r' m ↦ show _ = algebraMap _ Rₚ r • r' • m by rw [← mul_smul, ← Algebra.smul_def]⟩
  let l := (IsLocalizedModule.liftOfLE _ _ hp' (LocalizedModule.mkLinearMap S M)
    (LocalizedModule.mkLinearMap p'.primeCompl M)).extendScalarsOfIsLocalization S
    (Localization S)
  have : IsLocalizedModule p.asIdeal.primeCompl l := by
    have : IsLocalizedModule p'.primeCompl (l.restrictScalars R) :=
      inferInstanceAs (IsLocalizedModule p'.primeCompl
        (IsLocalizedModule.liftOfLE _ _ hp' (LocalizedModule.mkLinearMap S M)
        (LocalizedModule.mkLinearMap p'.primeCompl M)))
    have : IsLocalizedModule (Algebra.algebraMapSubmonoid (Localization S) p'.primeCompl) l :=
      IsLocalizedModule.of_restrictScalars p'.primeCompl ..
    apply IsLocalizedModule.of_exists_mul_mem
      (Algebra.algebraMapSubmonoid (Localization S) p'.primeCompl)
    · rintro _ ⟨x, hx, rfl⟩; exact hx
    · rintro ⟨x, hx⟩
      obtain ⟨x, s, rfl⟩ := IsLocalization.mk'_surjective S x
      refine ⟨algebraMap _ _ s.1, x, fun H ↦ hx ?_, by simp⟩
      rw [IsLocalization.mk'_eq_mul_mk'_one]
      exact Ideal.mul_mem_right _ _ H
  rw [mem_freeLocus_of_isLocalization (R := Localization S) p Rₚ Mₚ l]
  rfl

lemma freeLocus_eq_univ_iff [Module.FinitePresentation R M] :
    freeLocus R M = Set.univ ↔ Module.Projective R M := by
  simp_rw [Set.eq_univ_iff_forall, mem_freeLocus]
  exact ⟨fun H ↦ Module.projective_of_localization_maximal fun I hI ↦
    have := H ⟨I, hI.isPrime⟩; .of_free, fun H x ↦ Module.free_of_flat_of_isLocalRing⟩

lemma freeLocus_eq_univ [Module.FinitePresentation R M] [Module.Flat R M] :
    freeLocus R M = Set.univ := by
  simp_rw [Set.eq_univ_iff_forall, mem_freeLocus]
  exact fun x ↦ Module.free_of_flat_of_isLocalRing

lemma basicOpen_subset_freeLocus_iff [Module.FinitePresentation R M] {f : R} :
    (basicOpen f : Set (PrimeSpectrum R)) ⊆ freeLocus R M ↔
      Module.Projective (Localization.Away f) (LocalizedModule (.powers f) M) := by
  rw [← freeLocus_eq_univ_iff, freeLocus_localization,
    Set.preimage_eq_univ_iff, localization_away_comap_range _ f]

lemma isOpen_freeLocus [Module.FinitePresentation R M] :
    IsOpen (freeLocus R M) := by
  refine isOpen_iff_forall_mem_open.mpr fun x hx ↦ ?_
  have : Module.Free _ _ := hx
  obtain ⟨r, hr, hr', _⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    x.asIdeal.primeCompl (LocalizedModule.mkLinearMap x.asIdeal.primeCompl M)
    (Localization.AtPrime x.asIdeal)
  exact ⟨basicOpen r, basicOpen_subset_freeLocus_iff.mpr inferInstance, (basicOpen r).2, hr⟩

variable (M) in
/-- The rank of `M` at the stalk of `p` is the rank of `Mₚ` as a `Rₚ`-module. -/
noncomputable
def rankAtStalk (p : PrimeSpectrum R) : ℕ :=
  Module.finrank (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M)

lemma isLocallyConstant_rankAtStalk_freeLocus [Module.FinitePresentation R M] :
    IsLocallyConstant (fun x : freeLocus R M ↦ rankAtStalk M x.1) := by
  refine (IsLocallyConstant.iff_exists_open _).mpr fun ⟨x, hx⟩ ↦ ?_
  have : Module.Free _ _ := hx
  obtain ⟨f, hf, hf', hf''⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    x.asIdeal.primeCompl (LocalizedModule.mkLinearMap x.asIdeal.primeCompl M)
    (Localization.AtPrime x.asIdeal)
  refine ⟨Subtype.val ⁻¹' basicOpen f, (basicOpen f).2.preimage continuous_subtype_val, hf, ?_⟩
  rintro ⟨p, hp''⟩ hp
  let p' := Algebra.algebraMapSubmonoid (Localization (.powers f)) p.asIdeal.primeCompl
  have hp' : Submonoid.powers f ≤ p.asIdeal.primeCompl := by
    simpa [Submonoid.powers_le, Ideal.primeCompl]
  let Rₚ := Localization.AtPrime p.asIdeal
  let Mₚ := LocalizedModule p.asIdeal.primeCompl M
  letI : Algebra (Localization.Away f) Rₚ :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (.powers f) p.asIdeal.primeCompl hp'
  have : IsScalarTower R (Localization.Away f) Rₚ :=
    IsLocalization.localization_isScalarTower_of_submonoid_le ..
  letI : Module (Localization.Away f) Mₚ := Module.compHom Mₚ (algebraMap _ Rₚ)
  have : IsScalarTower R (Localization.Away f) Mₚ :=
    ⟨fun r r' m ↦ show algebraMap _ Rₚ (r • r') • m = _ by
      simp [Rₚ, Mₚ, Algebra.smul_def, ← IsScalarTower.algebraMap_apply, mul_smul]; rfl⟩
  have : IsScalarTower (Localization.Away f) Rₚ Mₚ :=
    ⟨fun r r' m ↦ show _ = algebraMap _ Rₚ r • r' • m by rw [← mul_smul, ← Algebra.smul_def]⟩
  let l := (IsLocalizedModule.liftOfLE _ _ hp' (LocalizedModule.mkLinearMap (.powers f) M)
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)).extendScalarsOfIsLocalization (.powers f)
    (Localization.Away f)
  have : IsLocalization p' Rₚ :=
    IsLocalization.isLocalization_of_submonoid_le (Localization.Away f) Rₚ _ _ hp'
  have : IsLocalizedModule p.asIdeal.primeCompl (l.restrictScalars R) :=
    inferInstanceAs (IsLocalizedModule p.asIdeal.primeCompl
    ((IsLocalizedModule.liftOfLE _ _ hp' (LocalizedModule.mkLinearMap (.powers f) M)
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M))))
  have : IsLocalizedModule (Algebra.algebraMapSubmonoid _ p.asIdeal.primeCompl) l :=
      IsLocalizedModule.of_restrictScalars p.asIdeal.primeCompl ..
  have := Module.finrank_of_isLocalizedModule_of_free Rₚ p' l
  simp [Rₚ, rankAtStalk, this, hf'']

lemma isLocallyConstant_rankAtStalk [Module.FinitePresentation R M] [Module.Flat R M] :
    IsLocallyConstant (rankAtStalk (R := R) M) := by
  let e : freeLocus R M ≃ₜ PrimeSpectrum R :=
    (Homeomorph.setCongr freeLocus_eq_univ).trans (Homeomorph.Set.univ (PrimeSpectrum R))
  convert isLocallyConstant_rankAtStalk_freeLocus.comp_continuous e.symm.continuous

@[simp]
lemma rankAtStalk_eq_zero_of_subsingleton [Subsingleton M] :
    rankAtStalk (R := R) M = 0 := by
  ext p
  exact Module.finrank_zero_of_subsingleton

lemma nontrivial_of_rankAtStalk_pos (h : 0 < rankAtStalk (R := R) M) :
    Nontrivial M := by
  by_contra! hn
  have : Subsingleton M := not_nontrivial_iff_subsingleton.mp hn
  simp at h

lemma rankAtStalk_eq_of_equiv {N : Type*} [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) :
    rankAtStalk (R := R) M = rankAtStalk N := by
  ext p
  exact IsLocalizedModule.mapEquiv p.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl N) _ e |>.finrank_eq

/-- If `M` is `R`-free, its rank at stalks is constant and agrees with the `R`-rank of `M`. -/
@[simp]
lemma rankAtStalk_eq_finrank_of_free [Module.Free R M] :
    rankAtStalk (R := R) M = Module.finrank R M := by
  ext p
  simp [rankAtStalk, finrank_of_isLocalizedModule_of_free _ p.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)]

lemma rankAtStalk_self [Nontrivial R] : rankAtStalk (R := R) R = 1 := by
  simp

open LocalizedModule Localization

/-- The rank of `Π i, M i` at a prime `p` is the sum of the ranks of `M i` at `p`. -/
lemma rankAtStalk_pi {ι : Type*} [Finite ι] (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, Module.Flat R (M i)]
    [∀ i, Module.Finite R (M i)] (p : PrimeSpectrum R) :
    rankAtStalk (Π i, M i) p = ∑ᶠ i, rankAtStalk (M i) p := by
  cases nonempty_fintype ι
  let f : (Π i, M i) →ₗ[R] Π i, LocalizedModule p.asIdeal.primeCompl (M i) :=
    .pi (fun i ↦ mkLinearMap p.asIdeal.primeCompl (M i) ∘ₗ LinearMap.proj i)
  let e : LocalizedModule p.asIdeal.primeCompl (Π i, M i) ≃ₗ[Localization.AtPrime p.asIdeal]
      Π i, LocalizedModule p.asIdeal.primeCompl (M i) :=
    IsLocalizedModule.linearEquiv p.asIdeal.primeCompl
      (mkLinearMap _ _) f |>.extendScalarsOfIsLocalization p.asIdeal.primeCompl _
  have (i : ι) : Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl (M i)) :=
    free_of_flat_of_isLocalRing
  simp_rw [rankAtStalk, e.finrank_eq, Module.finrank_pi_fintype, finsum_eq_sum_of_fintype]

lemma rankAtStalk_eq_finrank_tensorProduct (p : PrimeSpectrum R) :
    rankAtStalk M p =
      finrank (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal ⊗[R] M) := by
  let e : LocalizedModule p.asIdeal.primeCompl M ≃ₗ[Localization.AtPrime p.asIdeal]
      Localization.AtPrime p.asIdeal ⊗[R] M :=
    LocalizedModule.equivTensorProduct p.asIdeal.primeCompl M
  rw [rankAtStalk, e.finrank_eq]

variable [Flat R M] [Module.Finite R M]

attribute [local instance] free_of_flat_of_isLocalRing

lemma rankAtStalk_eq_zero_iff_notMem_support (p : PrimeSpectrum R) :
    rankAtStalk M p = 0 ↔ p ∉ support R M := by
  rw [notMem_support_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ Module.finrank_zero_of_subsingleton⟩
  apply subsingleton_of_rank_zero (R := Localization.AtPrime p.asIdeal)
  dsimp [rankAtStalk] at h
  simp [← finrank_eq_rank, h]

lemma rankAtStalk_pos_iff_mem_support (p : PrimeSpectrum R) :
    0 < rankAtStalk M p ↔ p ∈ support R M :=
  Nat.pos_iff_ne_zero.trans (rankAtStalk_eq_zero_iff_notMem_support _).not_left

lemma rankAtStalk_eq_zero_iff_subsingleton :
    rankAtStalk (R := R) M = 0 ↔ Subsingleton M := by
  refine ⟨fun h ↦ ?_, fun _ ↦ rankAtStalk_eq_zero_of_subsingleton⟩
  simp_rw [← support_eq_empty_iff (R := R), Set.eq_empty_iff_forall_notMem]
  intro p
  rw [← rankAtStalk_eq_zero_iff_notMem_support, h, Pi.zero_apply]

variable (M) in
/-- The rank of `M × N` at `p` is equal to the sum of the ranks. -/
lemma rankAtStalk_prod (N : Type*) [AddCommGroup N] [Module R N]
    [Module.Flat R N] [Module.Finite R N] :
    rankAtStalk (R := R) (M × N) = rankAtStalk M + rankAtStalk N := by
  ext p
  let e : LocalizedModule p.asIdeal.primeCompl (M × N) ≃ₗ[Localization.AtPrime p.asIdeal]
      LocalizedModule p.asIdeal.primeCompl M × LocalizedModule p.asIdeal.primeCompl N :=
    IsLocalizedModule.linearEquiv p.asIdeal.primeCompl (mkLinearMap _ _)
      (.prodMap (mkLinearMap _ M) (mkLinearMap _ N)) |>.extendScalarsOfIsLocalization
      p.asIdeal.primeCompl _
  simp [rankAtStalk, e.finrank_eq]

lemma rankAtStalk_baseChange {S : Type*} [CommRing S] [Algebra R S] (p : PrimeSpectrum S) :
    rankAtStalk (S ⊗[R] M) p = rankAtStalk M ((algebraMap R S).specComap p) := by
  let q : PrimeSpectrum R := (algebraMap R S).specComap p
  let e : LocalizedModule p.asIdeal.primeCompl (S ⊗[R] M) ≃ₗ[Localization.AtPrime p.asIdeal]
      Localization.AtPrime p.asIdeal ⊗[Localization.AtPrime q.asIdeal]
        LocalizedModule q.asIdeal.primeCompl M :=
    LocalizedModule.equivTensorProduct _ _ ≪≫ₗ
      (AlgebraTensorModule.cancelBaseChange R S _ _ M) ≪≫ₗ
      (AlgebraTensorModule.cancelBaseChange R _ _ _ M).symm ≪≫ₗ
      (AlgebraTensorModule.congr (LinearEquiv.refl _ _)
        (LocalizedModule.equivTensorProduct _ M).symm)
  rw [rankAtStalk, e.finrank_eq]
  apply Module.finrank_baseChange

/-- See `rankAtStalk_tensorProduct_of_isScalarTower` for a hetero-basic version. -/
lemma rankAtStalk_tensorProduct (N : Type*) [AddCommGroup N] [Module R N] [Module.Finite R N]
    [Module.Flat R N] : rankAtStalk (M ⊗[R] N) = rankAtStalk M * rankAtStalk (R := R) N := by
  ext p
  let e : Localization.AtPrime p.asIdeal ⊗[R] (M ⊗[R] N) ≃ₗ[Localization.AtPrime p.asIdeal]
      (Localization.AtPrime p.asIdeal ⊗[R] M) ⊗[Localization.AtPrime p.asIdeal]
        (Localization.AtPrime p.asIdeal ⊗[R] N) :=
    (AlgebraTensorModule.assoc _ _ _ _ _ _).symm ≪≫ₗ
      (AlgebraTensorModule.cancelBaseChange _ _ _ _ _).symm
  rw [rankAtStalk_eq_finrank_tensorProduct, e.finrank_eq, finrank_tensorProduct,
    ← rankAtStalk_eq_finrank_tensorProduct, ← rankAtStalk_eq_finrank_tensorProduct, Pi.mul_apply]

lemma rankAtStalk_tensorProduct_of_isScalarTower {S : Type*} [CommRing S] [Algebra R S]
    (N : Type*) [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [Module.Finite S N] [Module.Flat S N] (p : PrimeSpectrum S) :
    rankAtStalk (N ⊗[R] M) p = rankAtStalk N p * rankAtStalk M ((algebraMap R S).specComap p) := by
  simp [rankAtStalk_eq_of_equiv (AlgebraTensorModule.cancelBaseChange R S S N M).symm,
    rankAtStalk_tensorProduct, rankAtStalk_baseChange]

/-- The rank of a module `M` at a prime `p` is equal to the dimension
of `κ(p) ⊗[R] M` as a `κ(p)`-module. -/
lemma rankAtStalk_eq (p : PrimeSpectrum R) :
    rankAtStalk M p = finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M) := by
  let k := p.asIdeal.ResidueField
  let e : k ⊗[Localization.AtPrime p.asIdeal] (Localization.AtPrime p.asIdeal ⊗[R] M) ≃ₗ[k]
      k ⊗[R] M :=
    AlgebraTensorModule.cancelBaseChange _ _ _ _ _
  rw [← e.finrank_eq, finrank_baseChange, rankAtStalk_eq_finrank_tensorProduct]

end Module
