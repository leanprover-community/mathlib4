/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.TensorProduct.Pi
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.FieldTheory.PrimitiveElement

/-!
# Transcendental separable extensions
-/

universe u v

@[expose] public section

open TensorProduct

section

variable (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]

class Algebra.IsSeparablyGenerated : Prop where
  isSeparable' : ∃ (ι : Type v) (f : ι → K),
    IsTranscendenceBasis k f ∧
    Algebra.IsSeparable (IntermediateField.adjoin k (Set.range f)) K

class Algebra.IsTranscendentalSeparable : Prop where
  forall_isSeparablyGenerated : ∀ (A' : IntermediateField k K),
    Algebra.EssFiniteType k A' → Algebra.IsSeparablyGenerated k A'

end

lemma localization_minimal_isField {S : Type*} [CommRing S] [IsReduced S]
    (p : Ideal S) (min : p ∈ minimalPrimes S) :
    letI := min.1.1
    IsField (Localization.AtPrime p) := by
  let := min.1.1
  rw [IsLocalRing.isField_iff_maximalIdeal_eq, eq_bot_iff]
  intro x hx
  apply IsReduced.eq_zero x (nilpotent_iff_mem_prime.mpr (fun q hq ↦ ?_))
  convert hx
  have : Ideal.comap (algebraMap S (Localization.AtPrime p)) q ≤ p := by
    apply le_of_le_of_eq _ (IsLocalization.AtPrime.comap_maximalIdeal (Localization.AtPrime p) p)
    exact Ideal.comap_mono (IsLocalRing.le_maximalIdeal_of_isPrime q)
  rw [← Localization.AtPrime.eq_maximalIdeal_iff_comap_eq]
  exact le_antisymm this (min.2 ⟨q.comap_isPrime _, bot_le⟩ this)

def toLocalizationMinimal (S : Type*) [CommRing S] :=
  (Pi.ringHom (fun (p : minimalPrimes S) ↦
    letI := Ideal.minimalPrimes_isPrime p.2
    algebraMap S (Localization.AtPrime p.1)))

lemma isReduced_injective_to_prod_localizations (S : Type*) [CommRing S] [IsReduced S] :
    Function.Injective (toLocalizationMinimal S) := by
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
  intro x hx
  apply IsReduced.eq_zero x (nilpotent_iff_mem_prime.mpr (fun q hq ↦ ?_))
  rcases Ideal.exists_minimalPrimes_le (bot_le (a := q)) with ⟨p, min, hp⟩
  let := min.1.1
  apply hp
  rw [← IsLocalization.AtPrime.comap_maximalIdeal (Localization.AtPrime p) p, Ideal.mem_comap]
  have : (toLocalizationMinimal S) x ⟨p, min⟩ = 0 := by simp [hx]
  simp only [toLocalizationMinimal, Pi.ringHom_apply] at this
  simp [this]

lemma IsReduced.tensorProduct_of_forall_fg_intermediateField {k : Type*} [Field k]
    {S : Type*} [CommRing S] [Algebra k S] {K : Type*} [Field K] [Algebra k K]
    (h : ∀ (L : IntermediateField k K), L.FG → IsReduced (TensorProduct k S L)) :
    IsReduced (TensorProduct k S K) := by
  refine IsReduced.tensorProduct_of_flat_of_forall_fg (fun B ⟨T, hT⟩ ↦ ?_)
  have := h _ (IntermediateField.fg_adjoin_finset T)
  have le : B ≤ (IntermediateField.adjoin k (T : Set K)).toSubalgebra := by
    simp [← hT, Algebra.adjoin_le_iff]
  have : Function.Injective (Algebra.TensorProduct.lTensor S (Subalgebra.inclusion le)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (Subalgebra.inclusion_injective le)
  exact isReduced_of_injective _ this

variable (k : Type*) [Field k] (K : Type*) [Field K] [Algebra k K] (S : Type*) [CommRing S]

open scoped Polynomial

lemma isReduced_of_quotient_separable [IsDomain S] (f : S[X])
    (sep : f.Separable) : IsReduced (S[X] ⧸ Ideal.span {f}) := by
  sorry

noncomputable def polynomialTensorProductEquiv [Algebra k S] : K[X] ⊗[k] S ≃ₐ[K] (K ⊗[k] S)[X] :=
  ((((Algebra.TensorProduct.congr (polyEquivTensor' k K) AlgEquiv.refl).trans
    (Algebra.TensorProduct.assoc k k K K k[X] S)).trans
      (Algebra.TensorProduct.congr AlgEquiv.refl (Algebra.TensorProduct.comm k k[X] S))).trans
        (Algebra.TensorProduct.assoc k k K K S k[X]).symm).trans
          ((polyEquivTensor' k (K ⊗[k] S)).symm.restrictScalars K)

lemma polynomialTensorProductEquiv_map_algebraMap [Algebra k S] (f : K[X]) :
    f.map (algebraMap K (K ⊗[k] S)) =
    (polynomialTensorProductEquiv k K S) ((algebraMap K[X] (K[X] ⊗[k] S)) f) := by
  obtain ⟨g, rfl⟩ := (polyEquivTensor' k K).symm.surjective f
  induction g with
  | zero => simp
  | add g1 g2 hg1 hg2 => simp only [map_add, Polynomial.map_add, hg1, hg2]
  | tmul x y =>
    have : Polynomial.map (algebraMap K (K ⊗[k] S)) ((polyEquivTensor k K).symm (x ⊗ₜ[k] y)) =
      (polyEquivTensor k (K ⊗[k] S)).symm (x ⊗ₜ[k] 1 ⊗ₜ[k] y) := by
      simp [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
    simpa [- polyEquivTensor_symm_apply_tmul_eq_smul, polynomialTensorProductEquiv]

noncomputable def quotientPolynomialTensorProductEquiv (f : K[X]) [Algebra k S] :
    (K[X] ⧸ Ideal.span {f}) ⊗[k] S ≃ₐ[K]
    (K ⊗[k] S)[X] ⧸ Ideal.span {f.map (algebraMap K (K ⊗[k] S))} :=
  let : IsScalarTower K (K[X] ⧸ Ideal.span {f})
    (K[X] ⊗[k] S ⧸ Ideal.map (algebraMap K[X] (K[X] ⊗[k] S)) (Ideal.span {f})) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let e : (K[X] ⧸ Ideal.span {f}) ⊗[K[X]] (K[X] ⊗[k] S) ≃ₐ[K]
    (K[X] ⊗[k] S) ⧸ ((Ideal.span {f}).map (algebraMap K[X] (K[X] ⊗[k] S))) :=
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor _ _).symm.restrictScalars K
  (((Algebra.TensorProduct.cancelBaseChange k K[X] K[X] (K[X] ⧸ Ideal.span {f})
    S).symm.restrictScalars K).trans
      ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor _ _).symm.restrictScalars K)).trans
        (Ideal.quotientEquivAlg _ _ (polynomialTensorProductEquiv k K S) (by
          simp only [Ideal.map_span, Set.image_singleton, RingHom.coe_coe,
            polynomialTensorProductEquiv_map_algebraMap]))

open IntermediateField.algebraAdjoinAdjoin in
lemma tensorProduct_isReduced_of_isTranscendentalSeparable_of_isDomain
    (S : Type*) [CommRing S] [Algebra k S] [IsDomain S]
    [Algebra.IsSeparablyGenerated k K] [Algebra.EssFiniteType k K] :
    IsReduced (TensorProduct k K S) := by
  classical
  obtain ⟨ι, f, isT, sep⟩ : Algebra.IsSeparablyGenerated k K := ‹_›
  set K' := IntermediateField.adjoin k (Set.range f)
  have : Algebra.IsAlgebraic K' K := isT.isAlgebraic_field
  have : Algebra.EssFiniteType K' K := Algebra.EssFiniteType.of_comp k K' K
  have : FiniteDimensional K' K := Algebra.finite_of_essFiniteType_of_isAlgebraic
  obtain ⟨y, hy⟩ := Field.exists_primitive_element K' K
  let kx := Algebra.adjoin k (Set.range f)
  let e : TensorProduct k kx S ≃ₐ[k] MvPolynomial ι S :=
    (Algebra.TensorProduct.congr (AlgebraicIndependent.aevalEquiv isT.1).symm AlgEquiv.refl).trans
      MvPolynomial.scalarRTensorAlgEquiv
  have isd1 : IsDomain (TensorProduct k kx S) := e.injective.isDomain
  let nz := nonZeroDivisors kx
  have : IsLocalization nz K' := inferInstanceAs (IsFractionRing _ K')
  have isl := IsLocalization.tensorRight K' nz (S := TensorProduct k kx S)
  let : Algebra (kx ⊗[k] S) (K' ⊗[kx] (kx ⊗[k] S)) := Algebra.TensorProduct.rightAlgebra
  have le_nz : nz.map (algebraMap kx (kx ⊗[k] S)) ≤ nonZeroDivisors (↥kx ⊗[k] S) := by
    rw [Submonoid.map_le_iff_le_comap]
    intro x
    simp only [mem_nonZeroDivisors_iff_ne_zero, ne_eq, Submonoid.mem_comap, nz]
    exact fun hx ↦ (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective kx (kx ⊗[k] S))).mpr hx
  have isd2 := @IsLocalization.isDomain_of_le_nonZeroDivisors _ _ _ _ _ _ isl isd1 le_nz
  have isd3 : IsDomain (K' ⊗[k] S) :=
    (Algebra.TensorProduct.cancelBaseChange k kx kx K' S).symm.injective.isDomain
  let f := minpoly K' y
  have fsep : f.Separable := sep.1 y
  let eK : K ≃ₐ[K'] K'[X] ⧸ Ideal.span {f} :=
    (IntermediateField.topEquiv.symm.trans (IntermediateField.equivOfEq hy).symm).trans
    (IntermediateField.adjoinRootEquivAdjoin K' (Algebra.IsIntegral.isIntegral y)).symm
  let eTen : K ⊗[k] S ≃ₐ[K'] (K' ⊗[k] S)[X] ⧸ Ideal.span {f.map (algebraMap K' (K' ⊗[k] S))} :=
    (Algebra.TensorProduct.congr eK AlgEquiv.refl).trans
    (quotientPolynomialTensorProductEquiv k K' S f)
  have red : IsReduced ((K' ⊗[k] S)[X] ⧸ Ideal.span {f.map (algebraMap K' (K' ⊗[k] S))}) :=
    isReduced_of_quotient_separable _ _ fsep.map
  exact isReduced_of_injective _ eTen.injective

lemma tensorProduct_isReduced_of_isTranscendentalSeparable_of_isReduced_of_essFiniteType
    (S : Type*) [CommRing S] [Algebra k S] [Algebra.FiniteType k S] [IsReduced S]
    [Algebra.IsSeparablyGenerated k K] [Algebra.EssFiniteType k K] :
    IsReduced (TensorProduct k K S) := by
  classical
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  have h (x : k) (y : S) : (toLocalizationMinimal S) (x • y) = x • (toLocalizationMinimal S) y := by
    ext p
    simp [toLocalizationMinimal, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]
  let f := AlgHom.mk' (toLocalizationMinimal S) h
  have inj : Function.Injective (Algebra.TensorProduct.lTensor K f) :=
    Module.Flat.lTensor_preserves_injective_linearMap _
      (isReduced_injective_to_prod_localizations S)
  let : Fintype (minimalPrimes S) := (minimalPrimes.finite_of_isNoetherianRing S).fintype
  have (p : minimalPrimes S) :
    letI := Ideal.minimalPrimes_isPrime p.2
    IsReduced (K ⊗[k] Localization.AtPrime p.1) := by
    let := (localization_minimal_isField p.1 p.2).toField
    exact tensorProduct_isReduced_of_isTranscendentalSeparable_of_isDomain k K _
  have : IsReduced (K ⊗[k] ((p : (minimalPrimes S)) →
    letI := Ideal.minimalPrimes_isPrime p.2
    Localization.AtPrime p.1)) := by
    apply isReduced_of_injective _ (Algebra.TensorProduct.piRight k k K
      (fun (p : (minimalPrimes S)) ↦
        letI := Ideal.minimalPrimes_isPrime p.2
        Localization.AtPrime p.1)).injective
  exact isReduced_of_injective _ inj

lemma tensorProduct_isReduced_of_isTranscendentalSeparable_of_isReduced
    {S : Type*} [CommRing S] [Algebra k S] [IsReduced S]
    {K : Type*} [Field K] [Algebra k K] [Algebra.IsTranscendentalSeparable k K] :
    IsReduced (TensorProduct k K S) := by
  refine IsReduced.tensorProduct_of_flat_of_forall_fg (fun B hB ↦ ?_)
  have : Algebra.FiniteType k B := (Subalgebra.fg_iff_finiteType B).mp hB
  have : IsReduced B := isReduced_of_injective B.val Subtype.val_injective
  have : IsReduced (TensorProduct k B K) := by
    refine IsReduced.tensorProduct_of_forall_fg_intermediateField (fun L hL ↦ ?_)
    rw [← IntermediateField.essFiniteType_iff] at hL
    have := Algebra.IsTranscendentalSeparable.forall_isSeparablyGenerated L hL
    have := tensorProduct_isReduced_of_isTranscendentalSeparable_of_isReduced_of_essFiniteType k L B
    exact isReduced_of_injective _ (Algebra.TensorProduct.comm k B L).injective
  exact isReduced_of_injective _ (Algebra.TensorProduct.comm k K B).injective

lemma Algebra.isTranscendentalSeparable_of_perfectField [PerfectField k]
    {K : Type*} [Field K] [Algebra k K] : Algebra.IsTranscendentalSeparable k K := by
  sorry
