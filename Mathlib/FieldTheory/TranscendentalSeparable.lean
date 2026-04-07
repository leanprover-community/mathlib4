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
    Algebra.IsSeparable (Algebra.adjoin k (Set.range f)) K

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

variable (k : Type*) [Field k]

lemma tensorProduct_isReduced_of_isTranscendentalSeparable_of_isDomain
    (S : Type*) [CommRing S] [Algebra k S] [IsDomain S]
    (K : Type*) [Field K] [Algebra k K] [Algebra.IsSeparablyGenerated k K]
    [Algebra.EssFiniteType k K] : IsReduced (TensorProduct k K S) := by
  sorry

lemma tensorProduct_isReduced_of_isTranscendentalSeparable_of_isReduced_of_essFiniteType
    (S : Type*) [CommRing S] [Algebra k S] [Algebra.FiniteType k S] [IsReduced S]
    (K : Type*) [Field K] [Algebra k K] [Algebra.IsSeparablyGenerated k K]
    [Algebra.EssFiniteType k K] : IsReduced (TensorProduct k K S) := by
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
    exact tensorProduct_isReduced_of_isTranscendentalSeparable_of_isDomain k _ K
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
    have := tensorProduct_isReduced_of_isTranscendentalSeparable_of_isReduced_of_essFiniteType k B L
    exact isReduced_of_injective _ (Algebra.TensorProduct.comm k B L).injective
  exact isReduced_of_injective _ (Algebra.TensorProduct.comm k K B).injective

lemma Algebra.isTranscendentalSeparable_of_perfectField [PerfectField k]
    {K : Type*} [Field K] [Algebra k K] : Algebra.IsTranscendentalSeparable k K := by
  sorry
