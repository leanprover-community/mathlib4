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

lemma isReduced_injective_to_prod_localizations {S : Type*} [CommRing S] [IsReduced S] :
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

set_option backward.isDefEq.respectTransparency false in
/-- If `R ⊗[k] S` is nonreduced, then this already occurs on finitely generated `k`-subalgebras
of `R` and `S`. -/
lemma exists_subalgebra_fg_of_not_isReduced_tensorProduct
    (k R S : Type*) [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (h : ¬ IsReduced (R ⊗[k] S)) :
    ∃ R' : Subalgebra k R, ∃ S' : Subalgebra k S, R'.FG ∧ S'.FG ∧ ¬ IsReduced (R' ⊗[k] S') := by
  obtain ⟨z, hz_ne, ⟨n, hn⟩⟩ := exists_isNilpotent_of_not_isReduced h
  rcases TensorProduct.Algebra.exists_of_fg z with ⟨R', fgR, ⟨y, hy⟩⟩
  rcases TensorProduct.Algebra.exists_of_fg ((TensorProduct.comm k _ _) y) with ⟨S', fgS, ⟨x, hx⟩⟩
  use R', S', fgR, fgS
  rw [isReduced_iff, not_forall₂]
  use (TensorProduct.comm k _ _) x
  refine exists_prop.mpr ⟨?_, ?_⟩
  · use n
    have hx' : (Algebra.TensorProduct.rTensor _ S'.val) x =
      (Algebra.TensorProduct.comm k _ _) y := hx
    have : x ^ n = 0 := by
      rw [← map_eq_zero_iff (Algebra.TensorProduct.rTensor R' S'.val)
        (Module.Flat.rTensor_preserves_injective_linearMap S'.val.toLinearMap
        Subtype.val_injective), map_pow, hx', ← map_pow,
        map_eq_zero_iff _ (AlgEquiv.injective _), ← map_eq_zero_iff
        (Algebra.TensorProduct.rTensor S R'.val) (Module.Flat.rTensor_preserves_injective_linearMap
        R'.val.toLinearMap Subtype.val_injective), map_pow, ← hn, ← hy]
      rfl
    rwa [← map_eq_zero_iff (Algebra.TensorProduct.comm k _ _) (AlgEquiv.injective _), map_pow]
      at this
  · rw [LinearEquiv.map_eq_zero_iff]
    by_contra eq0
    rw [eq0, map_zero, eq_comm, LinearEquiv.map_eq_zero_iff] at hx
    simp [hx, map_zero, eq_comm, hz_ne] at hy

lemma IsReduced.tensorProduct_of_forall_fg_intermediateField {k : Type*} [Field k]
    {S : Type*} [CommRing S] [Algebra k S] {K : Type*} [Field K] [Algebra k K]
    (h : ∀ (L : IntermediateField k K), L.FG → IsReduced (TensorProduct k S L)) :
    IsReduced (TensorProduct k S K) := by
  refine IsReduced.tensorProduct_of_flat_of_forall_fg (fun B ⟨T, hT⟩ ↦ ?_)
  have := h _ (IntermediateField.fg_adjoin_finset T)
  have le : B ≤ (IntermediateField.adjoin k (T : Set K)).toSubalgebra := by
    simp [← hT, Algebra.adjoin_le_iff]
  have : Function.Injective (Algebra.TensorProduct.lTensor S (Subalgebra.inclusion le)) :=
    Module.Flat.lTensor_preserves_injective_linearMap (Subalgebra.inclusion le).toLinearMap
      (Subalgebra.inclusion_injective le)
  exact isReduced_of_injective _ this

variable {k : Type*} [Field k]

lemma tensorProduct_isReduced_of_isTranscendentalSeparable_of_isDomain
    {S : Type*} [CommRing S] [Algebra k S] [Algebra.FiniteType k S] [IsDomain S]
    {K : Type*} [Field K] [Algebra k K] [Algebra.IsTranscendentalSeparable k K]
    [Algebra.EssFiniteType k K] : IsReduced (TensorProduct k K S) := by
  sorry

lemma tensorProduct_isReduced_of_isTranscendentalSeparable_of_isReduced
    {S : Type*} [CommRing S] [Algebra k S] [Algebra.FiniteType k S] [IsReduced S]
    {K : Type*} [Field K] [Algebra k K] [Algebra.IsTranscendentalSeparable k K]
    [Algebra.EssFiniteType k K] : IsReduced (TensorProduct k K S) := by
  sorry

lemma Algebra.isTranscendentalSeparable_of_perfectField [PerfectField k]
    {K : Type*} [Field K] [Algebra k K] : Algebra.IsTranscendentalSeparable k K := by
  sorry
