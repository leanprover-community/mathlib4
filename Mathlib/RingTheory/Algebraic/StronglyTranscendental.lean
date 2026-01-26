/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.LocalProperties.Reduced

/-!
# Strongly transcendental elements

In this file, we provide basic properties for strongly transcendental elements in an algebra.
This is a relatively niche notion, but is useful for proving Zarkisi's main theorem.

## Reference
- https://stacks.math.columbia.edu/tag/00PZ

-/

@[expose] public section

open scoped TensorProduct nonZeroDivisors

open Polynomial

variable {R S T : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]

variable (R) in
/-- We say that `x : S` is strongly transcendental over `R` if
forall `u : S` and all `p : R[X]`, `p(x) * u = 0 → p * u = 0`.
If `S` is a domain, and `R ⊆ S`, this is equivalent to the image of `x` in `Frac(S)` being
transcendental over `R`. See `IsStronglyTranscendental.iff_of_isFractionRing`.
-/
@[stacks 00PZ]
def IsStronglyTranscendental (x : S) : Prop :=
  ∀ u : S, ∀ p : R[X], p.aeval x * u = 0 → p.map (algebraMap R S) * C u = 0

lemma IsStronglyTranscendental.transcendental {x : S} (h : IsStronglyTranscendental R x)
    [FaithfulSMul R S] : Transcendental R x :=
  transcendental_iff.mpr fun p hp ↦ Polynomial.ext <|
    by simpa [Algebra.smul_def, hp, Polynomial.ext_iff] using h 1 p

lemma isStronglyTranscendental_iff_of_field {K : Type*} [Field K] [Algebra R K] [FaithfulSMul R K]
    {x : K} : IsStronglyTranscendental R x ↔ Transcendental R x := by
  refine ⟨fun h ↦ h.transcendental, fun h ↦ ?_⟩
  simpa [IsStronglyTranscendental, or_imp, forall_and, @forall_comm K, ← subsingleton_iff_forall_eq,
    not_subsingleton, ext_iff, forall_or_left, ← imp_iff_or_not, transcendental_iff] using h

lemma IsStronglyTranscendental.of_map {x : S} {f : S →ₐ[R] T} (hf : Function.Injective f)
    (h : IsStronglyTranscendental R (f x)) :
    IsStronglyTranscendental R x := by
  refine fun u p hp ↦ ?_
  have := h (f u) p (by rw [aeval_algHom_apply, ← map_mul, hp, map_zero])
  rwa [← f.comp_algebraMap, ← map_map, ← f.coe_toRingHom, ← map_C, ← Polynomial.map_mul,
    ← coe_mapRingHom, map_eq_zero_iff] at this
  exact map_injective f.toRingHom hf

lemma IsStronglyTranscendental.of_isLocalization [Algebra S T] (M : Submonoid S)
    [IsLocalization M T] [IsScalarTower R S T]
    {x : S} (h : IsStronglyTranscendental R x) :
    IsStronglyTranscendental R (algebraMap S T x) := by
  refine fun u p hp ↦ ?_
  obtain ⟨u, s, rfl⟩ := IsLocalization.exists_mk'_eq M u
  obtain ⟨a, haM, e⟩ : ∃ a ∈ M, a * ((aeval x) p * u) = 0 := by
    simpa [aeval_algebraMap_apply, ← Algebra.smul_def, IsLocalization.smul_mk',
      IsLocalization.mk'_eq_zero_iff] using hp
  have : p.map (algebraMap R T) * C (a • algebraMap S T u) = 0 := by
    simpa [map_map, ← IsScalarTower.algebraMap_eq, Algebra.smul_def] using
      congr(map (algebraMap S T) $(h (a * u) p (by linear_combination e)))
  refine ((IsLocalization.map_units T (⟨a, haM⟩ * s)).map C).mul_right_cancel ?_
  simpa [mul_assoc, ← map_mul, mul_comm _ (algebraMap _ _ _), ← Algebra.smul_def, mul_smul]

lemma IsStronglyTranscendental.of_isLocalization_left [Algebra S T] (M : Submonoid R)
    [IsLocalization M S] [IsScalarTower R S T]
    {x : T} (h : IsStronglyTranscendental R x) :
    IsStronglyTranscendental S x := by
  intro t p hp
  obtain ⟨a, ha⟩ := IsLocalization.integerNormalization_map_to_map M p
  have H : aeval x (IsLocalization.integerNormalization M p) = a.1 • aeval x p := by
    simpa [AlgHom.map_smul_of_tower] using congr(aeval x $ha)
  have := h t (IsLocalization.integerNormalization M p) (by simp [H, hp])
  rw [IsScalarTower.algebraMap_eq R S T, ← map_map, ha] at this
  rw [← (((IsLocalization.map_units S a).map (algebraMap S T)).map C).mul_right_inj]
  simpa [Algebra.smul_def, mul_assoc] using this

lemma IsStronglyTranscendental.restrictScalars [Algebra S T] [IsScalarTower R S T]
    {x : T} (h : IsStronglyTranscendental S x) :
    IsStronglyTranscendental R x := by
  intro t p hp
  simpa [map_map, ← IsScalarTower.algebraMap_eq] using h t (p.map (algebraMap R S)) (by simpa)

lemma IsStronglyTranscendental.of_surjective_left [Algebra S T] [IsScalarTower R S T]
    {x : T} (h : IsStronglyTranscendental R x) (H : Function.Surjective (algebraMap R S)) :
    IsStronglyTranscendental S x := by
  intro t p hp
  obtain ⟨p, rfl⟩ := map_surjective _ H p
  simpa [map_map, ← IsScalarTower.algebraMap_eq] using h t p (by simpa using hp)

lemma IsStronglyTranscendental.iff_of_isLocalization [Algebra S T] {M : Submonoid S}
    (hM : M ≤ S⁰) [IsLocalization M T] [IsScalarTower R S T]
    {x : S} : IsStronglyTranscendental R (algebraMap S T x) ↔ IsStronglyTranscendental R x :=
  ⟨fun h ↦ .of_map (f := IsScalarTower.toAlgHom R S T) (IsLocalization.injective _ hM) h,
    fun h ↦ .of_isLocalization M h⟩

lemma IsStronglyTranscendental.iff_of_isFractionRing (K : Type*) [Field K] [Algebra R K]
    [Algebra S K] [IsScalarTower R S K] [FaithfulSMul R S] [IsFractionRing S K] {x : S} :
    IsStronglyTranscendental R x ↔ Transcendental R (algebraMap S K x) := by
  have : FaithfulSMul R K := .trans R S K
  rw [← IsStronglyTranscendental.iff_of_isLocalization (T := K) le_rfl,
    isStronglyTranscendental_iff_of_field]

lemma IsStronglyTranscendental.of_transcendental {K : Type*} [Field K] [Algebra R K]
    [Algebra S K] [IsScalarTower R S K] [FaithfulSMul R S] [FaithfulSMul S K]
    {x : S} (H : Transcendental R (algebraMap S K x)) :
    IsStronglyTranscendental R x := by
  have : FaithfulSMul R K := .trans R S K
  rw [← isStronglyTranscendental_iff_of_field] at H
  exact .of_map (f := IsScalarTower.toAlgHom R S K) (FaithfulSMul.algebraMap_injective _ _) H

@[stacks 00Q0]
lemma isStronglyTranscendental_mk_of_mem_minimalPrimes [IsReduced S]
    {x : S} (hx : IsStronglyTranscendental R x) (q : Ideal S) (hq : q ∈ minimalPrimes S) :
    IsStronglyTranscendental R (Ideal.Quotient.mk q x) := by
  refine Ideal.Quotient.mk_surjective.forall.mpr fun u p e ↦ ?_
  rw [← Ideal.Quotient.algebraMap_eq, aeval_algebraMap_apply, Ideal.Quotient.algebraMap_eq,
    ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at e
  have := hq.1.1
  have : Ring.KrullDimLE 0 (Localization.AtPrime q) := .of_isLocalization _ hq _
  let : Field (Localization.AtPrime q) := Ring.KrullDimLE.isField_of_isReduced.toField
  obtain ⟨⟨m, hmq⟩, hm⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl (Localization.AtPrime q)
    (aeval x p * u)).mp (by rw [← Ideal.mem_bot, ← IsLocalRing.maximalIdeal_eq_bot,
      ← Localization.AtPrime.map_eq_maximalIdeal]; exact Ideal.mem_map_of_mem _ e)
  ext i
  simp only [coeff_mul_C, coeff_map, coeff_zero, ← Ideal.Quotient.mk_algebraMap, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem]
  have : algebraMap R S (p.coeff i) * u * m = 0 := by
    simpa [← mul_assoc] using congr(($(hx (u * m) p (by linear_combination hm))).coeff i)
  exact (Ideal.IsPrime.mem_or_mem_of_mul_eq_zero ‹_› (by linear_combination this)).resolve_left hmq
