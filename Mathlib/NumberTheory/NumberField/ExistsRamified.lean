/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# Every number field has a ramified prime over `ℚ`
...except `ℚ` itself.

This is a trivial corollary of `NumberField.not_dvd_discr_iff_forall_pow_mem` and
`NumberField.abs_discr_gt_two` but is placed in a separate file to avoid large imports.

-/

@[expose] public section

variable {K 𝒪 : Type*} [Field K] [NumberField K] [CommRing 𝒪] [Algebra 𝒪 K]
variable [IsIntegralClosure 𝒪 ℤ K]

/-- If `K` is a number field with positive rank, then there exists some maximal ideal of `𝓞 K`
that is ramified over `ℤ`. -/
lemma NumberField.exists_not_isUramifiedAt_int (H : Module.finrank ℚ K ≠ 1) :
    ∃ (P : Ideal 𝒪) (_ : P.IsMaximal), P ≠ ⊥ ∧ ¬ Algebra.IsUnramifiedAt ℤ P := by
  have := (IsIntegralClosure.algebraMap_injective 𝒪 ℤ K).isDomain
  have := IsIntegralClosure.isDedekindDomain ℤ ℚ K 𝒪
  have := CharZero.of_module (R := 𝒪) K
  have := Module.finrank_pos (R := ℚ) (M := K)
  have := NumberField.abs_discr_gt_two (K := K) (by lia)
  obtain ⟨q, hq, hqK⟩ := Int.exists_prime_and_dvd (n := discr K) (by zify; linarith)
  have := (not_dvd_discr_iff_forall_mem K 𝒪 hq).not_right.mp hqK
  push_neg at this
  obtain ⟨P, hP, h, H⟩ := this
  exact ⟨P, hP.isMaximal (by aesop), by aesop, H⟩

/-- Any number field that is unramified over `ℚ` has rank `1`. -/
lemma NumberField.finrank_eq_one_of_unramified [Algebra.Unramified ℤ 𝒪] :
    Module.finrank ℚ K = 1 := by
  by_contra H
  obtain ⟨P, _, _, H⟩ := NumberField.exists_not_isUramifiedAt_int (𝒪 := 𝒪) H
  exact H inferInstance

open scoped NumberField

/-- If `K` is a number field with positive rank, then there exists some maximal ideal of `𝓞 K`
that is ramified over `ℤ`. -/
lemma NumberField.finrank_eq_one_of_isUnramifiedAt
    [Module.Finite ℤ 𝒪] [Algebra.Unramified ℤ 𝒪] [IsDomain 𝒪] [FaithfulSMul ℤ 𝒪] :
    Function.Bijective (algebraMap ℤ 𝒪) := by
  suffices Function.Surjective (algebraMap ℤ 𝒪) from ⟨FaithfulSMul.algebraMap_injective _ _, this⟩
  wlog _ : IsIntegrallyClosed 𝒪
  · let K := FractionRing 𝒪
    letI inst : Algebra ℤ K := Ring.toIntAlgebra K
    have inst : NumberField K := sorry
    let f : 𝒪 →+* 𝓞 K := RingHom.codRestrict (algebraMap 𝒪 K) _ fun x ↦
      (Algebra.IsIntegral.isIntegral x).algebraMap
    have hf : Function.Injective f :=
      RingHom.injective_codRestrict.mpr (FaithfulSMul.algebraMap_injective _ _)
    let inst := f.toAlgebra
    have inst : IsScalarTower 𝒪 (𝓞 K) K := .of_algebraMap_eq' rfl
    have inst : IsLocalization ((IsUnit.submonoid _).comap f) (𝓞 K) := by
      refine ⟨fun x ↦ x.2, fun ⟨z, hz⟩ ↦ ?_, ?_⟩; swap
      · simpa [RingHom.algebraMap_toAlgebra', hf.eq_iff] using
          ⟨1, ((IsUnit.submonoid _).comap f).one_mem⟩
      obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := 𝒪) z
      simp only [mem_nonZeroDivisors_iff_ne_zero, ne_eq] at hy
      suffices ∃ a b, IsUnit (f b) ∧ x * b = a * y by
        simpa [RingOfIntegers.ext_iff, ← IsScalarTower.algebraMap_apply, IsUnit.mem_submonoid_iff,
          div_mul_eq_mul_div₀, div_eq_iff, hy, ← map_mul (algebraMap 𝒪 K), -map_mul,
          map_mul (algebraMap (𝓞 K) K)]
      sorry
    have inst : Algebra.FormallyUnramified 𝒪 (𝓞 K) := .of_restrictScalars _ _ K
    have inst : Algebra.Unramified ℤ (𝓞 K) := sorry
    have := this (𝒪 := 𝓞 K) inferInstance
    simp only [IsScalarTower.algebraMap_eq ℤ 𝒪 (𝓞 K), RingHom.coe_comp] at this
    exact .of_comp_left this hf


attribute [local simp] Ideal.span_le in
/-- If `K` is a number field with positive rank such that `K/ℚ` is galois, then there exists
some rational prime `p : ℤ` such that every prime of `K` over `P` is unramified. -/
lemma NumberField.exists_not_isUramifiedAt_int_of_isGalois [IsGalois ℚ K]
    (H : 1 < Module.finrank ℚ K) :
    ∃ p : ℕ, p.Prime ∧ ∀ (P : Ideal 𝒪) (_ : P.IsPrime), ↑p ∈ P → ¬ Algebra.IsUnramifiedAt ℤ P := by
  have := (IsIntegralClosure.algebraMap_injective 𝒪 ℤ K).isDomain
  have := IsIntegralClosure.isDedekindDomain ℤ ℚ K 𝒪
  have := IsIntegralClosure.isFractionRing_of_finite_extension ℤ ℚ K 𝒪
  have := IsIntegralClosure.finite ℤ ℚ K 𝒪
  have := CharZero.of_module (R := 𝒪) K
  let : MulSemiringAction Gal(K/ℚ) 𝒪 := IsIntegralClosure.MulSemiringAction ℤ ℚ K 𝒪
  have := IsGaloisGroup.of_isFractionRing Gal(K/ℚ) ℤ 𝒪 ℚ K
  obtain ⟨P, _, hP, hP'⟩ := NumberField.exists_not_isUramifiedAt_int (𝒪 := 𝒪) H
  obtain ⟨p, hp : _ = Ideal.span _⟩ := IsPrincipalIdealRing.principal (P.under ℤ)
  have hp0 : p ≠ 0 := fun hp0 ↦ hP (Ideal.eq_bot_of_comap_eq_bot (hp.trans (by aesop)))
  have : Prime p := by rw [← Ideal.span_singleton_prime hp0, ← hp]; infer_instance
  refine ⟨p.natAbs, Int.prime_iff_natAbs_prime.mp this, fun Q _ hQ ↦ ?_⟩
  replace hQ : (p : 𝒪) ∈ Q := Q.mem_of_dvd
    (map_dvd (algebraMap _ _) p.associated_natAbs.symm.dvd) (by simpa using hQ)
  have : .span {p} = Ideal.under ℤ Q := (Ideal.IsPrime.isMaximal (hp ▸ inferInstance) (by simpa))
    |>.eq_of_le Ideal.IsPrime.ne_top' (by simpa)
  rwa [Algebra.isUnramifiedAt_iff_of_isDedekindDomain (by aesop),
    ← Ideal.ramificationIdxIn_eq_ramificationIdx _ _ Gal(K/ℚ), ← this, ← hp,
    Ideal.ramificationIdxIn_eq_ramificationIdx _ P Gal(K/ℚ),
    ← Algebra.isUnramifiedAt_iff_of_isDedekindDomain hP]
