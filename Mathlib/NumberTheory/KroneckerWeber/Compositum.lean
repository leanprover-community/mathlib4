import Mathlib
import Mathlib.NumberTheory.KroneckerWeber.DedekindDomain

variable {F K₁ K₂ L : Type*} [Field F] [Field K₁] [Field K₂] [Field L]
variable {A B₁ B₂ C : Type*} [CommRing A] [CommRing B₁] [CommRing B₂] [CommRing C]
variable [Algebra A F] [Algebra B₁ K₁] [Algebra B₂ K₂] [Algebra C L]
variable [IsFractionRing A F] [IsFractionRing B₁ K₁] [IsFractionRing B₂ K₂] [IsFractionRing C L]
variable [Algebra F K₁] [Algebra F K₂] [Algebra K₁ L] [Algebra K₂ L] [Algebra F L]
variable [IsScalarTower F K₁ L] [IsScalarTower F K₂ L]
variable [Algebra A B₁] [Algebra A B₂] [Algebra B₁ C] [Algebra B₂ C] [Algebra A C]
variable [IsScalarTower A B₁ C] [IsScalarTower A B₂ C]
variable [IsDomain A] [IsDedekindDomain B₁] [NoZeroSMulDivisors A B₁]
variable [IsDomain B₂] [IsDedekindDomain C] [NoZeroSMulDivisors B₂ C] [IsIntegrallyClosed B₂]
variable [Algebra.IsIntegral B₂ C] [NoZeroSMulDivisors B₁ C]
variable [IsIntegrallyClosed A] [Algebra.IsIntegral A B₁]


attribute [local instance 10000] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

open nonZeroDivisors in
lemma Field.exists_adjoin_algebraMap_eq_top
    (A K L B : Type*) [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K] [Field L]
    [CommRing B] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [Algebra B L]
    [IsIntegralClosure B A L] [Algebra A B] [IsScalarTower A B L]
    [IsDomain A] [Algebra.IsSeparable K L] [FiniteDimensional K L] :
    ∃ x, Algebra.adjoin K {algebraMap B L x} = ⊤ := by
  obtain ⟨x, hx⟩ := Field.exists_primitive_element K L
  apply_fun IntermediateField.toSubalgebra at hx
  rw [IntermediateField.top_toSubalgebra, IntermediateField.adjoin_simple_toSubalgebra_of_integral
    (Algebra.IsIntegral.isIntegral _)] at hx
  have := IsIntegralClosure.isLocalization_of_isSeparable A K L B
  obtain ⟨x, ⟨_, s, hs, rfl⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid B A⁰) x
  refine ⟨x, ?_⟩
  rw [← top_le_iff, ← hx, Algebra.adjoin_le_iff, Set.singleton_subset_iff]
  convert_to algebraMap _ _ x * (algebraMap K L (1 / algebraMap A K s)) ∈ _
  · rw [IsLocalization.mk'_eq_iff_eq_mul]
    have : algebraMap A L s ≠ 0 := by
      rw [IsScalarTower.algebraMap_apply A K]
      simpa using hs
    simp [← IsScalarTower.algebraMap_apply, this]
  · exact mul_mem (Algebra.self_mem_adjoin_singleton _ _) (Subalgebra.algebraMap_mem _ _)

open nonZeroDivisors in
lemma foobar (H : (algebraMap (FractionRing B₁) (FractionRing C)).fieldRange ⊔
      (algebraMap (FractionRing B₂) (FractionRing C)).fieldRange = ⊤) :
    differentIdeal A B₁ ≤ (differentIdeal B₂ C).comap (algebraMap B₁ C) := by

  -- intro x hx y hy


  -- show (differentIdeal A B₁).restrictScalars A ≤
  --   ((differentIdeal B₂ C).restrictScalars A).comap (IsScalarTower.toAlgHom A B₁ C).toLinearMap
  rw [← Ideal.map_le_iff_le_comap]
  let F := FractionRing A
  let L := FractionRing C
  let K₁ := FractionRing B₁
  let K₂ := FractionRing B₂
  have : Algebra.IsSeparable K₂ L := sorry
  have : Module.Finite K₂ L := sorry
  have : Algebra.IsSeparable F K₁ := sorry
  have : Module.Finite F K₁ := sorry
  obtain ⟨x, hx⟩ := Field.exists_adjoin_algebraMap_eq_top A F K₁ B₁
  have := conductor_mul_differentIdeal A F K₁ x hx
  apply le_of_mul_le_mul_left (a := (conductor A x).map (algebraMap B₁ C))
  · refine (le_of_le_of_eq ?_
      (conductor_mul_differentIdeal B₂ K₂ L (algebraMap _ C x) ?_).symm).trans ?_
    · rw [← Ideal.map_mul, conductor_mul_differentIdeal A F K₁ x hx, Ideal.map_span,
        Set.image_singleton, Ideal.span_singleton_le_span_singleton]
      sorry
    · sorry
    · refine mul_le_mul_right' ?_ (differentIdeal B₂ C)
      intro a ha

  · sorry
  -- have := IsIntegralClosure.isLocalization_of_isSeparable A F K₁ B₁
  -- obtain ⟨x, s, rfl⟩ :=
  --   IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid B₁ A⁰) x
  -- have : Module.Finite K₂ L := sorry
  -- refine (Submodule.map_le_map_iff_of_injective (f := (IsScalarTower.toAlgHom A C L).toLinearMap)
  --   (IsLocalization.injective _ le_rfl) _ _).mp ?_
  -- -- rw [← Submodule.map_comp]
  -- convert_to ((IsLocalization.coeSubmodule K₁ (differentIdeal A B₁)).map
  --   (IsScalarTower.toAlgHom B₁ K₁ L).toLinearMap).restrictScalars A ≤
  --   (IsLocalization.coeSubmodule L (differentIdeal B₂ C)).restrictScalars A
  -- · simp_rw [IsLocalization.coeSubmodule, ← Submodule.map_comp]
  --   ext
  --   simp [← IsScalarTower.algebraMap_apply]
  -- rw [coeSubmodule_differentIdeal (K := F), coeSubmodule_differentIdeal (K := K₂),
  --   Submodule.restrictScalars_div]
