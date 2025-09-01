import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.NumberTheory.NumberField.Basic

open Algebra Module Submodule IntermediateField FractionalIdeal

open scoped nonZeroDivisors

-- set_option pp.proofs true

-- theorem FractionRing.algEquiv_symm_apply (A : Type*) [CommRing A]  (K : Type*) [CommRing K]
--     [Algebra A K] [IsFractionRing A K] (x : K) :
--     (FractionRing.algEquiv A K).symm x = 0 := by
--     --  (IsLocalization.map (Localization A⁰) (RingHom.id A) sorry) a := rfl
--   have := Localization.algEquiv_symm_apply (R := A) (M := A⁰) K x

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

-- Inline
theorem FractionRing.algEquiv_algebraMap_commutes (A B : Type*) [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] (K L : Type*) [Field K]
    [Field L] [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L] [Algebra A B]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L] [FaithfulSMul A B]
    (x : K) :
     algebraMap (FractionRing A) (FractionRing B) ((FractionRing.algEquiv A K).symm x) =
       (FractionRing.algEquiv B L).symm (algebraMap K L x) := by
  obtain ⟨r, s, -, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  simp_rw [map_div₀, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A B L,
    AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]

variable {A K C M : Type*} [CommRing A] [Field K] [CommRing C] [Field M] [Algebra K M]
  [Algebra A K] [IsFractionRing A K] [Algebra C M] [Algebra A M] [IsScalarTower A K M]
  {L₁ L₂ : IntermediateField K M} {B₁ B₂ : Type*} [CommRing B₁] [CommRing B₂] [Algebra B₁ L₁]
  [Algebra B₂ L₂] [Algebra A B₂] [Algebra B₁ C] [Algebra B₂ C] [Algebra B₁ M] [Algebra B₂ M]
  [IsScalarTower A B₂ L₂] [IsScalarTower B₁ C M] [IsScalarTower B₂ C M] [IsScalarTower B₁ L₁ M]
  [IsScalarTower B₂ L₂ M] [Algebra.IsSeparable K M] [FiniteDimensional K M]

variable (A C B₁ B₂) in
theorem traceDual_le_span_traceDual [IsLocalization (algebraMapSubmonoid B₂ A⁰) L₂]
    [Module.Free A B₂] [Module.Finite A B₂]
    (h₁ : L₁.LinearDisjoint L₂) (h₂ : L₁ ⊔ L₂ = ⊤) :
    (traceDual B₁ L₁ (1 : Submodule C M)).restrictScalars B₁ ≤
      span B₁ (algebraMap L₂ M '' (traceDual A K (1 : Submodule B₂ L₂))) := by
  intro x hx
  let b₂ := (Module.Free.chooseBasis A B₂).localizationLocalization K A⁰ L₂
  have h₂' : L₁.toSubalgebra ⊔ L₂.toSubalgebra = ⊤ := by
    simpa [sup_toSubalgebra_of_isAlgebraic_right] using congr_arg toSubalgebra h₂
  let bM : Basis _ L₁ M := h₁.basisOfBasisRight h₂' b₂.traceDual
  rw [← bM.sum_repr x]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  rsuffices ⟨c, hc⟩ : bM.repr x i ∈ (algebraMap B₁ L₁).range := by
    have : (h₁.basisOfBasisRight h₂' b₂).traceDual = bM := by
      refine (DFunLike.ext'_iff.trans Basis.traceDual_eq_iff).mpr fun _ _ ↦ ?_
      rw [h₁.basisOfBasisRight_apply, h₁.basisOfBasisRight_apply, traceForm_apply, ← map_mul,
        h₁.trace_algebraMap h₂, b₂.trace_traceDual_mul, MonoidWithZeroHom.map_ite_one_zero]
    rw [← this, (h₁.basisOfBasisRight h₂' b₂).traceDual_repr_apply x i]
    refine mem_traceDual.mp hx _ ?_
    rw [mem_one, h₁.basisOfBasisRight_apply, Basis.localizationLocalization_apply,
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply B₂ C M]
    exact ⟨_, rfl⟩
  rw [← hc, ← algebra_compatible_smul L₁]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  refine ⟨b₂.traceDual i, ?_, by rw [h₁.basisOfBasisRight_apply]⟩
  rw [SetLike.mem_coe, ← restrictScalars_mem A, traceDual_span_of_basis A _ b₂
    (by rw [Basis.localizationLocalization_span K A⁰ L₂]; ext; simp)]
  exact Submodule.subset_span <| Set.mem_range_self i

variable [IsDomain A] [IsDomain B₁]
  [IsIntegrallyClosed A] [IsIntegrallyClosed B₁] [IsDedekindDomain B₂] [IsDedekindDomain C]
  [IsFractionRing B₁ L₁] [IsFractionRing B₂ L₂] [IsFractionRing C M]
  [IsIntegralClosure B₂ A L₂] [IsIntegralClosure C B₂ M] [IsIntegralClosure C B₁ M]
  [NoZeroSMulDivisors B₁ C] [NoZeroSMulDivisors B₂ C]

variable [Algebra A B₁] [IsDedekindDomain B₁] [NoZeroSMulDivisors A B₁]
  [Algebra A C] [IsScalarTower A B₁ L₁] [IsScalarTower A C M] [IsIntegralClosure B₁ A L₁]
  [IsIntegralClosure C A M] [NoZeroSMulDivisors A C] [IsScalarTower K L₂ M] [IsScalarTower K L₁ M]

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable (A C B₁ B₂) in
theorem traceDual_eq_span_traceDual [IsDedekindDomain A] [Module.Finite A B₂] [Module.Free A B₂]
    [NoZeroSMulDivisors A B₂] (h₁ : L₁.LinearDisjoint L₂) (h₂ : L₁ ⊔ L₂ = ⊤)
    (h₃ : IsCoprime ((differentIdeal A B₁).map (algebraMap B₁ C))
      ((differentIdeal A B₂).map (algebraMap B₂ C))) :
    span B₁ (algebraMap L₂ M '' (traceDual A K (1 : Submodule B₂ L₂))) =
      (traceDual B₁ L₁ (1 : Submodule C M)).restrictScalars B₁ := by
  apply le_antisymm
  · suffices span C (algebraMap L₂ M '' (traceDual A K (1 : Submodule B₂ L₂))) ≤
        traceDual B₁ L₁ (1 : Submodule C M) by
      refine SetLike.coe_subset_coe.mp (subset_trans ?_ this)
      rw [← Submodule.span_span_of_tower B₁ C]
      exact Submodule.subset_span
    have := IsIntegralClosure.isLocalization B₂ L₂ M C
    rw [← coe_dual_one, coeToSet_coeToSubmodule, ← coe_extended_eq_span_algebraMap, ← coe_dual_one,
      coe_le_coe, ← inv_inv (dual B₁ L₁ 1), ← le_inv_comm (inv_ne_zero (by simp)),
      ← extended_inv _ (by simp), ← coeIdeal_differentIdeal A K, ← coeIdeal_differentIdeal B₁ L₁,
      extended_coeIdeal_eq_map_algebraMap L₂ M, coeIdeal_le_coeIdeal' _ le_rfl, ← Ideal.dvd_iff_le]
    · have : Module.Finite A B₁ := by
        apply IsIntegralClosure.finite A K L₁
      have : Module.Finite A C := by
        apply IsIntegralClosure.finite A K M
      have : Module.Finite B₁ C := by
        apply IsIntegralClosure.finite B₁ L₁ M
      have : Module.Finite B₂ C := by
        apply IsIntegralClosure.finite B₂ L₂ M
      have : IsScalarTower A B₁ C := by
        refine IsScalarTower.of_algebraMap_eq ?_
        intro x
        apply FaithfulSMul.algebraMap_injective C M
        have : IsScalarTower A L₁ M := by
          refine IsScalarTower.to₁₃₄ A K L₁ M
        have : IsScalarTower A B₁ M := by
          refine IsScalarTower.to₁₂₄ A B₁ L₁ M
        rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
          ← IsScalarTower.algebraMap_apply]
      have : IsScalarTower A B₂ C := by
        refine IsScalarTower.of_algebraMap_eq ?_
        intro x
        apply FaithfulSMul.algebraMap_injective C M
        have : IsScalarTower A L₂ M := by
          refine IsScalarTower.to₁₃₄ A K L₂ M
        have : IsScalarTower A B₂ M := by
          refine IsScalarTower.to₁₂₄ A B₂ L₂ M
        rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
          ← IsScalarTower.algebraMap_apply]
      have : Algebra.IsSeparable (FractionRing A) (FractionRing C) := by
        refine Algebra.IsSeparable.of_equiv_equiv (FractionRing.algEquiv A K).symm.toRingEquiv
          (FractionRing.algEquiv C M).symm.toRingEquiv ?_
        ext x
        exact FractionRing.algEquiv_algebraMap_commutes A C K M x
      have eq₁ := differentIdeal_eq_differentIdeal_mul_differentIdeal A B₂ C
      have eq₂ := differentIdeal_eq_differentIdeal_mul_differentIdeal A B₁ C
      have := eq₁.symm.trans eq₂
      exact h₃.symm.dvd_of_dvd_mul_right (dvd_of_mul_left_eq _ this)
    · exact extended_ne_zero _ _ (FaithfulSMul.algebraMap_injective _ _) (by simp)
  · have := IsIntegralClosure.isLocalization A K L₂ B₂
    exact traceDual_le_span_traceDual A C B₁ B₂ h₁ h₂

variable (A C B₁ B₂) in
theorem span_eq_range
    [IsDedekindDomain A]
    [IsScalarTower A L₂ M]
    [IsScalarTower A B₁ M]
    [Module.Free A B₂]
    [Module.Finite A B₂]
    [NoZeroSMulDivisors A B₂]
    (h₁ : L₁.LinearDisjoint L₂) (h₂ : L₁ ⊔ L₂ = ⊤)
    (h₃ : IsCoprime ((differentIdeal A B₁).map (algebraMap B₁ C))
      ((differentIdeal A B₂).map (algebraMap B₂ C)))
    {ι : Type*} (b : Basis ι K L₂)
    (hb : span A (Set.range b) = (1 : Submodule B₂ L₂).restrictScalars A) :
    span B₁ (Set.range (algebraMap L₂ M ∘ b)) =
      LinearMap.range (IsScalarTower.toAlgHom B₁ C M) := by
  classical
  have : Finite ι := Module.Finite.finite_basis b
  have h_main : (traceDual B₁ L₁ (1 : Submodule C M)).restrictScalars B₁ =
      span B₁ (algebraMap L₂ M '' (traceDual A K (1 : Submodule B₂ L₂))) :=
    (traceDual_eq_span_traceDual A C B₁ B₂ h₁ h₂ h₃).symm
  convert congr_arg (Submodule.restrictScalars B₁) <|
    congr_arg coeToSubmodule <| (1 : FractionalIdeal C⁰ M).dual_dual B₁ L₁
  · rw [coe_dual _ _ (by simp), coe_dual_one]
    rw [restrictScalars_traceDual, h_main]
    have := Submodule.traceDual_span_of_basis A (1 : Submodule B₂ L₂) b ?_
    · rw [← Submodule.coe_restrictScalars A, this, ← IsScalarTower.coe_toAlgHom' A L₂ M,
        ← map_coe, map_span, span_span_of_tower, IsScalarTower.coe_toAlgHom', ← Set.range_comp]
      have h₂' : L₁.toSubalgebra ⊔ L₂.toSubalgebra = ⊤ := by
        simpa [sup_toSubalgebra_of_isAlgebraic_right] using congr_arg toSubalgebra h₂
      have : algebraMap L₂ M ∘ b.traceDual = (h₁.basisOfBasisRight h₂' b).traceDual := by
        rw [eq_comm, Basis.traceDual_eq_iff]
        intro i j
        simp only [Function.comp_apply, h₁.basisOfBasisRight_apply, traceForm_apply]
        rw [← map_mul, h₁.trace_algebraMap h₂]
        rw [b.trace_traceDual_mul i j, MonoidWithZeroHom.map_ite_one_zero]
      rw [this, (traceForm L₁ M).dualSubmodule_span_of_basis (traceForm_nondegenerate L₁ M),
        ← Basis.traceDual_def, Basis.traceDual_traceDual]
      congr!
      ext
      rw [Function.comp_apply, h₁.basisOfBasisRight_apply]
    · rw [hb]
  · ext; simp

open NumberField

example {K : Type*} [Field K] [NumberField K] (E F : IntermediateField ℚ K)
    (h₁ : E.LinearDisjoint F)
    (h₂ : IsCoprime ((differentIdeal ℤ (𝓞 E)).map (algebraMap (𝓞 E) (𝓞 K)))
      ((differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 K)))) (α : 𝓞 E) (β : 𝓞 F)
    (hα : Algebra.adjoin ℤ {α} = ⊤)
    (hβ : Algebra.adjoin ℤ {β} = ⊤) :
    Algebra.adjoin ℤ {algebraMap (𝓞 E) (𝓞 K) α, algebraMap (𝓞 F) (𝓞 K) β} = ⊤ := by
  sorry
