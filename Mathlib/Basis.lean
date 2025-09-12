import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.NumberTheory.NumberField.Basic

open Algebra Module Submodule IntermediateField FractionalIdeal

section misc

theorem Algebra.adjoin_trans {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (s : Set S) (t : Set T) (hS : adjoin R s = ⊤) :
    (adjoin S t).restrictScalars R = adjoin R ((algebraMap S T '' s) ∪ t) := by
  have := congr_arg (Subalgebra.map (IsScalarTower.toAlgHom R S T)) hS
  rw [Algebra.map_top, AlgHom.map_adjoin, IsScalarTower.coe_toAlgHom'] at this
  rw [adjoin_union_eq_adjoin_adjoin, this, ← IsScalarTower.adjoin_range_toAlgHom]

-- This probably true more generally and already proved somewhere...
attribute [local instance] FractionRing.liftAlgebra in
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

end misc

noncomputable section PowerBasis

/--
Docstring
-/
def PowerBasis.ofBasis {R S : Type*} [CommRing R] [Ring S] [Algebra R S] {ι : Type*} [Fintype ι]
    (B : Basis ι R S) {x : S} (e : ι ≃ Fin (Fintype.card ι)) (hx : ∀ i, B i = x ^ (e i : ℕ)) :
    PowerBasis R S := ⟨x, Fintype.card ι, B.reindex e, fun i ↦ by simp [hx]⟩

@[simp]
theorem PowerBasis.ofBasis_gen {R S : Type*} [CommRing R] [Ring S] [Algebra R S] {ι : Type*}
    [Fintype ι] (B : Basis ι R S) {x : S} (e : ι ≃ Fin (Fintype.card ι))
    (hx : ∀ i, B i = x ^ (e i : ℕ)) : (PowerBasis.ofBasis B e hx).gen = x := rfl

variable {R S : Type*} {S : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S] [Algebra R S]
  [NoZeroSMulDivisors R S] [IsIntegrallyClosed R]

/--
If `x` generates `S` over `R` and is integral over `R`, then it defines a power basis.
-/
def PowerBasis.ofAdjoinEqTop {x : S} (hx : IsIntegral R x) (hx' : adjoin R {x} = ⊤) :=
  (adjoin.powerBasis' hx).map ((Subalgebra.equivOfEq _ _ hx').trans Subalgebra.topEquiv)

@[simp]
theorem PowerBasis.ofAdjoinEqTop_gen {x : S} (hx : IsIntegral R x) (hx' : adjoin R {x} = ⊤) :
    (PowerBasis.ofAdjoinEqTop hx hx').gen = x := by
  simp [PowerBasis.ofAdjoinEqTop]

end PowerBasis

section general

open scoped nonZeroDivisors

-- set_option pp.proofs true

-- theorem FractionRing.algEquiv_symm_apply (A : Type*) [CommRing A]  (K : Type*) [CommRing K]
--     [Algebra A K] [IsFractionRing A K] (x : K) :
--     (FractionRing.algEquiv A K).symm x = 0 := by
--     --  (IsLocalization.map (Localization A⁰) (RingHom.id A) sorry) a := rfl
--   have := Localization.algEquiv_symm_apply (R := A) (M := A⁰) K x

-- attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

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

variable (A C B₁ B₂)

theorem traceDual_eq_span_traceDual [IsDedekindDomain A] [Module.Finite A B₂] [Module.Free A B₂]
    [NoZeroSMulDivisors A B₂] (h₁ : L₁.LinearDisjoint L₂)
    (h₂ : L₁ ⊔ L₂ = ⊤) (h₃ : IsCoprime ((differentIdeal A B₁).map (algebraMap B₁ C))
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
    have : Module.Finite B₂ C := by
        apply IsIntegralClosure.finite B₂ L₂ M
    rw [← coe_dual_one, coeToSet_coeToSubmodule, ← coe_extendedHomₐ_eq_span, ← coe_dual_one,
      coe_le_coe, ← inv_inv (dual B₁ L₁ 1), ← le_inv_comm (inv_ne_zero (by simp)),
      ← map_inv₀, ← coeIdeal_differentIdeal A K, ← coeIdeal_differentIdeal B₁ L₁,
      extendedHomₐ_coeIdeal_eq_map, coeIdeal_le_coeIdeal' _ le_rfl, ← Ideal.dvd_iff_le]
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

theorem differentIdeal_eq_map_differentIdeal_of_isCoprime [IsDedekindDomain A] [Module.Finite A B₂]
    [Module.Free A B₂] [NoZeroSMulDivisors A B₂] (h₁ : L₁.LinearDisjoint L₂)
    (h₂ : L₁ ⊔ L₂ = ⊤) (h₃ : IsCoprime ((differentIdeal A B₁).map (algebraMap B₁ C))
      ((differentIdeal A B₂).map (algebraMap B₂ C))) :
    differentIdeal B₁ C = Ideal.map (algebraMap B₂ C) (differentIdeal A B₂) := by
  have : Module.Finite B₂ C := IsIntegralClosure.finite B₂ L₂ M _
  rw [← coeIdeal_inj (K := M), coeIdeal_differentIdeal B₁ L₁, inv_eq_iff_eq_inv,
    ← extendedHomₐ_coeIdeal_eq_map (K := L₂), coeIdeal_differentIdeal A K, map_inv₀, inv_inv,
    ← coeToSubmodule_inj, coe_dual_one, coe_extendedHomₐ_eq_span]
  have := congr_arg (fun x : Submodule B₁ M ↦ span C (x : Set M)) <|
    traceDual_eq_span_traceDual A C B₁ B₂ h₁ h₂ h₃
  simp only [span_span_of_tower] at this
  rw [← FractionalIdeal.coeToSet_coeToSubmodule, coe_dual_one, this]
  rw [Submodule.coe_restrictScalars, Submodule.span_eq]

theorem traceDual_eq_traceDual_mul_traceDual_of_isCoprime [IsDedekindDomain A]
    [NoZeroSMulDivisors A B₂] [Module.Finite A B₂] [Module.Free A B₂] [Algebra.IsIntegral B₂ C]
    (h₁ : L₁.LinearDisjoint L₂) (h₂ : L₁ ⊔ L₂ = ⊤)
    (h₃ : IsCoprime ((differentIdeal A B₁).map (algebraMap B₁ C))
      ((differentIdeal A B₂).map (algebraMap B₂ C))) :
    traceDual A K (1 : Submodule C M) = traceDual B₁ L₁ (1 : Submodule C M) *
      traceDual B₂ L₂ (1 : Submodule C M) := by
  have h_main : (traceDual B₁ L₁ (1 : Submodule C M)).restrictScalars B₁ =
      span B₁ (algebraMap L₂ M '' (traceDual A K (1 : Submodule B₂ L₂))) :=
    (traceDual_eq_span_traceDual A C B₁ B₂ h₁ h₂ h₃).symm
  have t₁ := congr_arg (fun x : Submodule B₁ M ↦ span C (x : Set M)) h_main
  simp only [span_span_of_tower] at t₁
  have t₂ := dual_eq_dual_mul_dual A K L₂ B₂ C M
  replace t₂ := congr_arg FractionalIdeal.coeToSubmodule t₂
  rw [coe_mul, FractionalIdeal.coe_dual, coe_extendedHomₐ_eq_span, coe_dual_one, coe_one] at t₂
  · have : (dual A K (1 : FractionalIdeal B₂⁰ L₂) : Set L₂)
      = (traceDual A K (1 : Submodule B₂ L₂) : Set L₂) := by
      rw [← FractionalIdeal.coeToSet_coeToSubmodule, coe_dual_one]
    rw [this] at t₂
    rw [← t₁] at t₂
    rwa [Submodule.coe_restrictScalars, Submodule.span_eq, mul_comm] at t₂
  simp

theorem dual_eq_dual_mul_dual_of_isCoprime [IsDedekindDomain A] [NoZeroSMulDivisors A B₂]
    [Module.Finite A B₂] [Module.Free A B₂] [Algebra.IsIntegral B₂ C]
    (h₁ : L₁.LinearDisjoint L₂) (h₂ : L₁ ⊔ L₂ = ⊤)
    (h₃ : IsCoprime ((differentIdeal A B₁).map (algebraMap B₁ C))
      ((differentIdeal A B₂).map (algebraMap B₂ C))) :
    dual A K (1 : FractionalIdeal C⁰ M) = dual B₁ L₁ (1 : FractionalIdeal C⁰ M) *
      dual B₂ L₂ (1 : FractionalIdeal C⁰ M) := by
  have t₁ := traceDual_eq_traceDual_mul_traceDual_of_isCoprime A C B₁ B₂ h₁ h₂ h₃
  have := coe_dual_one A K M C
  rw [← this] at t₁
  have := coe_dual_one B₁ L₁ M C
  rw [← this] at t₁
  have := coe_dual_one B₂ L₂ M C
  rw [← this] at t₁
  rw [← coe_mul] at t₁
  rwa [FractionalIdeal.coeToSubmodule_inj] at t₁

theorem differentIdeal_eq_differentIdeal_mul_differentIdeal_of_isCoprime [IsDedekindDomain A]
    [NoZeroSMulDivisors A B₂] [Module.Finite A B₂] [Module.Free A B₂] [Algebra.IsIntegral B₂ C]
    (h₁ : L₁.LinearDisjoint L₂) (h₂ : L₁ ⊔ L₂ = ⊤)
    (h₃ : IsCoprime ((differentIdeal A B₁).map (algebraMap B₁ C))
      ((differentIdeal A B₂).map (algebraMap B₂ C))) :
    differentIdeal A C = differentIdeal B₁ C * differentIdeal B₂ C := by
  rw [← FractionalIdeal.coeIdeal_inj (K := M), coeIdeal_mul, coeIdeal_differentIdeal A K,
    coeIdeal_differentIdeal B₁ L₁, coeIdeal_differentIdeal B₂ L₂, inv_eq_iff_eq_inv, mul_inv,
    inv_inv, inv_inv]
  exact dual_eq_dual_mul_dual_of_isCoprime A C B₁ B₂ h₁ h₂ h₃

variable [IsDedekindDomain A] [IsScalarTower A L₂ M] [IsScalarTower A B₁ M] [Module.Free A B₂]
  [Module.Finite A B₂] [NoZeroSMulDivisors A B₂]

theorem span_eq_range
    (h₁ : L₁.LinearDisjoint L₂) (h₂ : L₁.toSubalgebra ⊔ L₂.toSubalgebra = ⊤)
    (h₃ : IsCoprime ((differentIdeal A B₁).map (algebraMap B₁ C))
      ((differentIdeal A B₂).map (algebraMap B₂ C)))
    {ι : Type*} (b : Basis ι K L₂)
    (hb : span A (Set.range b) = (1 : Submodule B₂ L₂).restrictScalars A) :
    span B₁ (Set.range (h₁.basisOfBasisRight h₂ b)) =
      LinearMap.range (IsScalarTower.toAlgHom B₁ C M) := by
    -- span B₁ (Set.range (algebraMap L₂ M ∘ b)) =
    -- LinearMap.range (IsScalarTower.toAlgHom B₁ C M) := by
  classical
  replace h₂ : L₁ ⊔ L₂ = ⊤ := by
    rwa [← sup_toSubalgebra_of_isAlgebraic_right, ← top_toSubalgebra, toSubalgebra_inj] at h₂
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
    · rw [hb]
  · ext; simp


variable {A C B₁ B₂}

/--
Docstring.
-/
noncomputable def Module.Basis.ofIsCoprimeDifferentIdeal (h₁ : L₁.LinearDisjoint L₂)
    (h₂ : L₁.toSubalgebra ⊔ L₂.toSubalgebra = ⊤)
    (h₃ : IsCoprime ((differentIdeal A B₁).map (algebraMap B₁ C))
      ((differentIdeal A B₂).map (algebraMap B₂ C))) {ι : Type*} (b : Basis ι A B₂) :
    Basis ι B₁ C := by
  let v := fun i : ι ↦ algebraMap B₂ C (b i)
  refine Basis.mk (v := v) ?_ ?_
  · have := b.linearIndependent
    have : LinearIndependent A ((IsScalarTower.toAlgHom A B₂ L₂).toLinearMap ∘ b) := by
      apply LinearIndependent.map_injOn b.linearIndependent
      apply Function.Injective.injOn
      exact FaithfulSMul.algebraMap_injective _ _
    rw [LinearIndependent.iff_fractionRing A K] at this
    have := h₁.linearIndependent_right this
    rw [← LinearMap.linearIndependent_iff (IsScalarTower.toAlgHom B₁ C M).toLinearMap]
    · rw [LinearIndependent.iff_fractionRing B₁ L₁]
      convert this
      ext; simp [v, ← IsScalarTower.algebraMap_apply]
      change _ = algebraMap L₂ M (algebraMap B₂ L₂ _)
      rw [← IsScalarTower.algebraMap_apply B₂ L₂ M]
    rw [LinearMap.ker_eq_bot]
    exact FaithfulSMul.algebraMap_injective _ _
  · rw [top_le_iff]
    let f := IsScalarTower.toAlgHom B₁ C M
    let F := Submodule.map f
    have : Function.Injective F := by
      apply Submodule.map_injective_of_injective
      exact FaithfulSMul.algebraMap_injective C M
    apply this
    unfold F f
    simp only [Submodule.map_top]
    let B : Basis ι K L₂ := b.localizationLocalization K A⁰ L₂
    have := span_eq_range A C B₁ B₂ h₁ h₂ h₃ B ?_
    · convert this
      rw [LinearMap.map_span, IsScalarTower.coe_toAlgHom', ← Set.range_comp]
      congr; ext
      simp [B, v, ← IsScalarTower.algebraMap_apply]
    · convert b.localizationLocalization_span K A⁰ L₂
      ext; simp

@[simp]
theorem Module.Basis.ofIsCoprimeDifferentIdeal_apply (h₁ : L₁.LinearDisjoint L₂)
    (h₂ : L₁.toSubalgebra ⊔ L₂.toSubalgebra = ⊤)
    (h₃ : IsCoprime ((differentIdeal A B₁).map (algebraMap B₁ C))
      ((differentIdeal A B₂).map (algebraMap B₂ C))) {ι : Type*} (b : Basis ι A B₂) (i : ι) :
    b.ofIsCoprimeDifferentIdeal h₁ h₂ h₃ i = algebraMap B₂ C (b i) := by
  simp [ofIsCoprimeDifferentIdeal]

theorem Algebra.adjoin_pair_eq_top_of_isCoprime_differentialIdeal [IsScalarTower A B₁ C]
    (h₁ : L₁.LinearDisjoint L₂)
    (h₂ : L₁.toSubalgebra ⊔ L₂.toSubalgebra = ⊤)
    (h₃ : IsCoprime ((differentIdeal A B₁).map (algebraMap B₁ C))
      ((differentIdeal A B₂).map (algebraMap B₂ C))) {α : B₁} {β : B₂}
    (hα : Algebra.adjoin A {α} = ⊤)
    (hβ : Algebra.adjoin A {β} = ⊤) :
    Algebra.adjoin A {algebraMap B₁ C α, algebraMap B₂ C β} = ⊤ := by
  let b := (PowerBasis.ofAdjoinEqTop
    (IsIntegral.isIntegral β) hβ).basis.ofIsCoprimeDifferentIdeal h₁ h₂ h₃
  let Pb := PowerBasis.ofBasis b (finCongr (Fintype.card_fin _).symm)
    (x := algebraMap B₂ C β) (fun i ↦ by simp [b])
  have := congr_arg (Subalgebra.restrictScalars A) Pb.adjoin_gen_eq_top
  rw [Subalgebra.restrictScalars_top] at this
  rw [← this]
  rw [Algebra.adjoin_trans _ _ hα]
  simp [Pb, Set.pair_comm]

end general
