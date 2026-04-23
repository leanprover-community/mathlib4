/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.FieldTheory.LinearDisjoint
public import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.Init
import Mathlib.Logic.Equiv.PartialEquiv
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike

/-!
# Disjoint extensions with coprime different ideals

Let `A ⊆ B` be a finite extension of Dedekind domains and assume that `A ⊆ R₁, R₂ ⊆ B` are two
subrings such that `Frac R₁ ⊔ Frac R₂ = Frac B`, `Frac R₁` and `Frac R₂` are linearly disjoint
over `Frac A`, and that `𝓓(R₁/A)` and `𝓓(R₂/A)` are coprime where `𝓓` denotes the different ideal
and `Frac R` denotes the fraction field of a domain `R`.

## Main results and definitions

* `FractionalIdeal.differentIdeal_eq_map_differentIdeal`: `𝓓(B/R₁) = 𝓓(R₂/A)`
* `FractionalIdeal.differentIdeal_eq_differentIdeal_mul_differentIdeal_of_isCoprime`:
  `𝓓(B/A) = 𝓓(R₁/A) * 𝓓(R₂/A)`.
* `Module.Basis.ofIsCoprimeDifferentIdeal`: Construct a `R₁`-basis of `B` by lifting an
  `A`-basis of `R₂`.
* `IsDedekindDomain.range_sup_range_eq_top_of_isCoprime_differentIdeal`: `B` is generated
  (as an `A`-algebra) by `R₁` and `R₂`.

-/

@[expose] public section

open FractionalIdeal nonZeroDivisors IntermediateField Algebra Module Submodule

variable (A B : Type*) {K L : Type*} [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
  [CommRing B] [Field L] [Algebra B L] [Algebra A L] [Algebra K L] [FiniteDimensional K L]
  [IsScalarTower A K L]
variable (R₁ R₂ : Type*) [CommRing R₁] [CommRing R₂] [IsDomain R₁] [Algebra A R₁] [Algebra A R₂]
  [Algebra R₁ B] [Algebra R₂ B] [Algebra R₁ L] [Algebra R₂ L]
  [IsScalarTower A R₁ L] [IsScalarTower R₁ B L] [IsScalarTower R₂ B L] [Module.Finite A R₂]
variable {F₁ F₂ : IntermediateField K L} [Algebra R₁ F₁] [Algebra R₂ F₂] [IsTorsionFree R₁ F₁]
  [IsScalarTower A F₂ L] [IsScalarTower A R₂ F₂] [IsScalarTower R₁ F₁ L] [IsScalarTower R₂ F₂ L]
  [Algebra.IsSeparable K F₂] [Algebra.IsSeparable F₁ L]

theorem Submodule.traceDual_le_span_map_traceDual [Module.Free A R₂]
    [IsLocalization (Algebra.algebraMapSubmonoid R₂ A⁰) F₂] (h₁ : F₁.LinearDisjoint F₂)
    (h₂ : F₁ ⊔ F₂ = ⊤) :
    (traceDual R₁ F₁ (1 : Submodule B L)).restrictScalars R₁ ≤
      span R₁ (algebraMap F₂ L '' (traceDual A K (1 : Submodule R₂ F₂))) := by
  intro x hx
  have h₂' : F₁.toSubalgebra ⊔ F₂.toSubalgebra = ⊤ := by
    simpa [sup_toSubalgebra_of_isAlgebraic_right] using congr_arg IntermediateField.toSubalgebra h₂
  let b₂ := (Free.chooseBasis A R₂).localizationLocalization K A⁰ F₂
  let B₁ := h₁.basisOfBasisRight h₂' b₂
  have h_main : x ∈ span R₁ (Set.range B₁.traceDual) := by
    rw [B₁.traceDual.mem_span_iff_repr_mem R₁ x]
    intro i
    rw [B₁.traceDual_repr_apply]
    refine mem_traceDual.mp hx _ ?_
    rw [LinearDisjoint.basisOfBasisRight_apply, Basis.localizationLocalization_apply,
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R₂ B L, mem_one]
    exact ⟨_, rfl⟩
  have h : Set.range B₁.traceDual =
      Set.range (IsScalarTower.toAlgHom A F₂ L ∘ b₂.traceDual) := by
    refine congr_arg Set.range <| B₁.traceDual_eq_iff.mpr fun i j ↦ ?_
    rw [LinearDisjoint.basisOfBasisRight_apply, traceForm_apply, Function.comp_apply,
      IsScalarTower.coe_toAlgHom', ← map_mul, h₁.trace_algebraMap h₂, b₂.trace_traceDual_mul,
      MonoidWithZeroHom.map_ite_one_zero]
  rwa [← span_span_of_tower A R₁, h, Set.range_comp, ← AlgHom.coe_toLinearMap, ← map_span,
    ← traceDual_span_of_basis A (1 : Submodule R₂ F₂) b₂
      (by rw [Basis.localizationLocalization_span K A⁰ F₂]; ext; simp)] at h_main

attribute [local instance] FractionRing.liftAlgebra

variable [IsDomain A] [IsDedekindDomain B] [IsDedekindDomain R₁] [IsDedekindDomain R₂]
    [IsFractionRing B L] [IsFractionRing R₁ F₁] [IsFractionRing R₂ F₂] [IsIntegrallyClosed A]
    [IsIntegralClosure B R₁ L] [IsTorsionFree R₁ B] [IsTorsionFree R₂ B]

namespace IsDedekindDomain

theorem differentIdeal_dvd_map_differentIdeal [Algebra.IsIntegral R₂ B]
    [Module.Free A R₂] [IsLocalization (Algebra.algebraMapSubmonoid R₂ A⁰) F₂]
    (h₁ : F₁.LinearDisjoint F₂) (h₂ : F₁ ⊔ F₂ = ⊤) :
    differentIdeal R₁ B ∣ Ideal.map (algebraMap R₂ B) (differentIdeal A R₂) := by
  have : Algebra.IsSeparable (FractionRing A) (FractionRing R₂) := by
    refine Algebra.IsSeparable.of_equiv_equiv (FractionRing.algEquiv A K).symm.toRingEquiv
          (FractionRing.algEquiv R₂ F₂).symm.toRingEquiv ?_
    ext _
    exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv A K).symm
      (FractionRing.algEquiv R₂ ↥F₂).symm _
  rw [Ideal.dvd_iff_le, ← coeIdeal_le_coeIdeal L, coeIdeal_differentIdeal R₁ F₁ L B,
    ← extendedHom_coeIdeal_eq_map L B (K := F₂), le_inv_comm _ (by simp), ← map_inv₀,
    coeIdeal_differentIdeal A K, inv_inv, ← coe_le_coe, coe_dual_one, coe_extendedHom_eq_span,
    ← coeToSet_coeToSubmodule, coe_dual_one]
  · have := Submodule.span_mono (R := B) <| traceDual_le_span_map_traceDual A B R₁ R₂ h₁ h₂
    rwa [← span_coe_eq_restrictScalars, span_span_of_tower, span_span_of_tower, span_eq] at this
  · exact (_root_.map_ne_zero _).mpr <| coeIdeal_eq_zero.not.mpr differentIdeal_ne_bot

variable [Algebra A B] [Module.Finite A B] [IsTorsionFree A B] [IsTorsionFree A R₁]
  [IsTorsionFree A R₂] [Module.Finite A R₁] [Module.Finite R₂ B] [IsScalarTower A R₂ B]
  [Module.Finite R₁ B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
  [IsScalarTower A R₁ B]

theorem map_differentIdeal_dvd_differentIdeal
    (h : IsCoprime ((differentIdeal A R₁).map (algebraMap R₁ B))
      ((differentIdeal A R₂).map (algebraMap R₂ B))) :
    Ideal.map (algebraMap R₂ B) (differentIdeal A R₂) ∣ differentIdeal R₁ B :=
  have := (differentIdeal_eq_differentIdeal_mul_differentIdeal A R₂ B).symm.trans
    (differentIdeal_eq_differentIdeal_mul_differentIdeal A R₁ B)
  h.symm.dvd_of_dvd_mul_right (dvd_of_mul_left_eq _ this)

theorem differentIdeal_eq_map_differentIdeal [Module.Free A R₂] (h₁ : F₁.LinearDisjoint F₂)
    (h₂ : F₁ ⊔ F₂ = ⊤)
    (h₃ : IsCoprime ((differentIdeal A R₁).map (algebraMap R₁ B))
      ((differentIdeal A R₂).map (algebraMap R₂ B))) :
    differentIdeal R₁ B = Ideal.map (algebraMap R₂ B) (differentIdeal A R₂) := by
  apply dvd_antisymm
  · exact differentIdeal_dvd_map_differentIdeal A B R₁ R₂ h₁ h₂
  · exact map_differentIdeal_dvd_differentIdeal A B R₁ R₂ h₃

/--
Let `A ⊆ B` be a finite extension of Dedekind domains and assume that `A ⊆ R₁, R₂ ⊆ B` are two
subrings such that `Frac R₁ ⊔ Frac R₂ = Frac B`, `Frac R₁` and `Frac R₂` are linearly disjoint
over `Frac A`, and that `𝓓(R₁/A)` and `𝓓(R₂/A)` are coprime where `𝓓` denotes the different ideal
and `Frac R` denotes the fraction field of a domain `R`.
We have `𝓓(B/A) = 𝓓(R₁/A) * 𝓓(R₂/A)`.
-/
theorem differentIdeal_eq_differentIdeal_mul_differentIdeal_of_isCoprime
    [Module.Free A R₂] (h₁ : F₁.LinearDisjoint F₂) (h₂ : F₁ ⊔ F₂ = ⊤)
    (h₃ : IsCoprime ((differentIdeal A R₁).map (algebraMap R₁ B))
      ((differentIdeal A R₂).map (algebraMap R₂ B))) :
    differentIdeal A B = differentIdeal R₁ B * differentIdeal R₂ B := by
  have := differentIdeal_eq_differentIdeal_mul_differentIdeal A R₂ B
  rwa [← differentIdeal_eq_map_differentIdeal A B R₁ R₂ h₁ h₂ h₃,
    mul_comm] at this

end IsDedekindDomain

variable [Algebra A B] [Module.Finite A B] [IsTorsionFree A B] [IsTorsionFree A R₁]
  [IsTorsionFree A R₂] [Module.Finite A R₁] [Module.Finite R₂ B] [IsScalarTower A R₂ B]
  [Module.Finite R₁ B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
  [IsScalarTower A R₁ B]

theorem Submodule.traceDual_eq_span_map_traceDual_of_linearDisjoint [Module.Free A R₂]
    [IsLocalization (Algebra.algebraMapSubmonoid R₂ A⁰) F₂] (h₁ : F₁.LinearDisjoint F₂)
    (h₂ : F₁ ⊔ F₂ = ⊤) (h₃ : IsCoprime ((differentIdeal A R₁).map (algebraMap R₁ B))
      ((differentIdeal A R₂).map (algebraMap R₂ B))) :
    span R₁ (algebraMap F₂ L '' (traceDual A K (1 : Submodule R₂ F₂))) =
      (traceDual R₁ F₁ (1 : Submodule B L)).restrictScalars R₁ := by
  have : Algebra.IsSeparable (FractionRing A) (FractionRing R₂) := by
    refine Algebra.IsSeparable.of_equiv_equiv (FractionRing.algEquiv A K).symm.toRingEquiv
          (FractionRing.algEquiv R₂ F₂).symm.toRingEquiv ?_
    ext x
    exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv A K).symm
      (FractionRing.algEquiv R₂ ↥F₂).symm _
  suffices span B (algebraMap F₂ L '' (traceDual A K (1 : Submodule R₂ F₂))) ≤
      traceDual R₁ F₁ (1 : Submodule B L) by
    apply le_antisymm
    · refine SetLike.coe_subset_coe.mp (subset_trans ?_ this)
      rw [← Submodule.span_span_of_tower R₁ B]
      exact Submodule.subset_span
    · exact traceDual_le_span_map_traceDual A B R₁ R₂ h₁ h₂
  have := dvd_of_eq <|
    (IsDedekindDomain.differentIdeal_eq_map_differentIdeal A B R₁ R₂ h₁ h₂ h₃).symm
  rwa [Ideal.dvd_iff_le, ← coeIdeal_le_coeIdeal (K := L), coeIdeal_differentIdeal R₁ F₁,
    inv_le_comm, ← extendedHom_coeIdeal_eq_map (K := F₂), coeIdeal_differentIdeal A K, map_inv₀,
    inv_inv, ← coe_le_coe, coe_extendedHom_eq_span, coe_dual_one, ← coeToSet_coeToSubmodule,
    coe_dual_one] at this
  · simp
  · rw [← extendedHom_coeIdeal_eq_map (K := F₂), ne_eq, extendedHom_eq_zero_iff]
    rw [coeIdeal_eq_zero]
    exact differentIdeal_ne_bot

namespace Module.Basis

private theorem ofIsCoprimeDifferentIdeal_aux [Module.Free A R₂]
    (h₁ : F₁.LinearDisjoint F₂) (h₂ : F₁.toSubalgebra ⊔ F₂.toSubalgebra = ⊤)
    (h₃ : IsCoprime ((differentIdeal A R₁).map (algebraMap R₁ B))
      ((differentIdeal A R₂).map (algebraMap R₂ B))) {ι : Type*} (b : Basis ι K F₂)
    (hb : span A (Set.range b) = LinearMap.range (IsScalarTower.toAlgHom A R₂ F₂ : R₂ →ₗ[A] F₂)) :
    span R₁ (Set.range (h₁.basisOfBasisRight h₂ b)) =
      Submodule.restrictScalars R₁ (1 : Submodule B L) := by
  classical
  have h₂' : F₁ ⊔ F₂ = ⊤ := by
    rwa [← sup_toSubalgebra_of_isAlgebraic_right, ← top_toSubalgebra, toSubalgebra_inj] at h₂
  have : Finite ι := Module.Finite.finite_basis b
  have h_main := congr_arg (Submodule.restrictScalars R₁) <|
    congr_arg coeToSubmodule <| (1 : FractionalIdeal B⁰ L).dual_dual R₁ F₁
  rw [← coe_one, ← h_main, coe_dual _ _ (by simp), coe_dual_one, restrictScalars_traceDual,
    ← traceDual_eq_span_map_traceDual_of_linearDisjoint A B R₁ R₂ h₁ h₂' h₃,
    ← coe_restrictScalars A, traceDual_span_of_basis A (1 : Submodule R₂ F₂) b,
    ← IsScalarTower.coe_toAlgHom' A F₂ L, ← AlgHom.coe_toLinearMap, ← map_coe, map_span,
    span_span_of_tower, AlgHom.coe_toLinearMap, IsScalarTower.coe_toAlgHom', ← Set.range_comp]
  · have : (h₁.basisOfBasisRight h₂ b).traceDual = algebraMap F₂ L ∘ b.traceDual := by
      refine Basis.traceDual_eq_iff.mpr fun i j ↦ ?_
      rw [Function.comp_apply, h₁.basisOfBasisRight_apply, traceForm_apply, ← map_mul,
        h₁.trace_algebraMap h₂', b.trace_traceDual_mul i j, MonoidWithZeroHom.map_ite_one_zero]
    rw [← this, (traceForm F₁ L).dualSubmodule_span_of_basis (traceForm_nondegenerate F₁ L),
      ← Basis.traceDual_def, Basis.traceDual_traceDual]
  · rw [hb]
    ext; simp

/--
Let `A ⊆ B` be a finite extension of Dedekind domains and assume that `A ⊆ R₁, R₂ ⊆ B` are two
subrings such that `Frac R₁ ⊔ Frac R₂ = Frac B`, `Frac R₁` and `Frac R₂` are linearly disjoint
over `Frac A`, and that `𝓓(R₁/A)` and `𝓓(R₂/A)` are coprime where `𝓓` denotes the different ideal
and `Frac R` denotes the fraction field of a domain `R`.
Construct a `R₁`-basis of `B` by lifting an `A`-basis of `R₂`.
-/
noncomputable def ofIsCoprimeDifferentIdeal (h₁ : F₁.LinearDisjoint F₂)
    (h₂ : F₁.toSubalgebra ⊔ F₂.toSubalgebra = ⊤)
    (h₃ : IsCoprime ((differentIdeal A R₁).map (algebraMap R₁ B))
      ((differentIdeal A R₂).map (algebraMap R₂ B))) {ι : Type*} (b : Basis ι A R₂) :
    Basis ι R₁ B :=
  have : Module.Free A R₂ := Free.of_basis b
  let v := fun i : ι ↦ algebraMap R₂ B (b i)
  let b₂ : Basis ι K F₂ := b.localizationLocalization K A⁰ F₂
  have P₁ : LinearIndependent R₁ v := by
    rw [← LinearMap.linearIndependent_iff (IsScalarTower.toAlgHom R₁ B L).toLinearMap
      (LinearMap.ker_eq_bot.mpr <| FaithfulSMul.algebraMap_injective _ _),
      LinearIndependent.iff_fractionRing R₁ F₁, Function.comp_def]
    simp_rw [AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom', v,
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R₂ F₂ L,
      ← b.localizationLocalization_apply K A⁰ F₂]
    exact h₁.linearIndependent_right b₂.linearIndependent
  have P₂ : ⊤ ≤ span R₁ (Set.range v) := by
    rw [top_le_iff]
    apply map_injective_of_injective (f := (IsScalarTower.toAlgHom R₁ B L).toLinearMap)
      (FaithfulSMul.algebraMap_injective B L)
    rw [map_span, ← Set.range_comp]
    convert Module.Basis.ofIsCoprimeDifferentIdeal_aux A B R₁ R₂ h₁ h₂ h₃ b₂
      (b.localizationLocalization_span K A⁰ F₂)
    · ext
      simp [b₂, v, ← IsScalarTower.algebraMap_apply]
    · ext; simp
  Basis.mk P₁ P₂

@[simp]
theorem ofIsCoprimeDifferentIdeal_apply (h₁ : F₁.LinearDisjoint F₂)
    (h₂ : F₁.toSubalgebra ⊔ F₂.toSubalgebra = ⊤)
    (h₃ : IsCoprime ((differentIdeal A R₁).map (algebraMap R₁ B))
      ((differentIdeal A R₂).map (algebraMap R₂ B))) {ι : Type*} (b : Basis ι A R₂) (i : ι) :
    b.ofIsCoprimeDifferentIdeal A B R₁ R₂ h₁ h₂ h₃ i = algebraMap R₂ B (b i) := by
  simp [Module.Basis.ofIsCoprimeDifferentIdeal]

end Module.Basis

namespace IsDedekindDomain

/--
Let `A ⊆ B` be a finite extension of Dedekind domains and assume that `A ⊆ R₁, R₂ ⊆ B` are two
subrings such that `Frac R₁ ⊔ Frac R₂ = Frac B`, `Frac R₁` and `Frac R₂` are linearly disjoint
over `Frac A`, and that `𝓓(R₁/A)` and `𝓓(R₂/A)` are coprime where `𝓓` denotes the different ideal
and `Frac R` denotes the fraction field of a domain `R`.
Then `B` is generated (as an `A`-algebra) by `R₁` and `R₂`.
-/
theorem range_sup_range_eq_top_of_isCoprime_differentIdeal
    (h₁ : F₁.LinearDisjoint F₂)
    (h₂ : F₁.toSubalgebra ⊔ F₂.toSubalgebra = ⊤)
    (h₃ : IsCoprime ((differentIdeal A R₁).map (algebraMap R₁ B))
      ((differentIdeal A R₂).map (algebraMap R₂ B))) [Module.Free A R₂] :
    (IsScalarTower.toAlgHom A R₁ B).range ⊔
      (IsScalarTower.toAlgHom A R₂ B).range = ⊤ := by
  let B₁ := (Free.chooseBasis A R₂).ofIsCoprimeDifferentIdeal A B R₁ R₂ h₁ h₂ h₃
  refine Algebra.eq_top_iff.mpr fun x ↦ ?_
  rw [← B₁.sum_repr x]
  refine Subalgebra.sum_mem _ fun i _ ↦ ?_
  rw [Algebra.smul_def]
  exact Subalgebra.mul_mem _ (Algebra.mem_sup_left (by simp)) (Algebra.mem_sup_right (by simp [B₁]))

theorem adjoin_union_eq_top_of_isCoprime_differentialIdeal [Module.Free A R₂]
    (h₁ : F₁.LinearDisjoint F₂) (h₂ : F₁.toSubalgebra ⊔ F₂.toSubalgebra = ⊤)
    (h₃ : IsCoprime ((differentIdeal A R₁).map (algebraMap R₁ B))
      ((differentIdeal A R₂).map (algebraMap R₂ B))) {s : Set R₁} {t : Set R₂}
    (hs : Algebra.adjoin A s = ⊤) (ht : Algebra.adjoin A t = ⊤) :
    Algebra.adjoin A (algebraMap R₁ B '' s ∪ algebraMap R₂ B '' t) = ⊤ := by
  rw [Algebra.adjoin_union, ← IsScalarTower.coe_toAlgHom' A R₁, ← IsScalarTower.coe_toAlgHom' A R₂,
    ← AlgHom.map_adjoin, hs, ← AlgHom.map_adjoin, ht, Algebra.map_top, Algebra.map_top]
  exact range_sup_range_eq_top_of_isCoprime_differentIdeal A B R₁ R₂ h₁ h₂ h₃

end IsDedekindDomain
