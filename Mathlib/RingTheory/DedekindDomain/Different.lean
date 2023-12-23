/-
Copyright (c) 2023 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.DedekindDomain.Ideal
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# The different ideal

## Main definition
- `Submodule.traceDual`: The dual `L`-sub `B`-module under the trace form.
- `FractionalIdeal.dual`: The dual fractional ideal under the trace form.
- `differentIdeal`: The different ideal of an extension of integral domains.

## TODO
- Show properties of the different ideal
-/

universe u

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable (A K : Type*) {L : Type u} {B} [CommRing A] [Field K] [CommRing B] [Field L]
variable [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
variable [IsScalarTower A K L] [IsScalarTower A B L]
variable [IsDomain A] [IsDomain B]
variable [IsFractionRing A K] [IsIntegralClosure B A L] [IsFractionRing B L]
variable [FiniteDimensional K L] [IsSeparable K L]

open nonZeroDivisors IsLocalization Matrix Algebra

/-- Under the AKLB setting, `Iᵛ := traceDual A K (I : Submodule B L)` is the
`Submodule B L` such that `x ∈ Iᵛ ↔ ∀ y ∈ I, Tr(x, y) ∈ A` -/
noncomputable
def Submodule.traceDual (I : Submodule B L) : Submodule B L where
  __ := (traceForm K L).dualSubmodule (I.restrictScalars A)
  smul_mem' c x hx a ha := by
    rw [traceForm_apply, smul_mul_assoc, mul_comm, ← smul_mul_assoc, mul_comm]
    exact hx _ (Submodule.smul_mem _ c ha)

variable {A K}

local notation:max I:max "ᵛ" => Submodule.traceDual A K I

namespace Submodule

lemma mem_traceDual {I : Submodule B L} {x} :
    x ∈ Iᵛ ↔ ∀ a ∈ I, traceForm K L x a ∈ (algebraMap A K).range :=
  Iff.rfl

lemma le_traceDual_iff_map_le_one {I J : Submodule B L} :
    I ≤ Jᵛ ↔ ((I * J : Submodule B L).restrictScalars A).map
      ((trace K L).restrictScalars A) ≤ 1 := by
  rw [Submodule.map_le_iff_le_comap, Submodule.restrictScalars_mul, Submodule.mul_le]
  simp [SetLike.le_def, mem_traceDual]

lemma le_traceDual_mul_iff {I J J' : Submodule B L} :
    I ≤ (J * J')ᵛ ↔ I * J ≤ J'ᵛ := by
  simp_rw [le_traceDual_iff_map_le_one, mul_assoc]

lemma le_traceDual {I J : Submodule B L} :
    I ≤ Jᵛ ↔ I * J ≤ 1ᵛ := by
  rw [← le_traceDual_mul_iff, mul_one]

lemma le_traceDual_comm {I J : Submodule B L} :
    I ≤ Jᵛ ↔ J ≤ Iᵛ := by rw [le_traceDual, mul_comm, ← le_traceDual]

lemma le_traceDual_traceDual {I : Submodule B L} :
    I ≤ Iᵛᵛ := le_traceDual_comm.mpr le_rfl

@[simp]
lemma traceDual_bot :
    (⊥ : Submodule B L)ᵛ = ⊤ := by ext; simpa [mem_traceDual, -RingHom.mem_range] using zero_mem _

open scoped Classical in
lemma traceDual_top' :
    (⊤ : Submodule B L)ᵛ =
      if ((LinearMap.range (Algebra.trace K L)).restrictScalars A ≤ 1) then ⊤ else ⊥ := by
  classical
  split_ifs with h
  · rw [_root_.eq_top_iff]
    exact fun _ _ _ _ ↦ h ⟨_, rfl⟩
  · rw [_root_.eq_bot_iff]
    intro x hx
    change ¬∀ x, _ → _ at h; push_neg at h
    show x = 0; by_contra hx'
    obtain ⟨_, ⟨b, rfl⟩, hb⟩ := h
    apply hb
    simpa [hx'] using hx (x⁻¹ * b) trivial

lemma traceDual_top [Decidable (IsField A)] :
    (⊤ : Submodule B L)ᵛ = if IsField A then ⊤ else ⊥ := by
  convert traceDual_top'
  rw [← IsFractionRing.surjective_iff_isField (R := A) (K := K),
    LinearMap.range_eq_top.mpr (Algebra.trace_surjective K L),
    ← RingHom.range_top_iff_surjective, _root_.eq_top_iff, SetLike.le_def]
  rfl

end Submodule

open Submodule

variable [IsIntegrallyClosed A]

lemma Submodule.mem_traceDual_iff_isIntegral {I : Submodule B L} {x} :
    x ∈ Iᵛ ↔ ∀ a ∈ I, IsIntegral A (traceForm K L x a) :=
  forall₂_congr (fun _ _ ↦ IsIntegrallyClosed.isIntegral_iff.symm)

lemma Submodule.one_le_traceDual_one :
    (1 : Submodule B L) ≤ 1ᵛ := by
  rw [le_traceDual_iff_map_le_one, mul_one]
  rintro _ ⟨x, ⟨x, rfl⟩, rfl⟩
  apply IsIntegrallyClosed.isIntegral_iff.mp
  apply isIntegral_trace
  rw [IsIntegralClosure.isIntegral_iff (A := B)]
  exact ⟨_, rfl⟩

/-- If `b` is an `A`-integral basis of `L` with discriminant `b`, then `d • a * x` is integral over
  `A` for all `a ∈ I` and `x ∈ Iᵛ`. -/
lemma isIntegral_discr_mul_of_mem_traceDual
    (I : Submodule B L) {ι} [DecidableEq ι] [Fintype ι]
    {b : Basis ι K L} (hb : ∀ i, IsIntegral A (b i))
    {a x : L} (ha : a ∈ I) (hx : x ∈ Iᵛ) :
    IsIntegral A ((discr K b) • a * x) := by
  have hinv : IsUnit (traceMatrix K b).det := by
    simpa [← discr_def] using discr_isUnit_of_basis _ b
  have H := mulVec_cramer (traceMatrix K b) fun i => trace K L (x * a * b i)
  have : Function.Injective (traceMatrix K b).mulVec
  · rwa [mulVec_injective_iff_isUnit, isUnit_iff_isUnit_det]
  rw [← traceMatrix_of_basis_mulVec, ← mulVec_smul, this.eq_iff,
    traceMatrix_of_basis_mulVec] at H
  rw [← b.equivFun.symm_apply_apply (_ * _), b.equivFun_symm_apply]
  apply IsIntegral.sum
  intro i _
  rw [smul_mul_assoc, b.equivFun.map_smul, discr_def, mul_comm, ← H, Algebra.smul_def]
  refine RingHom.IsIntegralElem.mul _ ?_ (hb _)
  apply IsIntegral.algebraMap
  rw [cramer_apply]
  apply IsIntegral.det
  intros j k
  rw [updateColumn_apply]
  split
  · rw [mul_assoc]
    rw [mem_traceDual_iff_isIntegral] at hx
    apply hx
    have ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := B)).mp (hb j)
    rw [mul_comm, ← hy, ← Algebra.smul_def]
    exact I.smul_mem _ (ha)
  · exact isIntegral_trace (RingHom.IsIntegralElem.mul _ (hb j) (hb k))

variable (A K)

lemma map_equiv_traceDual [NoZeroSMulDivisors A B] (I : Submodule B (FractionRing B)) :
    (traceDual A (FractionRing A) I).map (FractionRing.algEquiv B L) =
      traceDual A K (I.map (FractionRing.algEquiv B L)) := by
  show Submodule.map (FractionRing.algEquiv B L).toLinearEquiv.toLinearMap _ =
    traceDual A K (I.map (FractionRing.algEquiv B L).toLinearEquiv.toLinearMap)
  rw [Submodule.map_equiv_eq_comap_symm, Submodule.map_equiv_eq_comap_symm]
  ext x
  simp only [AlgEquiv.toLinearEquiv_symm, AlgEquiv.toLinearEquiv_toLinearMap,
    traceDual, traceForm_apply, Submodule.mem_comap, AlgEquiv.toLinearMap_apply,
    Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
  apply (FractionRing.algEquiv B L).forall_congr
  simp only [restrictScalars_mem, traceForm_apply, AlgEquiv.toEquiv_eq_coe,
    EquivLike.coe_coe, mem_comap, AlgEquiv.toLinearMap_apply, AlgEquiv.symm_apply_apply]
  refine fun {y} ↦ (forall_congr' $ fun hy ↦ ?_)
  rw [Algebra.trace_eq_of_equiv_equiv (FractionRing.algEquiv A K).toRingEquiv
    (FractionRing.algEquiv B L).toRingEquiv]
  swap
  · apply IsLocalization.ringHom_ext (M := A⁰); ext
    simp only [AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_comp,
      RingHom.coe_coe, Function.comp_apply, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply A B (FractionRing B), AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply]
  simp only [AlgEquiv.toRingEquiv_eq_coe, _root_.map_mul, AlgEquiv.coe_ringEquiv,
    AlgEquiv.apply_symm_apply]
  show (FractionRing.algEquiv A K).symm _ ∈ (algebraMap A (FractionRing A)).range ↔ _
  rw [← (FractionRing.algEquiv A K).symm.toAlgHom.comp_algebraMap, ← RingHom.map_range,
    AlgEquiv.toAlgHom_eq_coe, AlgEquiv.coe_ringHom_commutes, Subring.mem_map_equiv]
  simp

open scoped Classical

namespace FractionalIdeal

/-- The dual of a non-zero fractional ideal is the dual of the submodule under the traceform. -/
noncomputable
def dual (I : FractionalIdeal B⁰ L) :
    FractionalIdeal B⁰ L :=
  if hI : I = 0 then 0 else
  ⟨Iᵛ, by
    classical
    have ⟨s, b, hb⟩ := FiniteDimensional.exists_is_basis_integral A K L
    obtain ⟨x, hx, hx'⟩ := exists_ne_zero_mem_isInteger hI
    have ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := B)).mp
      (IsIntegral.algebraMap (B := L) (discr_isIntegral K hb))
    refine ⟨y * x, mem_nonZeroDivisors_iff_ne_zero.mpr (mul_ne_zero ?_ hx), fun z hz ↦ ?_⟩
    · rw [← (IsIntegralClosure.algebraMap_injective B A L).ne_iff, hy, RingHom.map_zero,
        ← (algebraMap K L).map_zero, (algebraMap K L).injective.ne_iff]
      exact discr_not_zero_of_basis K b
    · convert isIntegral_discr_mul_of_mem_traceDual I hb hx' hz using 1
      · ext w; exact (IsIntegralClosure.isIntegral_iff (A := B)).symm
      · rw [Algebra.smul_def, RingHom.map_mul, hy, ← Algebra.smul_def]⟩

variable [IsDedekindDomain B] {I J : FractionalIdeal B⁰ L} (hI : I ≠ 0) (hJ : J ≠ 0)

lemma coe_dual :
    (dual A K I : Submodule B L) = Iᵛ := by rw [dual, dif_neg hI]; rfl

variable (B L)

@[simp]
lemma coe_dual_one :
    (dual A K (1 : FractionalIdeal B⁰ L) : Submodule B L) = 1ᵛ := by
  rw [← coe_one, coe_dual]
  exact one_ne_zero

@[simp]
lemma dual_zero :
    dual A K (0 : FractionalIdeal B⁰ L) = 0 := by rw [dual, dif_pos rfl]

variable {A K L B}

lemma mem_dual {x} :
    x ∈ dual A K I ↔ ∀ a ∈ I, traceForm K L x a ∈ (algebraMap A K).range := by
  rw [dual, dif_neg hI]; rfl

variable (A K)

lemma dual_ne_zero :
    dual A K I ≠ 0 := by
  obtain ⟨b, hb, hb'⟩ := I.prop
  suffices algebraMap B L b ∈ dual A K I by
    intro e
    rw [e, mem_zero_iff, ← (algebraMap B L).map_zero,
      (IsIntegralClosure.algebraMap_injective B A L).eq_iff] at this
    exact mem_nonZeroDivisors_iff_ne_zero.mp hb this
  rw [mem_dual hI]
  intro a ha
  apply IsIntegrallyClosed.isIntegral_iff.mp
  apply isIntegral_trace
  dsimp
  convert hb' a ha using 1
  · ext w
    exact IsIntegralClosure.isIntegral_iff (A := B)
  · exact (Algebra.smul_def _ _).symm

variable {A K}

@[simp]
lemma dual_eq_zero_iff :
    dual A K I = 0 ↔ I = 0 :=
  ⟨not_imp_not.mp (dual_ne_zero A K), fun e ↦ e.symm ▸ dual_zero A K L B⟩

lemma dual_ne_zero_iff :
    dual A K I ≠ 0 ↔ I ≠ 0 := dual_eq_zero_iff.not

variable (A K)

lemma le_dual_inv_aux (hIJ : I * J ≤ 1) :
    J ≤ dual A K I := by
  rw [dual, dif_neg hI]
  intro x hx y hy
  apply IsIntegrallyClosed.isIntegral_iff.mp
  apply isIntegral_trace
  rw [IsIntegralClosure.isIntegral_iff (A := B)]
  have ⟨z, _, hz⟩ := hIJ (FractionalIdeal.mul_mem_mul hy hx)
  rw [mul_comm] at hz
  exact ⟨z, hz⟩

lemma one_le_dual_one :
    1 ≤ dual A K (1 : FractionalIdeal B⁰ L) :=
  le_dual_inv_aux A K one_ne_zero (by rw [one_mul])

lemma le_dual_iff :
    I ≤ dual A K J ↔ I * J ≤ dual A K 1 := by
  by_cases hI : I = 0
  · simp [hI, zero_le]
  rw [← coe_le_coe, ← coe_le_coe, coe_mul, coe_dual A K hJ, coe_dual_one, le_traceDual]

variable (I)

lemma inv_le_dual :
    I⁻¹ ≤ dual A K I :=
  if hI : I = 0 then by simp [hI] else le_dual_inv_aux A K hI (le_of_eq (mul_inv_cancel hI))

lemma dual_inv_le :
    (dual A K I)⁻¹ ≤ I := by
  by_cases hI : I = 0; · simp [hI]
  convert mul_right_mono ((dual A K I)⁻¹)
    (mul_left_mono I (inv_le_dual A K I)) using 1
  · simp only [mul_inv_cancel hI, one_mul]
  · simp only [mul_inv_cancel (dual_ne_zero A K (hI := hI)), mul_assoc, mul_one]

lemma dual_eq_mul_inv :
    dual A K I = dual A K 1 * I⁻¹ := by
  by_cases hI : I = 0; · simp [hI]
  apply le_antisymm
  · suffices : dual A K I * I ≤ dual A K 1
    · convert mul_right_mono I⁻¹ this using 1; simp only [mul_inv_cancel hI, mul_one, mul_assoc]
    rw [← le_dual_iff A K hI]
  rw [le_dual_iff A K hI, mul_assoc, inv_mul_cancel hI, mul_one]

variable {I}

lemma dual_div_dual :
    dual A K J / dual A K I = I / J := by
  rw [dual_eq_mul_inv A K J, dual_eq_mul_inv A K I, mul_div_mul_comm, div_self, one_mul]
  exact inv_div_inv J I
  simp only [ne_eq, dual_eq_zero_iff, one_ne_zero, not_false_eq_true]

lemma dual_mul_self :
    dual A K I * I = dual A K 1 := by
  rw [dual_eq_mul_inv, mul_assoc, inv_mul_cancel hI, mul_one]

lemma self_mul_dual :
    I * dual A K I = dual A K 1 := by
  rw [mul_comm, dual_mul_self A K hI]

lemma dual_inv :
    dual A K I⁻¹ = dual A K 1 * I := by rw [dual_eq_mul_inv, inv_inv]

variable (I)

@[simp]
lemma dual_dual :
    dual A K (dual A K I) = I := by
  rw [dual_eq_mul_inv, dual_eq_mul_inv A K (I := I), mul_inv, inv_inv, ← mul_assoc, mul_inv_cancel,
    one_mul]
  rw [dual_ne_zero_iff]
  exact one_ne_zero

variable {I}

@[simp]
lemma dual_le_dual :
    dual A K I ≤ dual A K J ↔ J ≤ I := by
  nth_rewrite 2 [← dual_dual A K I]
  rw [le_dual_iff A K hJ, le_dual_iff A K (I := J) (by rwa [dual_ne_zero_iff]), mul_comm]

variable {A K}

lemma dual_involutive :
    Function.Involutive (dual A K : FractionalIdeal B⁰ L → FractionalIdeal B⁰ L) := dual_dual A K

lemma dual_injective :
    Function.Injective (dual A K : FractionalIdeal B⁰ L → FractionalIdeal B⁰ L) :=
  dual_involutive.injective

end FractionalIdeal

variable (B)
variable [IsDedekindDomain B]

/-- The different ideal of an extension of integral domains `B/A` is the inverse of the dual of `A`
as an ideal of `B`. See `coeIdeal_differentIdeal` and `coeSubmodule_differentIdeal`. -/
def differentIdeal [NoZeroSMulDivisors A B] : Ideal B :=
  (1 / Submodule.traceDual A (FractionRing A) 1 : Submodule B (FractionRing B)).comap
    (Algebra.linearMap B (FractionRing B))

lemma coeSubmodule_differentIdeal_fractionRing
    [NoZeroSMulDivisors A B] (hAB : Algebra.IsIntegral A B)
    [IsSeparable (FractionRing A) (FractionRing B)]
    [FiniteDimensional (FractionRing A) (FractionRing B)] :
    coeSubmodule (FractionRing B) (differentIdeal A B) =
      1 / Submodule.traceDual A (FractionRing A) 1 := by
  have : IsIntegralClosure B A (FractionRing B) :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _ hAB
  rw [coeSubmodule, differentIdeal, Submodule.map_comap_eq, inf_eq_right]
  have := FractionalIdeal.dual_inv_le (A := A) (K := FractionRing A)
    (1 : FractionalIdeal B⁰ (FractionRing B))
  have : _ ≤ ((1 : FractionalIdeal B⁰ (FractionRing B)) : Submodule B (FractionRing B)) := this
  simp only [← one_div, FractionalIdeal.val_eq_coe] at this
  rw [FractionalIdeal.coe_div (FractionalIdeal.dual_ne_zero _ _ _),
    FractionalIdeal.coe_dual] at this
  simpa only [FractionalIdeal.coe_one] using this
  · exact one_ne_zero
  · exact one_ne_zero

lemma coeSubmodule_differentIdeal [NoZeroSMulDivisors A B] :
    coeSubmodule L (differentIdeal A B) = 1 / Submodule.traceDual A K 1 := by
  have : (FractionRing.algEquiv B L).toLinearEquiv.comp (Algebra.linearMap B (FractionRing B)) =
    Algebra.linearMap B L := by ext; simp
  rw [coeSubmodule, ← this]
  have H : RingHom.comp (algebraMap (FractionRing A) (FractionRing B))
    ↑(FractionRing.algEquiv A K).symm.toRingEquiv =
      RingHom.comp ↑(FractionRing.algEquiv B L).symm.toRingEquiv (algebraMap K L)
  · apply IsLocalization.ringHom_ext A⁰
    ext
    simp only [AlgEquiv.toRingEquiv_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
      AlgEquiv.coe_ringEquiv, Function.comp_apply, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply A B L, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  have : IsSeparable (FractionRing A) (FractionRing B) := IsSeparable.of_equiv_equiv _ _ H
  have : FiniteDimensional (FractionRing A) (FractionRing B) := Module.Finite.of_equiv_equiv _ _ H
  simp only [AlgEquiv.toLinearEquiv_toLinearMap, Submodule.map_comp]
  rw [← coeSubmodule, coeSubmodule_differentIdeal_fractionRing _ _
      (IsIntegralClosure.isIntegral_algebra _ L),
    Submodule.map_div, ← AlgEquiv.toAlgHom_toLinearMap, Submodule.map_one]
  congr 1
  refine (map_equiv_traceDual A K _).trans ?_
  congr 1
  ext
  simp

variable (L)

lemma coeIdeal_differentIdeal [NoZeroSMulDivisors A B] :
    ↑(differentIdeal A B) = (FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ L))⁻¹ := by
  apply FractionalIdeal.coeToSubmodule_injective
  simp only [FractionalIdeal.coe_div
    (FractionalIdeal.dual_ne_zero _ _ (@one_ne_zero (FractionalIdeal B⁰ L) _ _ _)),
    FractionalIdeal.coe_coeIdeal, coeSubmodule_differentIdeal A K, inv_eq_one_div,
    FractionalIdeal.coe_dual_one, FractionalIdeal.coe_one]

variable {A K B L}

lemma differentialIdeal_le_fractionalIdeal_iff
    {I : FractionalIdeal B⁰ L} (hI : I ≠ 0) [NoZeroSMulDivisors A B] :
    differentIdeal A B ≤ I ↔ (((I⁻¹ : _) : Submodule B L).restrictScalars A).map
      ((Algebra.trace K L).restrictScalars A) ≤ 1 := by
  rw [coeIdeal_differentIdeal A K L B, FractionalIdeal.inv_le_comm (by simp) hI,
    ← FractionalIdeal.coe_le_coe, FractionalIdeal.coe_dual_one]
  refine le_traceDual_iff_map_le_one.trans ?_
  simp

lemma differentialIdeal_le_iff {I : Ideal B} (hI : I ≠ ⊥) [NoZeroSMulDivisors A B] :
    differentIdeal A B ≤ I ↔ (((I⁻¹ : FractionalIdeal B⁰ L) : Submodule B L).restrictScalars A).map
      ((Algebra.trace K L).restrictScalars A) ≤ 1 :=
  (FractionalIdeal.coeIdeal_le_coeIdeal _).symm.trans
    (differentialIdeal_le_fractionalIdeal_iff (I := (I : FractionalIdeal B⁰ L)) (by simpa))
