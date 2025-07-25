/-
Copyright (c) 2023 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.NumberTheory.KummerDedekind
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.Finiteness.Quotient
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.RingTheory.Trace.Quotient

/-!
# The different ideal

## Main definition
- `Submodule.traceDual`: The dual `L`-sub `B`-module under the trace form.
- `FractionalIdeal.dual`: The dual fractional ideal under the trace form.
- `differentIdeal`: The different ideal of an extension of integral domains.

## Main results
- `conductor_mul_differentIdeal`:
  If `L = K[x]`, with `x` integral over `A`, then `𝔣 * 𝔇 = (f'(x))`
    with `f` being the minimal polynomial of `x`.
- `aeval_derivative_mem_differentIdeal`:
  If `L = K[x]`, with `x` integral over `A`, then `f'(x) ∈ 𝔇`
    with `f` being the minimal polynomial of `x`.
- `not_dvd_differentIdeal_iff`: A prime does not divide the different ideal iff it is unramified
  (in the sense of `Algebra.IsUnramifiedAt`).

## TODO
- Show properties of the different ideal
-/

open Module

universe u

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
  Ideal.Quotient.field

variable (A K : Type*) {L : Type u} {B} [CommRing A] [Field K] [CommRing B] [Field L]
variable [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
variable [IsScalarTower A K L] [IsScalarTower A B L]

open nonZeroDivisors IsLocalization Matrix Algebra Pointwise Polynomial Submodule
section BIsDomain

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
  forall₂_congr fun _ _ ↦ mem_one

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
lemma restrictScalars_traceDual {I : Submodule B L} :
    Iᵛ.restrictScalars A = (Algebra.traceForm K L).dualSubmodule (I.restrictScalars A) := rfl

@[simp]
lemma traceDual_bot :
    (⊥ : Submodule B L)ᵛ = ⊤ := by ext; simp [mem_traceDual, -RingHom.mem_range]

open scoped Classical in
lemma traceDual_top' :
    (⊤ : Submodule B L)ᵛ =
      if ((LinearMap.range (Algebra.trace K L)).restrictScalars A ≤ 1) then ⊤ else ⊥ := by
  classical
  split_ifs with h
  · rw [_root_.eq_top_iff]
    exact fun _ _ _ _ ↦ h ⟨_, rfl⟩
  · simp only [SetLike.le_def, restrictScalars_mem, LinearMap.mem_range, mem_one,
      forall_exists_index, forall_apply_eq_imp_iff, not_forall, not_exists] at h
    obtain ⟨b, hb⟩ := h
    simp_rw [eq_bot_iff, SetLike.le_def, mem_bot, mem_traceDual, mem_top, true_implies,
      traceForm_apply, RingHom.mem_range]
    contrapose! hb with hx'
    obtain ⟨c, hc, hc0⟩ := hx'
    simpa [hc0] using hc (c⁻¹ * b)

variable [IsDomain A] [IsFractionRing A K] [FiniteDimensional K L] [Algebra.IsSeparable K L]

lemma traceDual_top [Decidable (IsField A)] :
    (⊤ : Submodule B L)ᵛ = if IsField A then ⊤ else ⊥ := by
  convert traceDual_top'
  rw [← IsFractionRing.surjective_iff_isField (R := A) (K := K),
    LinearMap.range_eq_top.mpr (Algebra.trace_surjective K L),
    ← RingHom.range_eq_top, _root_.eq_top_iff]
  simp [SetLike.le_def]

end Submodule

open Submodule

variable [IsFractionRing A K]

variable (A K) in
lemma map_equiv_traceDual [IsDomain A] [IsFractionRing B L] [IsDomain B]
    [FaithfulSMul A B] (I : Submodule B (FractionRing B)) :
    (traceDual A (FractionRing A) I).map (FractionRing.algEquiv B L) =
      traceDual A K (I.map (FractionRing.algEquiv B L)) := by
  change Submodule.map (FractionRing.algEquiv B L).toLinearEquiv.toLinearMap _ =
    traceDual A K (I.map (FractionRing.algEquiv B L).toLinearEquiv.toLinearMap)
  rw [Submodule.map_equiv_eq_comap_symm, Submodule.map_equiv_eq_comap_symm]
  ext x
  simp only [traceDual, Submodule.mem_comap,
    Submodule.mem_mk]
  apply (FractionRing.algEquiv B L).forall_congr
  simp only [restrictScalars_mem, LinearEquiv.coe_coe, AlgEquiv.coe_symm_toLinearEquiv,
    traceForm_apply, mem_one, AlgEquiv.toEquiv_eq_coe, EquivLike.coe_coe, mem_comap,
    AlgEquiv.symm_apply_apply]
  refine fun {y} ↦ (forall_congr' fun hy ↦ ?_)
  rw [Algebra.trace_eq_of_equiv_equiv (FractionRing.algEquiv A K).toRingEquiv
    (FractionRing.algEquiv B L).toRingEquiv]
  swap
  · apply IsLocalization.ringHom_ext (M := A⁰); ext
    simp only [AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_comp,
      RingHom.coe_coe, Function.comp_apply, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply A B (FractionRing B), AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply]
  simp only [AlgEquiv.toRingEquiv_eq_coe, map_mul, AlgEquiv.coe_ringEquiv,
    AlgEquiv.apply_symm_apply, ← AlgEquiv.symm_toRingEquiv, AlgEquiv.algebraMap_eq_apply]

variable [IsIntegrallyClosed A]

lemma Submodule.mem_traceDual_iff_isIntegral {I : Submodule B L} {x} :
    x ∈ Iᵛ ↔ ∀ a ∈ I, IsIntegral A (traceForm K L x a) :=
  forall₂_congr fun _ _ ↦ mem_one.trans IsIntegrallyClosed.isIntegral_iff.symm

variable [FiniteDimensional K L] [IsIntegralClosure B A L]

lemma Submodule.one_le_traceDual_one :
    (1 : Submodule B L) ≤ 1ᵛ := by
  rw [le_traceDual_iff_map_le_one, mul_one, one_eq_range]
  rintro _ ⟨x, ⟨x, rfl⟩, rfl⟩
  rw [mem_one]
  apply IsIntegrallyClosed.isIntegral_iff.mp
  apply isIntegral_trace
  rw [IsIntegralClosure.isIntegral_iff (A := B)]
  exact ⟨_, rfl⟩

variable [Algebra.IsSeparable K L]

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
  have : Function.Injective (traceMatrix K b).mulVec := by
    rwa [mulVec_injective_iff_isUnit, isUnit_iff_isUnit_det]
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
  rw [updateCol_apply]
  split
  · rw [mul_assoc]
    rw [mem_traceDual_iff_isIntegral] at hx
    apply hx
    have ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := B)).mp (hb j)
    rw [mul_comm, ← hy, ← Algebra.smul_def]
    exact I.smul_mem _ (ha)
  · exact isIntegral_trace (RingHom.IsIntegralElem.mul _ (hb j) (hb k))

variable (A K)

variable [IsDomain A] [IsFractionRing B L] [Nontrivial B] [NoZeroDivisors B]

namespace FractionalIdeal

open scoped Classical in
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

end FractionalIdeal

end BIsDomain

variable [IsDomain A] [IsFractionRing A K]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsIntegralClosure B A L]

namespace FractionalIdeal

variable [IsFractionRing B L] [IsIntegrallyClosed A]

open Submodule

local notation:max I:max "ᵛ" => Submodule.traceDual A K I

variable [IsDedekindDomain B] {I J : FractionalIdeal B⁰ L}

lemma coe_dual (hI : I ≠ 0) :
    (dual A K I : Submodule B L) = Iᵛ := by rw [dual, dif_neg hI, coe_mk]

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

lemma mem_dual (hI : I ≠ 0) {x} :
    x ∈ dual A K I ↔ ∀ a ∈ I, traceForm K L x a ∈ (algebraMap A K).range := by
  rw [dual, dif_neg hI]; exact forall₂_congr fun _ _ ↦ mem_one

variable (A K)

lemma dual_ne_zero (hI : I ≠ 0) :
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

lemma le_dual_inv_aux (hI : I ≠ 0) (hIJ : I * J ≤ 1) :
    J ≤ dual A K I := by
  rw [dual, dif_neg hI]
  intro x hx y hy
  rw [mem_one]
  apply IsIntegrallyClosed.isIntegral_iff.mp
  apply isIntegral_trace
  rw [IsIntegralClosure.isIntegral_iff (A := B)]
  have ⟨z, _, hz⟩ := hIJ (FractionalIdeal.mul_mem_mul hy hx)
  rw [mul_comm] at hz
  exact ⟨z, hz⟩

lemma one_le_dual_one :
    1 ≤ dual A K (1 : FractionalIdeal B⁰ L) :=
  le_dual_inv_aux A K one_ne_zero (by rw [one_mul])

lemma le_dual_iff (hJ : J ≠ 0) :
    I ≤ dual A K J ↔ I * J ≤ dual A K 1 := by
  by_cases hI : I = 0
  · simp [hI]
  rw [← coe_le_coe, ← coe_le_coe, coe_mul, coe_dual A K hJ, coe_dual_one, le_traceDual]

variable (I)

lemma inv_le_dual :
    I⁻¹ ≤ dual A K I := by
  classical
  exact if hI : I = 0 then by simp [hI] else le_dual_inv_aux A K hI (le_of_eq (mul_inv_cancel₀ hI))

lemma dual_inv_le :
    (dual A K I)⁻¹ ≤ I := by
  by_cases hI : I = 0; · simp [hI]
  convert mul_right_mono ((dual A K I)⁻¹)
    (mul_left_mono I (inv_le_dual A K I)) using 1
  · simp only [mul_inv_cancel₀ hI, one_mul]
  · simp only [mul_inv_cancel₀ (dual_ne_zero A K (hI := hI)), mul_assoc, mul_one]

lemma dual_eq_mul_inv :
    dual A K I = dual A K 1 * I⁻¹ := by
  by_cases hI : I = 0; · simp [hI]
  apply le_antisymm
  · suffices dual A K I * I ≤ dual A K 1 by
      convert mul_right_mono I⁻¹ this using 1; simp only [mul_inv_cancel₀ hI, mul_one, mul_assoc]
    rw [← le_dual_iff A K hI]
  rw [le_dual_iff A K hI, mul_assoc, inv_mul_cancel₀ hI, mul_one]

variable {I}

lemma dual_div_dual :
    dual A K J / dual A K I = I / J := by
  rw [dual_eq_mul_inv A K J, dual_eq_mul_inv A K I, mul_div_mul_comm, div_self, one_mul]
  · exact inv_div_inv J I
  · simp only [ne_eq, dual_eq_zero_iff, one_ne_zero, not_false_eq_true]

lemma dual_mul_self (hI : I ≠ 0) :
    dual A K I * I = dual A K 1 := by
  rw [dual_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hI, mul_one]

lemma self_mul_dual (hI : I ≠ 0) :
    I * dual A K I = dual A K 1 := by
  rw [mul_comm, dual_mul_self A K hI]

lemma dual_inv :
    dual A K I⁻¹ = dual A K 1 * I := by rw [dual_eq_mul_inv, inv_inv]

variable (I)

@[simp]
lemma dual_dual :
    dual A K (dual A K I) = I := by
  rw [dual_eq_mul_inv, dual_eq_mul_inv A K (I := I), mul_inv, inv_inv, ← mul_assoc, mul_inv_cancel₀,
    one_mul]
  rw [dual_ne_zero_iff]
  exact one_ne_zero

variable {I}

@[simp]
lemma dual_le_dual (hI : I ≠ 0) (hJ : J ≠ 0) :
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

section IsIntegrallyClosed

variable (B)
variable [IsIntegrallyClosed A] [IsDedekindDomain B] [NoZeroSMulDivisors A B]

/-- The different ideal of an extension of integral domains `B/A` is the inverse of the dual of `A`
as an ideal of `B`. See `coeIdeal_differentIdeal` and `coeSubmodule_differentIdeal`. -/
noncomputable def differentIdeal : Ideal B :=
  (1 / Submodule.traceDual A (FractionRing A) 1 : Submodule B (FractionRing B)).comap
    (Algebra.linearMap B (FractionRing B))

lemma coeSubmodule_differentIdeal_fractionRing [Algebra.IsIntegral A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    [FiniteDimensional (FractionRing A) (FractionRing B)] :
    coeSubmodule (FractionRing B) (differentIdeal A B) =
      1 / Submodule.traceDual A (FractionRing A) 1 := by
  have : IsIntegralClosure B A (FractionRing B) :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  rw [coeSubmodule, differentIdeal, Submodule.map_comap_eq, inf_eq_right]
  have := FractionalIdeal.dual_inv_le (A := A) (K := FractionRing A)
    (1 : FractionalIdeal B⁰ (FractionRing B))
  have : _ ≤ ((1 : FractionalIdeal B⁰ (FractionRing B)) : Submodule B (FractionRing B)) := this
  simp only [← one_div, FractionalIdeal.val_eq_coe] at this
  rw [FractionalIdeal.coe_div (FractionalIdeal.dual_ne_zero _ _ _),
    FractionalIdeal.coe_dual] at this
  · simpa only [FractionalIdeal.coe_one, Submodule.one_eq_range] using this
  · exact one_ne_zero
  · exact one_ne_zero

section

variable [IsFractionRing B L]

lemma coeSubmodule_differentIdeal :
    coeSubmodule L (differentIdeal A B) = 1 / Submodule.traceDual A K 1 := by
  have : (FractionRing.algEquiv B L).toLinearEquiv.comp (Algebra.linearMap B (FractionRing B)) =
    Algebra.linearMap B L := by ext; simp
  rw [coeSubmodule, ← this]
  have H : RingHom.comp (algebraMap (FractionRing A) (FractionRing B))
      ↑(FractionRing.algEquiv A K).symm.toRingEquiv =
        RingHom.comp ↑(FractionRing.algEquiv B L).symm.toRingEquiv (algebraMap K L) := by
    apply IsLocalization.ringHom_ext A⁰
    ext
    simp only [AlgEquiv.toRingEquiv_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
      AlgEquiv.coe_ringEquiv, Function.comp_apply, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply A B L, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  have : Algebra.IsSeparable (FractionRing A) (FractionRing B) :=
    Algebra.IsSeparable.of_equiv_equiv _ _ H
  have : FiniteDimensional (FractionRing A) (FractionRing B) := Module.Finite.of_equiv_equiv _ _ H
  have : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra _ L
  simp only [AlgEquiv.toLinearEquiv_toLinearMap, Submodule.map_comp]
  rw [← coeSubmodule, coeSubmodule_differentIdeal_fractionRing _ _,
    Submodule.map_div, ← AlgEquiv.toAlgHom_toLinearMap, Submodule.map_one]
  congr 1
  refine (map_equiv_traceDual A K _).trans ?_
  congr 1
  ext
  simp

variable (L)

lemma coeIdeal_differentIdeal :
    ↑(differentIdeal A B) = (FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ L))⁻¹ := by
  apply FractionalIdeal.coeToSubmodule_injective
  simp only [FractionalIdeal.coe_div
    (FractionalIdeal.dual_ne_zero _ _ (@one_ne_zero (FractionalIdeal B⁰ L) _ _ _)),
    FractionalIdeal.coe_coeIdeal, coeSubmodule_differentIdeal A K, inv_eq_one_div,
    FractionalIdeal.coe_dual_one, FractionalIdeal.coe_one]

variable {A K B L}

theorem differentIdeal_ne_bot [Module.Finite A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)] :
    differentIdeal A B ≠ ⊥ := by
  let K := FractionRing A
  let L := FractionRing B
  have : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L :=
    IsIntegralClosure.isLocalization _ K _ _
  have : FiniteDimensional K L := .of_isLocalization A B A⁰
  rw [ne_eq, ← FractionalIdeal.coeIdeal_inj (K := L), coeIdeal_differentIdeal (K := K)]
  simp

lemma differentialIdeal_le_fractionalIdeal_iff
    {I : FractionalIdeal B⁰ L} (hI : I ≠ 0) :
    differentIdeal A B ≤ I ↔ (((I⁻¹ :) : Submodule B L).restrictScalars A).map
      ((Algebra.trace K L).restrictScalars A) ≤ 1 := by
  rw [coeIdeal_differentIdeal A K L B, FractionalIdeal.inv_le_comm (by simp) hI,
    ← FractionalIdeal.coe_le_coe, FractionalIdeal.coe_dual_one]
  refine le_traceDual_iff_map_le_one.trans ?_
  simp

lemma differentialIdeal_le_iff {I : Ideal B} (hI : I ≠ ⊥) :
    differentIdeal A B ≤ I ↔ (((I⁻¹ : FractionalIdeal B⁰ L) : Submodule B L).restrictScalars A).map
      ((Algebra.trace K L).restrictScalars A) ≤ 1 :=
  (FractionalIdeal.coeIdeal_le_coeIdeal _).symm.trans
    (differentialIdeal_le_fractionalIdeal_iff (I := (I : FractionalIdeal B⁰ L)) (by simpa))

variable (A K)

open Pointwise Polynomial in
lemma traceForm_dualSubmodule_adjoin
    {x : L} (hx : Algebra.adjoin K {x} = ⊤) (hAx : IsIntegral A x) :
    (traceForm K L).dualSubmodule (Subalgebra.toSubmodule (Algebra.adjoin A {x})) =
      (aeval x (derivative <| minpoly K x) : L)⁻¹ •
        (Subalgebra.toSubmodule (Algebra.adjoin A {x})) := by
  classical
  have hKx : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  let pb := (Algebra.adjoin.powerBasis' hKx).map
    ((Subalgebra.equivOfEq _ _ hx).trans (Subalgebra.topEquiv))
  have pbgen : pb.gen = x := by simp [pb]
  have hpb : ⇑(LinearMap.BilinForm.dualBasis (traceForm K L) _ pb.basis) = _ :=
    _root_.funext (traceForm_dualBasis_powerBasis_eq pb)
  have : (Subalgebra.toSubmodule (Algebra.adjoin A {x})) =
      Submodule.span A (Set.range pb.basis) := by
    rw [← span_range_natDegree_eq_adjoin (minpoly.monic hAx) (minpoly.aeval _ _)]
    congr; ext y
    have : natDegree (minpoly A x) = natDegree (minpoly K x) := by
      rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hAx, (minpoly.monic hAx).natDegree_map]
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio, Set.mem_range,
      pb.basis_eq_pow, pbgen]
    simp only [this]
    exact ⟨fun ⟨a, b, c⟩ ↦ ⟨⟨a, b⟩, c⟩, fun ⟨⟨a, b⟩, c⟩ ↦ ⟨a, b, c⟩⟩
  clear_value pb
  conv_lhs => rw [this]
  rw [← span_coeff_minpolyDiv hAx, LinearMap.BilinForm.dualSubmodule_span_of_basis,
    Submodule.smul_span, hpb]
  change _ = Submodule.span A (_ '' _)
  simp only [← Set.range_comp, smul_eq_mul, div_eq_inv_mul, pbgen,
    minpolyDiv_eq_of_isIntegrallyClosed K hAx]
  apply le_antisymm <;> rw [Submodule.span_le]
  · rintro _ ⟨i, rfl⟩; exact Submodule.subset_span ⟨i, rfl⟩
  · rintro _ ⟨i, rfl⟩
    by_cases hi : i < pb.dim
    · exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
    · rw [Function.comp_apply, coeff_eq_zero_of_natDegree_lt, mul_zero]
      · exact zero_mem _
      rw [← pb.natDegree_minpoly, pbgen, ← natDegree_minpolyDiv_succ hKx,
        ← Nat.succ_eq_add_one] at hi
      exact le_of_not_gt hi

end

variable (L) {B}

open Polynomial Pointwise in
lemma conductor_mul_differentIdeal
    (x : B) (hx : Algebra.adjoin K {algebraMap B L x} = ⊤) :
    (conductor A x) * differentIdeal A B = Ideal.span {aeval x (derivative (minpoly A x))} := by
  classical
  have hAx : IsIntegral A x := IsIntegralClosure.isIntegral A L x
  haveI := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  apply FractionalIdeal.coeIdeal_injective (K := L)
  simp only [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton]
  rw [coeIdeal_differentIdeal A K L B,
    mul_inv_eq_iff_eq_mul₀]
  swap
  · exact FractionalIdeal.dual_ne_zero A K one_ne_zero
  apply FractionalIdeal.coeToSubmodule_injective
  simp only [FractionalIdeal.coe_coeIdeal, FractionalIdeal.coe_mul,
    FractionalIdeal.coe_spanSingleton, Submodule.span_singleton_mul]
  ext y
  have hne₁ : aeval (algebraMap B L x) (derivative (minpoly K (algebraMap B L x))) ≠ 0 :=
    (Algebra.IsSeparable.isSeparable _ _).aeval_derivative_ne_zero (minpoly.aeval _ _)
  have : algebraMap B L (aeval x (derivative (minpoly A x))) ≠ 0 := by
    rwa [minpoly.isIntegrallyClosed_eq_field_fractions K L hAx, derivative_map,
      aeval_map_algebraMap, aeval_algebraMap_apply] at hne₁
  rw [Submodule.mem_smul_iff_inv_mul_mem this, FractionalIdeal.mem_coe, FractionalIdeal.mem_dual,
    mem_coeSubmodule_conductor]
  swap
  · exact one_ne_zero
  have hne₂ : (aeval (algebraMap B L x) (derivative (minpoly K (algebraMap B L x))))⁻¹ ≠ 0 := by
    rwa [ne_eq, inv_eq_zero]
  have : IsIntegral A (algebraMap B L x) := IsIntegral.map (IsScalarTower.toAlgHom A B L) hAx
  simp_rw [← Subalgebra.mem_toSubmodule, ← Submodule.mul_mem_smul_iff (y := y * _)
    (mem_nonZeroDivisors_of_ne_zero hne₂)]
  rw [← traceForm_dualSubmodule_adjoin A K hx this]
  simp only [LinearMap.BilinForm.mem_dualSubmodule, traceForm_apply, Subalgebra.mem_toSubmodule,
    minpoly.isIntegrallyClosed_eq_field_fractions K L hAx,
    derivative_map, aeval_map_algebraMap, aeval_algebraMap_apply, mul_assoc,
    FractionalIdeal.mem_one_iff, forall_exists_index, forall_apply_eq_imp_iff]
  simp_rw [← IsScalarTower.toAlgHom_apply A B L x, ← AlgHom.map_adjoin_singleton]
  simp only [Subalgebra.mem_map, IsScalarTower.coe_toAlgHom', Submodule.one_eq_range,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, ← map_mul]
  exact ⟨fun H b ↦ (mul_one b) ▸ H b 1 (one_mem _), fun H _ _ _ ↦ H _⟩

open Polynomial Pointwise in
lemma aeval_derivative_mem_differentIdeal
    (x : B) (hx : Algebra.adjoin K {algebraMap B L x} = ⊤) :
    aeval x (derivative (minpoly A x)) ∈ differentIdeal A B := by
  refine SetLike.le_def.mp ?_ (Ideal.mem_span_singleton_self _)
  rw [← conductor_mul_differentIdeal A K L x hx]
  exact Ideal.mul_le_left

end IsIntegrallyClosed
section

variable (L)
variable [IsFractionRing B L] [IsDedekindDomain A] [IsDedekindDomain B]
  [NoZeroSMulDivisors A B] [Module.Finite A B]

include K L in
lemma pow_sub_one_dvd_differentIdeal_aux
    {p : Ideal A} [p.IsMaximal] (P : Ideal B) {e : ℕ} (he : e ≠ 0) (hp : p ≠ ⊥)
    (hP : P ^ e ∣ p.map (algebraMap A B)) : P ^ (e - 1) ∣ differentIdeal A B := by
  obtain ⟨a, ha⟩ := (pow_dvd_pow _ (Nat.sub_le e 1)).trans hP
  have hp' := (Ideal.map_eq_bot_iff_of_injective
    (FaithfulSMul.algebraMap_injective A B)).not.mpr hp
  have habot : a ≠ ⊥ := fun ha' ↦ hp' (by simpa [ha'] using ha)
  have hPbot : P ≠ ⊥ := by
    rintro rfl; apply hp'
    rwa [← Ideal.zero_eq_bot, zero_pow he, zero_dvd_iff, Ideal.zero_eq_bot] at hP
  have : p.map (algebraMap A B) ∣ a ^ e := by
    obtain ⟨b, hb⟩ := hP
    apply_fun (· ^ e : Ideal B → _) at ha
    apply_fun (· ^ (e - 1) : Ideal B → _) at hb
    simp only [mul_pow, ← pow_mul, mul_comm e] at ha hb
    conv_lhs at ha => rw [← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr he)]
    rw [pow_add, hb, mul_assoc, mul_right_inj' (pow_ne_zero _ hPbot), pow_one, mul_comm] at ha
    exact ⟨_, ha.symm⟩
  suffices ∀ x ∈ a, intTrace A B x ∈ p by
    have hP : ((P ^ (e - 1) :)⁻¹ : FractionalIdeal B⁰ L) = a / p.map (algebraMap A B) := by
      apply inv_involutive.injective
      simp only [inv_inv, ha, FractionalIdeal.coeIdeal_mul, inv_div,
          mul_div_assoc]
      rw [div_self (by simpa), mul_one]
    rw [Ideal.dvd_iff_le, differentialIdeal_le_iff (K := K) (L := L) (pow_ne_zero _ hPbot), hP,
      Submodule.map_le_iff_le_comap]
    intro x hx
    rw [Submodule.restrictScalars_mem, FractionalIdeal.mem_coe,
      FractionalIdeal.mem_div_iff_of_nonzero (by simpa using hp')] at hx
    rw [Submodule.mem_comap, LinearMap.coe_restrictScalars, ← FractionalIdeal.coe_one,
      ← div_self (G₀ := FractionalIdeal A⁰ K) (a := p) (by simpa using hp),
      FractionalIdeal.mem_coe, FractionalIdeal.mem_div_iff_of_nonzero (by simpa using hp)]
    simp only [FractionalIdeal.mem_coeIdeal, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂] at hx
    intro y hy'
    obtain ⟨y, hy, rfl : algebraMap A K _ = _⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy'
    obtain ⟨z, hz, hz'⟩ := hx _ (Ideal.mem_map_of_mem _ hy)
    have : trace K L (algebraMap B L z) ∈ (p : FractionalIdeal A⁰ K) := by
      rw [← algebraMap_intTrace (A := A)]
      exact ⟨intTrace A B z, this z hz, rfl⟩
    rwa [mul_comm, ← smul_eq_mul, ← LinearMap.map_smul, Algebra.smul_def, mul_comm,
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A B L, ← hz']
  intros x hx
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← trace_quotient_eq_of_isDedekindDomain,
    ← isNilpotent_iff_eq_zero]
  refine trace_isNilpotent_of_isNilpotent ⟨e, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact (Ideal.dvd_iff_le.mp this) <| Ideal.pow_mem_pow hx _

lemma pow_sub_one_dvd_differentIdeal [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    {p : Ideal A} [p.IsMaximal] (P : Ideal B) (e : ℕ) (hp : p ≠ ⊥)
    (hP : P ^ e ∣ p.map (algebraMap A B)) : P ^ (e - 1) ∣ differentIdeal A B := by
  have : IsLocalization (algebraMapSubmonoid B A⁰) (FractionRing B) :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  have : FiniteDimensional (FractionRing A) (FractionRing B) := .of_isLocalization A B A⁰
  by_cases he : e = 0
  · rw [he, pow_zero]; exact one_dvd _
  exact pow_sub_one_dvd_differentIdeal_aux A (FractionRing A) (FractionRing B) _ he hp hP

theorem not_dvd_differentIdeal_of_intTrace_not_mem
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    {p : Ideal A} (P Q : Ideal B) (hP : P * Q = Ideal.map (algebraMap A B) p)
    (x : B) (hxQ : x ∈ Q) (hx : Algebra.intTrace A B x ∉ p) :
    ¬ P ∣ differentIdeal A B := by
  by_cases hp : p = ⊥
  · subst hp
    simp only [Ideal.map_bot, Ideal.mul_eq_bot] at hP
    obtain (rfl | rfl) := hP
    · rw [← Ideal.zero_eq_bot, zero_dvd_iff]
      exact differentIdeal_ne_bot
    · obtain rfl := hxQ
      simp at hx
  letI : Algebra (A ⧸ p) (B ⧸ Q) := Ideal.Quotient.algebraQuotientOfLEComap (by
      rw [← Ideal.map_le_iff_le_comap, ← hP]
      exact Ideal.mul_le_left)
  let K := FractionRing A
  let L := FractionRing B
  have : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L :=
    IsIntegralClosure.isLocalization _ K _ _
  have : FiniteDimensional K L := .of_isLocalization A B A⁰
  rw [Ideal.dvd_iff_le]
  intro H
  replace H := (mul_le_mul_right' H Q).trans_eq hP
  replace H := (FractionalIdeal.coeIdeal_le_coeIdeal' _ (P := L) le_rfl).mpr H
  rw [FractionalIdeal.coeIdeal_mul, coeIdeal_differentIdeal A K] at H
  replace H := FractionalIdeal.mul_le_mul_left H (FractionalIdeal.dual A K 1)
  simp only [ne_eq, FractionalIdeal.dual_eq_zero_iff, one_ne_zero, not_false_eq_true,
    mul_inv_cancel_left₀] at H
  apply hx
  suffices Algebra.trace K L (algebraMap B L x) ∈ (p : FractionalIdeal A⁰ K) by
    obtain ⟨y, hy, e⟩ := this
    rw [← Algebra.algebraMap_intTrace (A := A), Algebra.linearMap_apply,
      (IsLocalization.injective _ le_rfl).eq_iff] at e
    exact e ▸ hy
  refine FractionalIdeal.mul_induction_on (H ⟨_, hxQ, rfl⟩) ?_ ?_
  · rintro x hx _ ⟨y, hy, rfl⟩
    induction hy using Submodule.span_induction generalizing x with
    | mem y h =>
      obtain ⟨y, hy, rfl⟩ := h
      obtain ⟨z, hz⟩ :=
        (FractionalIdeal.mem_dual (by simp)).mp hx 1 ⟨1, trivial, (algebraMap B L).map_one⟩
      simp only [Algebra.traceForm_apply, mul_one] at hz
      refine ⟨z * y, Ideal.mul_mem_left _ _ hy, ?_⟩
      rw [Algebra.linearMap_apply, Algebra.linearMap_apply, mul_comm x,
        ← IsScalarTower.algebraMap_apply,
        ← Algebra.smul_def, LinearMap.map_smul_of_tower, ← hz,
        Algebra.smul_def, map_mul, mul_comm]
    | zero => simp
    | add y z _ _ hy hz =>
      simp only [map_add, mul_add]
      exact Submodule.add_mem _ (hy x hx) (hz x hx)
    | smul y z hz IH =>
      simpa [Algebra.smul_def, mul_assoc, -FractionalIdeal.mem_coeIdeal, mul_left_comm x] using
        IH _ (Submodule.smul_mem _ y hx)
  · simp only [map_add]
    exact fun _ _ h₁ h₂ ↦ Submodule.add_mem _ h₁ h₂

open nonZeroDivisors

theorem not_dvd_differentIdeal_of_isCoprime_of_isSeparable
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    {p : Ideal A} [p.IsMaximal] (P Q : Ideal B) [P.IsMaximal] [P.LiesOver p]
    (hPQ : IsCoprime P Q) (hP : P * Q = Ideal.map (algebraMap A B) p)
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)] :
    ¬ P ∣ differentIdeal A B := by
  letI : Algebra (A ⧸ p) (B ⧸ Q) := Ideal.Quotient.algebraQuotientOfLEComap (by
      rw [← Ideal.map_le_iff_le_comap, ← hP]
      exact Ideal.mul_le_left)
  have : IsScalarTower A (A ⧸ p) (B ⧸ Q) := .of_algebraMap_eq' rfl
  have : Module.Finite (A ⧸ p) (B ⧸ Q) :=
    Module.Finite.of_restrictScalars_finite A (A ⧸ p) (B ⧸ Q)
  letI e : (B ⧸ p.map (algebraMap A B)) ≃ₐ[A ⧸ p] ((B ⧸ P) × B ⧸ Q) :=
    { __ := (Ideal.quotEquivOfEq hP.symm).trans (Ideal.quotientMulEquivQuotientProd P Q hPQ),
      commutes' := Quotient.ind fun _ ↦ rfl }
  obtain ⟨x, hx⟩ : ∃ x, Algebra.trace (A ⧸ p) (B ⧸ P) x ≠ 0 := by
    simpa [LinearMap.ext_iff] using Algebra.trace_ne_zero (A ⧸ p) (B ⧸ P)
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (e.symm (x, 0))
  refine not_dvd_differentIdeal_of_intTrace_not_mem A P Q hP y ?_ ?_
  · simpa [e, Ideal.Quotient.eq_zero_iff_mem] using congr((e $hy).2)
  · rw [← Ideal.Quotient.eq_zero_iff_mem, ← Algebra.trace_quotient_eq_of_isDedekindDomain,
      hy, Algebra.trace_eq_of_algEquiv, Algebra.trace_prod_apply]
    simpa

theorem not_dvd_differentIdeal_of_isCoprime
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    {p : Ideal A} [p.IsMaximal] [Finite (A ⧸ p)] (P Q : Ideal B) [P.IsMaximal]
    (hPQ : IsCoprime P Q) (hP : P * Q = Ideal.map (algebraMap A B) p) :
    ¬ P ∣ differentIdeal A B := by
  have : P.LiesOver p := by
    constructor
    refine ‹p.IsMaximal›.eq_of_le ?_ ?_
    · simpa using ‹P.IsMaximal›.ne_top
    · rw [← Ideal.map_le_iff_le_comap, ← hP]
      exact Ideal.mul_le_right
  exact not_dvd_differentIdeal_of_isCoprime_of_isSeparable A P Q hPQ hP

lemma dvd_differentIdeal_of_not_isSeparable
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    {p : Ideal A} [p.IsMaximal] (hp : p ≠ ⊥)
    (P : Ideal B) [P.IsMaximal] [P.LiesOver p]
    (H : ¬ Algebra.IsSeparable (A ⧸ p) (B ⧸ P)) : P ∣ differentIdeal A B := by
  obtain ⟨a, ha⟩ : P ∣ p.map (algebraMap A B) :=
    Ideal.dvd_iff_le.mpr (Ideal.map_le_iff_le_comap.mpr Ideal.LiesOver.over.le)
  by_cases hPa : P ∣ a
  · simpa using pow_sub_one_dvd_differentIdeal A P 2 hp
      (by rw [pow_two, ha]; exact mul_dvd_mul_left _ hPa)
  let K := FractionRing A
  let L := FractionRing B
  have : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L :=
    IsIntegralClosure.isLocalization _ K _ _
  have : FiniteDimensional K L := .of_isLocalization A B A⁰
  have hp' := (Ideal.map_eq_bot_iff_of_injective
    (FaithfulSMul.algebraMap_injective A B)).not.mpr hp
  have habot : a ≠ ⊥ := fun ha' ↦ hp' (by simpa [ha'] using ha)
  have hPbot : P ≠ ⊥ := by
    rintro rfl; apply hp'
    rwa [Ideal.bot_mul] at ha
  suffices ∀ x ∈ a, Algebra.intTrace A B x ∈ p by
    have hP : ((P :)⁻¹ : FractionalIdeal B⁰ L) = a / p.map (algebraMap A B) := by
      apply inv_involutive.injective
      simp only [ha, FractionalIdeal.coeIdeal_mul, inv_div, mul_div_assoc]
      rw [div_self (by simpa), mul_one, inv_inv]
    rw [Ideal.dvd_iff_le, differentialIdeal_le_iff (K := K) (L := L) hPbot, hP,
      Submodule.map_le_iff_le_comap]
    intro x hx
    rw [Submodule.restrictScalars_mem, FractionalIdeal.mem_coe,
      FractionalIdeal.mem_div_iff_of_nonzero (by simpa using hp')] at hx
    rw [Submodule.mem_comap, LinearMap.coe_restrictScalars, ← FractionalIdeal.coe_one,
      ← div_self (G₀ := FractionalIdeal A⁰ K) (a := p) (by simpa using hp),
      FractionalIdeal.mem_coe, FractionalIdeal.mem_div_iff_of_nonzero (by simpa using hp)]
    simp only [FractionalIdeal.mem_coeIdeal, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂] at hx
    intro y hy'
    obtain ⟨y, hy, rfl : algebraMap A K _ = _⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy'
    obtain ⟨z, hz, hz'⟩ := hx _ (Ideal.mem_map_of_mem _ hy)
    have : Algebra.trace K L (algebraMap B L z) ∈ (p : FractionalIdeal A⁰ K) := by
      rw [← Algebra.algebraMap_intTrace (A := A)]
      exact ⟨Algebra.intTrace A B z, this z hz, rfl⟩
    rwa [mul_comm, ← smul_eq_mul, ← LinearMap.map_smul, Algebra.smul_def, mul_comm,
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A B L, ← hz']
  intros x hx
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Algebra.trace_quotient_eq_of_isDedekindDomain]
  letI : Algebra (A ⧸ p) (B ⧸ a) :=
    Ideal.Quotient.algebraQuotientOfLEComap (Ideal.map_le_iff_le_comap.mp
      (Ideal.dvd_iff_le.mp ⟨_, ha.trans (mul_comm _ _)⟩))
  have : IsScalarTower A (A ⧸ p) (B ⧸ a) := .of_algebraMap_eq' rfl
  have : Module.Finite (A ⧸ p) (B ⧸ a) := .of_restrictScalars_finite A _ _
  have := ((Ideal.prime_iff_isPrime hPbot).mpr inferInstance)
  rw [← this.irreducible.gcd_eq_one_iff, ← Ideal.isCoprime_iff_gcd] at hPa
  letI e : (B ⧸ p.map (algebraMap A B)) ≃ₐ[A ⧸ p] ((B ⧸ P) × B ⧸ a) :=
    { __ := (Ideal.quotEquivOfEq ha).trans (Ideal.quotientMulEquivQuotientProd P a hPa),
      commutes' := Quotient.ind fun _ ↦ rfl }
  have hx' : (e (Ideal.Quotient.mk _ x)).2 = 0 := by
    simpa [e, Ideal.Quotient.eq_zero_iff_mem]
  rw [← Algebra.trace_eq_of_algEquiv e, Algebra.trace_prod_apply,
    Algebra.trace_eq_zero_of_not_isSeparable H, LinearMap.zero_apply, zero_add, hx', map_zero]

variable {A}

/-- A prime does not divide the different ideal iff it is unramified. -/
theorem not_dvd_differentIdeal_iff
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)] {P : Ideal B} [P.IsPrime] :
    ¬ P ∣ differentIdeal A B ↔ Algebra.IsUnramifiedAt A P := by
  classical
  rcases eq_or_ne P ⊥ with rfl | hPbot
  · simp_rw [← Ideal.zero_eq_bot, zero_dvd_iff]
    simp only [Submodule.zero_eq_bot, differentIdeal_ne_bot, not_false_eq_true, true_iff]
    let K := FractionRing A
    let L := FractionRing B
    have : FiniteDimensional K L := .of_isLocalization A B A⁰
    have : IsLocalization B⁰ (Localization.AtPrime (⊥ : Ideal B)) := by
      convert (inferInstanceAs
        (IsLocalization (⊥ : Ideal B).primeCompl (Localization.AtPrime (⊥ : Ideal B))))
      ext; simp [Ideal.primeCompl]
    refine (Algebra.FormallyUnramified.iff_of_equiv (A := L)
      ((IsLocalization.algEquiv B⁰ _ _).restrictScalars A)).mp ?_
    have : Algebra.FormallyUnramified K L := by
      rwa [Algebra.FormallyUnramified.iff_isSeparable]
    refine .comp A K L
  have hp : P.under A ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot hPbot
  have hp' := (Ideal.map_eq_bot_iff_of_injective
    (FaithfulSMul.algebraMap_injective A B)).not.mpr hp
  have := Ideal.IsPrime.isMaximal inferInstance hPbot
  constructor
  · intro H
    · rw [Algebra.isUnramifiedAt_iff_map_eq (p := P.under A)]
      constructor
      · suffices Algebra.IsSeparable (A ⧸ P.under A) (B ⧸ P) by infer_instance
        contrapose! H
        exact dvd_differentIdeal_of_not_isSeparable A hp P H
      · rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_one_iff hPbot Ideal.map_comap_le]
        apply Ideal.ramificationIdx_spec
        · simp [Ideal.map_le_iff_le_comap]
        · contrapose! H
          rw [← pow_one P, show 1 = 2 - 1 by norm_num]
          apply pow_sub_one_dvd_differentIdeal _ _ _ hp
          simpa [Ideal.dvd_iff_le] using H
  · intro H
    obtain ⟨Q, h₁, h₂⟩ := Ideal.eq_prime_pow_mul_coprime hp' P
    rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count hp' ‹_› hPbot,
      Ideal.ramificationIdx_eq_one_of_isUnramifiedAt hPbot, pow_one] at h₂
    obtain ⟨h₃, h₄⟩ := (Algebra.isUnramifiedAt_iff_map_eq (p := P.under A) _ _).mp H
    exact not_dvd_differentIdeal_of_isCoprime_of_isSeparable
      A P Q (Ideal.isCoprime_iff_sup_eq.mpr h₁) h₂.symm

/-- A prime divides the different ideal iff it is ramified. -/
theorem dvd_differentIdeal_iff
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)] {P : Ideal B} [P.IsPrime] :
    P ∣ differentIdeal A B ↔ ¬ Algebra.IsUnramifiedAt A P :=
  iff_not_comm.mp not_dvd_differentIdeal_iff.symm

end
