/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.Complex.Spectrum
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Restrict
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
public import Mathlib.Analysis.CStarAlgebra.Unitization
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Analysis.RCLike.Lemmas

/-! # Instances of the continuous functional calculus

## Main theorems

* `IsSelfAdjoint.instContinuousFunctionalCalculus`: the continuous functional calculus for
  selfadjoint elements in a `ℂ`-algebra with a continuous functional calculus for normal elements
  and where every element has compact spectrum. In particular, this includes unital C⋆-algebras
  over `ℂ`.
* `Nonneg.instContinuousFunctionalCalculus`: the continuous functional calculus for nonnegative
  elements in an `ℝ`-algebra with a continuous functional calculus for selfadjoint elements,
  where every element has compact spectrum, and where nonnegative elements have nonnegative
  spectrum. In particular, this includes unital C⋆-algebras over `ℝ`.

## Tags

continuous functional calculus, normal, selfadjoint
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Topology

noncomputable section

local notation "σₙ" => quasispectrum
local notation "σ" => spectrum

/-!
### Pull back a non-unital instance from a unital one on the unitization
-/

section RCLike

variable {𝕜 A : Type*} [RCLike 𝕜] [NonUnitalNormedRing A] [StarRing A]
variable [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
variable [StarModule 𝕜 A] {p : A → Prop} {p₁ : Unitization 𝕜 A → Prop}

local postfix:max "⁺¹" => Unitization 𝕜

variable (hp₁ : ∀ {x : A}, p₁ x ↔ p x) (a : A) (ha : p a)
variable [ContinuousFunctionalCalculus.IsClosedEmbedding 𝕜 (Unitization 𝕜 A) p₁]

open scoped ContinuousMapZero


open Unitization in
/--
This is an auxiliary definition used for constructing an instance of the non-unital continuous
functional calculus given an instance of the unital one on the unitization.

This is the natural non-unital star homomorphism obtained from the chain
```lean
calc
  C(σₙ 𝕜 a, 𝕜)₀ →⋆ₙₐ[𝕜] C(σₙ 𝕜 a, 𝕜) := ContinuousMapZero.toContinuousMapHom
  _             ≃⋆[𝕜] C(σ 𝕜 (↑a : A⁺¹), 𝕜) := Homeomorph.compStarAlgEquiv'
  _             →⋆ₐ[𝕜] A⁺¹ := cfcHom
```
This range of this map is contained in the range of `(↑) : A → A⁺¹` (see `cfcₙAux_mem_range_inr`),
and so we may restrict it to `A` to get the necessary homomorphism for the non-unital continuous
functional calculus.
-/
noncomputable def cfcₙAux : C(σₙ 𝕜 a, 𝕜)₀ →⋆ₙₐ[𝕜] A⁺¹ :=
  (cfcHom (R := 𝕜) (hp₁.mpr ha) : C(σ 𝕜 (a : A⁺¹), 𝕜) →⋆ₙₐ[𝕜] A⁺¹) |>.comp
    (Homeomorph.compStarAlgEquiv' 𝕜 𝕜 <| .setCongr <| (quasispectrum_eq_spectrum_inr' 𝕜 𝕜 a).symm)
    |>.comp ContinuousMapZero.toContinuousMapHom

lemma cfcₙAux_id : cfcₙAux hp₁ a ha (.id _) = a := cfcHom_id (hp₁.mpr ha)

lemma continuous_cfcₙAux : Continuous (cfcₙAux hp₁ a ha) :=
  (cfcHom_continuous (hp₁.mpr ha)).comp <|
    (ContinuousMap.continuous_precomp _).comp <|
    ContinuousMapZero.isEmbedding_toContinuousMap.continuous

lemma cfcₙAux_injective : Function.Injective (cfcₙAux hp₁ a ha) :=
  (cfcHom_injective (hp₁.mpr ha)).comp <|
    .comp (Equiv.injective _) ContinuousMapZero.isEmbedding_toContinuousMap.injective

lemma spec_cfcₙAux (f : C(σₙ 𝕜 a, 𝕜)₀) : σ 𝕜 (cfcₙAux hp₁ a ha f) = Set.range f := by
  rw [cfcₙAux, NonUnitalStarAlgHom.comp_assoc, NonUnitalStarAlgHom.comp_apply]
  simp only [NonUnitalStarAlgHom.comp_apply, NonUnitalStarAlgHom.coe_coe]
  rw [cfcHom_map_spectrum (hp₁.mpr ha) (R := 𝕜) _]
  simp

-- generalize variables?
instance Unitization.instT2Space (𝕜 A : Type*)
    [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] :
    T2Space (Unitization 𝕜 A) :=
  Unitization.uniformEquivProd.symm.toHomeomorph.t2Space

open Unitization in
lemma isClosedEmbedding_cfcₙAux : IsClosedEmbedding (cfcₙAux hp₁ a ha) := by
  simp only [cfcₙAux, NonUnitalStarAlgHom.coe_comp]
  refine ((cfcHom_isClosedEmbedding _ (hp₁.mpr ha)).comp ?_).comp
    ContinuousMapZero.isClosedEmbedding_toContinuousMap
  let e : C(σₙ 𝕜 a, 𝕜) ≃ₜ C(σ 𝕜 (a : A⁺¹), 𝕜) :=
    (Homeomorph.setCongr (quasispectrum_eq_spectrum_inr' 𝕜 𝕜 a)).arrowCongr (.refl _)
  exact e.isClosedEmbedding

variable [CompleteSpace A]

lemma cfcₙAux_mem_range_inr (f : C(σₙ 𝕜 a, 𝕜)₀) :
    cfcₙAux hp₁ a ha f ∈ NonUnitalStarAlgHom.range (Unitization.inrNonUnitalStarAlgHom 𝕜 A) := by
  have h₁ := (continuous_cfcₙAux hp₁ a ha).range_subset_closure_image_dense
    (ContinuousMapZero.adjoin_id_dense (σₙ 𝕜 a)) ⟨f, rfl⟩
  rw [← SetLike.mem_coe]
  refine closure_minimal ?_ ?_ h₁
  · rw [← NonUnitalStarSubalgebra.coe_map, SetLike.coe_subset_coe, NonUnitalStarSubalgebra.map_le]
    apply NonUnitalStarAlgebra.adjoin_le
    apply Set.singleton_subset_iff.mpr
    rw [SetLike.mem_coe, NonUnitalStarSubalgebra.mem_comap, cfcₙAux_id hp₁ a ha]
    exact ⟨a, rfl⟩
  · have : Continuous (Unitization.fst (R := 𝕜) (A := A)) :=
      Unitization.uniformEquivProd.continuous.fst
    simp only [NonUnitalStarAlgHom.coe_range]
    convert IsClosed.preimage this (isClosed_singleton (x := 0))
    aesop


-- generalize variables?
@[fun_prop]
protected theorem Unitization.continuous_snd (𝕜 A : Type*)
    [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] :
    Continuous (snd : Unitization 𝕜 A → A) :=
  continuous_snd.comp <| map_continuous Unitization.uniformEquivProd.toHomeomorph

variable [CStarRing A]

include hp₁ in
open Unitization NonUnitalStarAlgHom in
theorem RCLike.nonUnitalContinuousFunctionalCalculus :
    NonUnitalContinuousFunctionalCalculus 𝕜 A p where
  predicate_zero := by
    rw [← hp₁, Unitization.inr_zero 𝕜]
    exact cfc_predicate_zero 𝕜
  exists_cfc_of_predicate a ha := by
    let ψ : C(σₙ 𝕜 a, 𝕜)₀ →⋆ₙₐ[𝕜] A := comp (inrRangeEquiv 𝕜 A).symm <|
      codRestrict (cfcₙAux hp₁ a ha) _ (cfcₙAux_mem_range_inr hp₁ a ha)
    have coe_ψ (f : C(σₙ 𝕜 a, 𝕜)₀) : ψ f = cfcₙAux hp₁ a ha f :=
      congr_arg Subtype.val <| (inrRangeEquiv 𝕜 A).apply_symm_apply
        ⟨cfcₙAux hp₁ a ha f, cfcₙAux_mem_range_inr hp₁ a ha f⟩
    refine ⟨ψ, ?continuous, ?injective, ?map_id, fun f ↦ ?map_spec, fun f ↦ ?isStarNormal⟩
    case continuous =>
      rw [isometry_inr (𝕜 := 𝕜) |>.isEmbedding.continuous_iff]
      have := continuous_cfcₙAux hp₁ a ha
      simp only [coe_comp, NonUnitalStarAlgHom.coe_coe, Function.comp_def,
        inrRangeEquiv_symm_apply, coe_codRestrict, ψ]
      fun_prop
    case injective => simpa [ψ] using
      (inrRangeEquiv 𝕜 A).symm.injective.comp (cfcₙAux_injective hp₁ a ha).codRestrict
    case map_id => exact inr_injective (R := 𝕜) <| coe_ψ _ ▸ cfcₙAux_id hp₁ a ha
    case map_spec =>
      exact quasispectrum_eq_spectrum_inr' 𝕜 𝕜 (ψ f) ▸ coe_ψ _ ▸ spec_cfcₙAux hp₁ a ha f
    case isStarNormal => exact hp₁.mp <| coe_ψ _ ▸ cfcHom_predicate (R := 𝕜) (hp₁.mpr ha) _

open Unitization in
open scoped NonUnitalContinuousFunctionalCalculus in
lemma inrNonUnitalStarAlgHom_comp_cfcₙHom_eq_cfcₙAux (a : A) (ha : p a) :
    letI _ := RCLike.nonUnitalContinuousFunctionalCalculus hp₁
    (inrNonUnitalStarAlgHom 𝕜 A).comp (cfcₙHom ha) = cfcₙAux hp₁ a ha := by
  letI _ := RCLike.nonUnitalContinuousFunctionalCalculus hp₁
  apply ContinuousMapZero.UniqueHom.eq_of_continuous_of_map_id _ _ _
    (Unitization.continuous_inr.comp <| cfcₙHom_continuous ha)
    (continuous_cfcₙAux hp₁ a ha)
    (by simp [cfcₙHom_id ha, cfcₙAux_id hp₁ a ha])
  all_goals infer_instance


include hp₁ in
open Unitization NonUnitalStarAlgHom in
theorem RCLike.nonUnitalContinuousFunctionalCalculusIsClosedEmbedding :
    NonUnitalContinuousFunctionalCalculus.IsClosedEmbedding 𝕜 A p where
  toNonUnitalContinuousFunctionalCalculus := RCLike.nonUnitalContinuousFunctionalCalculus hp₁
  isClosedEmbedding a ha := by
    apply isometry_inr (𝕜 := 𝕜) (A := A) |>.isClosedEmbedding |>.of_comp_iff.mp
    convert isClosedEmbedding_cfcₙAux hp₁ a ha
    congrm(⇑$(inrNonUnitalStarAlgHom_comp_cfcₙHom_eq_cfcₙAux hp₁ a ha))

end RCLike

/-!
### Continuous functional calculus for selfadjoint elements
-/

section SelfAdjointNonUnital

variable {A : Type*} [TopologicalSpace A] [NonUnitalRing A] [StarRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  [NonUnitalContinuousFunctionalCalculus ℂ A IsStarNormal]

/-- An element in a non-unital C⋆-algebra is selfadjoint if and only if it is normal and its
quasispectrum is contained in `ℝ`. -/
lemma isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts {a : A} :
    IsSelfAdjoint a ↔ IsStarNormal a ∧ QuasispectrumRestricts a Complex.reCLM := by
  refine ⟨fun ha ↦ ⟨ha.isStarNormal, ⟨fun x hx ↦ ?_, Complex.ofReal_re⟩⟩, ?_⟩
  · have := eqOn_of_cfcₙ_eq_cfcₙ <|
      (cfcₙ_star (id : ℂ → ℂ) a).symm ▸ (cfcₙ_id ℂ a).symm ▸ ha.star_eq
    exact Complex.conj_eq_iff_re.mp (by simpa using this hx)
  · rintro ⟨ha₁, ha₂⟩
    rw [isSelfAdjoint_iff]
    nth_rw 2 [← cfcₙ_id ℂ a]
    rw [← cfcₙ_star_id a (R := ℂ)]
    refine cfcₙ_congr fun x hx ↦ ?_
    obtain ⟨x, -, rfl⟩ := ha₂.algebraMap_image.symm ▸ hx
    exact Complex.conj_ofReal _

lemma IsSelfAdjoint.quasispectrumRestricts {a : A} (ha : IsSelfAdjoint a) :
    QuasispectrumRestricts a Complex.reCLM :=
  isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts |>.mp ha |>.2

@[deprecated (since := "2025-09-16")]
alias isSelfAdjoint_iff_isStarNormal_and_spectrumRestricts :=
  isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts

/-- A normal element whose `ℂ`-quasispectrum is contained in `ℝ` is selfadjoint. -/
lemma QuasispectrumRestricts.isSelfAdjoint (a : A) (ha : QuasispectrumRestricts a Complex.reCLM)
    [IsStarNormal a] : IsSelfAdjoint a :=
  isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts.mpr ⟨‹_›, ha⟩

@[deprecated (since := "2025-09-16")]
alias SpectrumRestricts.isSelfAdjoint := QuasispectrumRestricts.isSelfAdjoint

instance IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus :
    NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint :=
  QuasispectrumRestricts.cfc (q := IsStarNormal) (p := IsSelfAdjoint) Complex.reCLM
    Complex.isometry_ofReal.isClosedEmbedding (.zero _)
    (fun _ ↦ isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts)

end SelfAdjointNonUnital

section SelfAdjointUnital


variable {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A] [Algebra ℂ A]
  [ContinuousFunctionalCalculus ℂ A IsStarNormal]

lemma IsSelfAdjoint.spectrumRestricts {a : A} (ha : IsSelfAdjoint a) :
    SpectrumRestricts a Complex.reCLM :=
  ha.quasispectrumRestricts

instance IsSelfAdjoint.instContinuousFunctionalCalculus :
    ContinuousFunctionalCalculus ℝ A IsSelfAdjoint :=
  SpectrumRestricts.cfc (q := IsStarNormal) (p := IsSelfAdjoint) Complex.reCLM
    Complex.isometry_ofReal.isClosedEmbedding (.zero _)
    (fun _ ↦ isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts)

lemma IsSelfAdjoint.spectrum_nonempty {A : Type*} [Ring A] [StarRing A]
    [TopologicalSpace A] [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    [Nontrivial A] {a : A} (ha : IsSelfAdjoint a) : (σ ℝ a).Nonempty :=
  CFC.spectrum_nonempty ℝ a ha

end SelfAdjointUnital

/-!
### Continuous functional calculus for nonnegative elements
-/

section Nonneg

lemma CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts {A : Type*} [NonUnitalRing A]
    [StarRing A] [TopologicalSpace A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
    [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    {a : A} (ha₁ : IsSelfAdjoint a) (ha₂ : QuasispectrumRestricts a ContinuousMap.realToNNReal) :
    ∃ x : A, IsSelfAdjoint x ∧ QuasispectrumRestricts x ContinuousMap.realToNNReal ∧ x * x = a := by
  use cfcₙ (√·) a, cfcₙ_predicate (√·) a
  constructor
  · simpa only [QuasispectrumRestricts.nnreal_iff, cfcₙ_map_quasispectrum (√·) a,
      Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
        using fun x _ ↦ Real.sqrt_nonneg x
  · rw [← cfcₙ_mul ..]
    nth_rw 2 [← cfcₙ_id ℝ a]
    apply cfcₙ_congr fun x hx ↦ ?_
    rw [QuasispectrumRestricts.nnreal_iff] at ha₂
    apply ha₂ x at hx
    simp [← sq, Real.sq_sqrt hx]

@[deprecated (since := "2025-09-16")]
alias CFC.exists_sqrt_of_isSelfAdjoint_of_spectrumRestricts :=
  CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts

variable {A : Type*} [NonUnitalRing A] [PartialOrder A] [StarRing A] [StarOrderedRing A]
variable [TopologicalSpace A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
variable [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
variable [NonnegSpectrumClass ℝ A]

lemma nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts {a : A} :
    0 ≤ a ↔ IsSelfAdjoint a ∧ QuasispectrumRestricts a ContinuousMap.realToNNReal := by
  refine ⟨fun ha ↦ ⟨.of_nonneg ha, .nnreal_of_nonneg ha⟩, ?_⟩
  rintro ⟨ha₁, ha₂⟩
  obtain ⟨x, hx, -, rfl⟩ := CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts ha₁ ha₂
  simpa [sq, hx.star_eq] using star_mul_self_nonneg x

@[deprecated (since := "2025-09-16")]
alias nonneg_iff_isSelfAdjoint_and_spectrumRestricts :=
  nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts

open NNReal in
instance Nonneg.instNonUnitalContinuousFunctionalCalculus :
    NonUnitalContinuousFunctionalCalculus ℝ≥0 A (0 ≤ ·) :=
  QuasispectrumRestricts.cfc (q := IsSelfAdjoint) ContinuousMap.realToNNReal
    isometry_subtype_coe.isClosedEmbedding le_rfl
    (fun _ ↦ nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts)

/-- In a C⋆-algebra, commuting nonnegative elements have nonnegative products. -/
lemma Commute.mul_nonneg {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : Commute a b) :
    0 ≤ a * b := by
  rw [nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts]
  refine ⟨ha.isSelfAdjoint.commute_iff hb.isSelfAdjoint |>.mp h, ?_⟩
  rw [nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts] at hb
  obtain ⟨x, hx₁, hx₂, rfl⟩ := CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts hb.1 hb.2
  have hx := nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts.mpr ⟨hx₁, hx₂⟩
  rw [← mul_assoc, quasispectrumRestricts_iff, quasispectrum.mul_comm,
    ← quasispectrumRestricts_iff, ← mul_assoc]
  exact QuasispectrumRestricts.nnreal_of_nonneg <| conjugate_nonneg_of_nonneg ha hx

lemma commute_iff_mul_nonneg {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Commute a b ↔ 0 ≤ a * b :=
  ⟨Commute.mul_nonneg ha hb,
  fun h => ha.isSelfAdjoint.commute_iff hb.isSelfAdjoint |>.mpr h.isSelfAdjoint⟩

open NNReal in
lemma NNReal.spectrum_nonempty {A : Type*} [Ring A] [StarRing A] [LE A]
    [TopologicalSpace A] [Algebra ℝ≥0 A] [ContinuousFunctionalCalculus ℝ≥0 A (0 ≤ ·)]
    [Nontrivial A] {a : A} (ha : 0 ≤ a) : (spectrum ℝ≥0 a).Nonempty :=
  CFC.spectrum_nonempty ℝ≥0 a ha

end Nonneg

section Nonneg

variable {A : Type*} [Ring A] [PartialOrder A] [StarRing A] [StarOrderedRing A] [TopologicalSpace A]
variable [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
variable [NonnegSpectrumClass ℝ A]

open NNReal in
instance Nonneg.instContinuousFunctionalCalculus :
    ContinuousFunctionalCalculus ℝ≥0 A (0 ≤ ·) :=
  SpectrumRestricts.cfc (q := IsSelfAdjoint) ContinuousMap.realToNNReal
    isometry_subtype_coe.isClosedEmbedding le_rfl
    (fun _ ↦ nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts)

theorem IsStrictlyPositive.commute_iff {a b : A} (ha : IsStrictlyPositive a)
    (hb : IsStrictlyPositive b) : Commute a b ↔ IsStrictlyPositive (a * b) := by
  rw [commute_iff_mul_nonneg ha.nonneg hb.nonneg]
  exact ⟨fun h => ha.isUnit.mul hb.isUnit |>.isStrictlyPositive h, fun h => h.nonneg⟩

end Nonneg

/-!
### The restriction of a continuous functional calculus is equal to the original one
-/
section RealEqComplex

variable {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A] [Algebra ℂ A]
  [ContinuousFunctionalCalculus ℂ A IsStarNormal] [T2Space A]

lemma cfcHom_real_eq_restrict {a : A} (ha : IsSelfAdjoint a) :
    cfcHom ha =
      ha.spectrumRestricts.starAlgHom (R := ℝ) (S := ℂ)
        (cfcHom ha.isStarNormal) (f := Complex.reCLM) :=
  ha.spectrumRestricts.cfcHom_eq_restrict _ ha ha.isStarNormal

lemma cfc_real_eq_complex {a : A} (f : ℝ → ℝ) (ha : IsSelfAdjoint a := by cfc_tac) :
    cfc f a = cfc (fun x ↦ f x.re : ℂ → ℂ) a := by
  exact ha.spectrumRestricts.cfc_eq_restrict (f := Complex.reCLM)
    Complex.isometry_ofReal.isClosedEmbedding ha ha.isStarNormal f

lemma cfc_complex_eq_real {f : ℂ → ℂ} (a : A) (hf_real : ∀ x ∈ spectrum ℂ a, star (f x) = f x)
    (ha : IsSelfAdjoint a := by cfc_tac) :
    cfc f a = cfc (fun x : ℝ ↦ (f x).re) a := by
  rw [cfc_real_eq_complex ..]
  refine cfc_congr fun x hx ↦ ?_
  simp_rw [RCLike.star_def, RCLike.conj_eq_iff_re, RCLike.re_eq_complex_re,
    RCLike.ofReal_eq_complex_ofReal] at hf_real
  rw [← SpectrumRestricts.real_iff.mp ha.spectrumRestricts _ hx, hf_real _ hx]

end RealEqComplex

section RealEqComplexNonUnital

variable {A : Type*} [TopologicalSpace A] [NonUnitalRing A] [StarRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [T2Space A]
  [NonUnitalContinuousFunctionalCalculus ℂ A IsStarNormal]

lemma cfcₙHom_real_eq_restrict {a : A} (ha : IsSelfAdjoint a) :
    cfcₙHom ha = ha.quasispectrumRestricts.nonUnitalStarAlgHom (cfcₙHom ha.isStarNormal)
      (R := ℝ) (S := ℂ) (f := Complex.reCLM) :=
  ha.quasispectrumRestricts.cfcₙHom_eq_restrict _ ha ha.isStarNormal

lemma cfcₙ_real_eq_complex {a : A} (f : ℝ → ℝ) (ha : IsSelfAdjoint a := by cfc_tac) :
    cfcₙ f a = cfcₙ (fun x ↦ f x.re : ℂ → ℂ) a := by
  exact ha.quasispectrumRestricts.cfcₙ_eq_restrict (f := Complex.reCLM)
    Complex.isometry_ofReal.isClosedEmbedding ha ha.isStarNormal f

lemma cfcₙ_complex_eq_real {f : ℂ → ℂ} (a : A) (hf_real : ∀ x ∈ σₙ ℂ a, star (f x) = f x)
    (ha : IsSelfAdjoint a := by cfc_tac) :
    cfcₙ f a = cfcₙ (fun x : ℝ ↦ (f x).re) a := by
  rw [cfcₙ_real_eq_complex ..]
  refine cfcₙ_congr fun x hx ↦ ?_
  simp_rw [RCLike.star_def, RCLike.conj_eq_iff_re, RCLike.re_eq_complex_re,
    RCLike.ofReal_eq_complex_ofReal] at hf_real
  rw [← QuasispectrumRestricts.real_iff.mp ha.quasispectrumRestricts _ hx, hf_real _ hx]

end RealEqComplexNonUnital

section NNRealEqReal

open NNReal

variable {A : Type*} [TopologicalSpace A] [Ring A] [PartialOrder A] [StarRing A]
  [StarOrderedRing A] [Algebra ℝ A] [IsTopologicalRing A] [T2Space A]
  [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A]

lemma cfcHom_nnreal_eq_restrict {a : A} (ha : 0 ≤ a) :
    cfcHom ha = (SpectrumRestricts.nnreal_of_nonneg ha).starAlgHom
      (cfcHom (IsSelfAdjoint.of_nonneg ha)) := by
  apply (SpectrumRestricts.nnreal_of_nonneg ha).cfcHom_eq_restrict _

lemma cfc_nnreal_eq_real (f : ℝ≥0 → ℝ≥0) (a : A) (ha : 0 ≤ a := by cfc_tac) :
    cfc f a = cfc (fun x ↦ f x.toNNReal : ℝ → ℝ) a := by
  apply (SpectrumRestricts.nnreal_of_nonneg ha).cfc_eq_restrict _
    isometry_subtype_coe.isClosedEmbedding ha (.of_nonneg ha)

lemma cfc_real_eq_nnreal {f : ℝ → ℝ} (a : A) (hf_nonneg : ∀ x ∈ spectrum ℝ a, 0 ≤ f x)
    (ha : 0 ≤ a := by cfc_tac) : cfc f a = cfc (fun x : ℝ≥0 ↦ (f x).toNNReal) a := by
  rw [cfc_nnreal_eq_real ..]
  refine cfc_congr fun x hx ↦ ?_
  rw [x.coe_toNNReal (spectrum_nonneg_of_nonneg ha hx), (f x).coe_toNNReal (hf_nonneg x hx)]

end NNRealEqReal

section NNRealEqRealNonUnital

open NNReal

variable {A : Type*} [TopologicalSpace A] [NonUnitalRing A] [PartialOrder A] [StarRing A]
  [StarOrderedRing A] [Module ℝ A] [IsTopologicalRing A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
  [T2Space A] [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A]

lemma cfcₙHom_nnreal_eq_restrict {a : A} (ha : 0 ≤ a) :
    cfcₙHom ha = (QuasispectrumRestricts.nnreal_of_nonneg ha).nonUnitalStarAlgHom
      (cfcₙHom (IsSelfAdjoint.of_nonneg ha)) := by
  apply (QuasispectrumRestricts.nnreal_of_nonneg ha).cfcₙHom_eq_restrict _

lemma cfcₙ_nnreal_eq_real (f : ℝ≥0 → ℝ≥0) (a : A) (ha : 0 ≤ a := by cfc_tac) :
    cfcₙ f a = cfcₙ (fun x ↦ f x.toNNReal : ℝ → ℝ) a := by
  apply (QuasispectrumRestricts.nnreal_of_nonneg ha).cfcₙ_eq_restrict _
    isometry_subtype_coe.isClosedEmbedding ha (.of_nonneg ha)

lemma cfcₙ_real_eq_nnreal {f : ℝ → ℝ} (a : A) (hf_nonneg : ∀ x ∈ σₙ ℝ a, 0 ≤ f x)
    (ha : 0 ≤ a := by cfc_tac) : cfcₙ f a = cfcₙ (fun x : ℝ≥0 ↦ (f x).toNNReal) a := by
  rw [cfcₙ_nnreal_eq_real ..]
  refine cfcₙ_congr fun x hx ↦ ?_
  rw [x.coe_toNNReal (quasispectrum_nonneg_of_nonneg _ ha _ hx),
    (f x).coe_toNNReal (hf_nonneg x hx)]

end NNRealEqRealNonUnital

end
