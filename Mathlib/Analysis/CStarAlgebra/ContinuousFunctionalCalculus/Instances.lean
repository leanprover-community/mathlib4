/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Restrict
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.Unitization
import Mathlib.Analysis.Normed.Algebra.Spectrum

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
variable [ContinuousFunctionalCalculus 𝕜 p₁]

open scoped ContinuousMapZero


open Unitization in
/--
This is an auxiliary definition used for constructing an instance of the non-unital continuous
functional calculus given a instance of the unital one on the unitization.

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

lemma cfcₙAux_id : cfcₙAux hp₁ a ha (ContinuousMapZero.id rfl) = a := cfcHom_id (hp₁.mpr ha)

open Unitization in
lemma isClosedEmbedding_cfcₙAux : IsClosedEmbedding (cfcₙAux hp₁ a ha) := by
  simp only [cfcₙAux, NonUnitalStarAlgHom.coe_comp]
  refine ((cfcHom_isClosedEmbedding (hp₁.mpr ha)).comp ?_).comp
    ContinuousMapZero.isClosedEmbedding_toContinuousMap
  let e : C(σₙ 𝕜 a, 𝕜) ≃ₜ C(σ 𝕜 (a : A⁺¹), 𝕜) :=
    (Homeomorph.setCongr (quasispectrum_eq_spectrum_inr' 𝕜 𝕜 a)).arrowCongr (.refl _)
  exact e.isClosedEmbedding

@[deprecated (since := "2024-10-20")]
alias closedEmbedding_cfcₙAux := isClosedEmbedding_cfcₙAux

lemma spec_cfcₙAux (f : C(σₙ 𝕜 a, 𝕜)₀) : σ 𝕜 (cfcₙAux hp₁ a ha f) = Set.range f := by
  rw [cfcₙAux, NonUnitalStarAlgHom.comp_assoc, NonUnitalStarAlgHom.comp_apply]
  simp only [NonUnitalStarAlgHom.comp_apply, NonUnitalStarAlgHom.coe_coe]
  rw [cfcHom_map_spectrum (hp₁.mpr ha) (R := 𝕜) _]
  ext x
  constructor
  all_goals rintro ⟨x, rfl⟩
  · exact ⟨⟨x, (Unitization.quasispectrum_eq_spectrum_inr' 𝕜 𝕜 a).symm ▸ x.property⟩, rfl⟩
  · exact ⟨⟨x, Unitization.quasispectrum_eq_spectrum_inr' 𝕜 𝕜 a ▸ x.property⟩, rfl⟩

variable [CompleteSpace A]

lemma cfcₙAux_mem_range_inr (f : C(σₙ 𝕜 a, 𝕜)₀) :
    cfcₙAux hp₁ a ha f ∈ NonUnitalStarAlgHom.range (Unitization.inrNonUnitalStarAlgHom 𝕜 A) := by
  have h₁ := (isClosedEmbedding_cfcₙAux hp₁ a ha).continuous.range_subset_closure_image_dense
    (ContinuousMapZero.adjoin_id_dense (s := σₙ 𝕜 a) rfl) ⟨f, rfl⟩
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

variable [CStarRing A]

include hp₁ in
open Unitization NonUnitalStarAlgHom in
theorem RCLike.nonUnitalContinuousFunctionalCalculus :
    NonUnitalContinuousFunctionalCalculus 𝕜 (p : A → Prop) where
  predicate_zero := by
    rw [← hp₁, Unitization.inr_zero 𝕜]
    exact cfc_predicate_zero 𝕜
  exists_cfc_of_predicate a ha := by
    let ψ : C(σₙ 𝕜 a, 𝕜)₀ →⋆ₙₐ[𝕜] A := comp (inrRangeEquiv 𝕜 A).symm <|
      codRestrict (cfcₙAux hp₁ a ha) _ (cfcₙAux_mem_range_inr hp₁ a ha)
    have coe_ψ (f : C(σₙ 𝕜 a, 𝕜)₀) : ψ f = cfcₙAux hp₁ a ha f :=
      congr_arg Subtype.val <| (inrRangeEquiv 𝕜 A).apply_symm_apply
        ⟨cfcₙAux hp₁ a ha f, cfcₙAux_mem_range_inr hp₁ a ha f⟩
    refine ⟨ψ, ?isClosedEmbedding, ?map_id, fun f ↦ ?map_spec, fun f ↦ ?isStarNormal⟩
    case isClosedEmbedding =>
      apply isometry_inr (𝕜 := 𝕜) (A := A) |>.isClosedEmbedding |>.of_comp_iff.mp
      have : inr ∘ ψ = cfcₙAux hp₁ a ha := by ext1; rw [Function.comp_apply, coe_ψ]
      exact this ▸ isClosedEmbedding_cfcₙAux hp₁ a ha
    case map_id => exact inr_injective (R := 𝕜) <| coe_ψ _ ▸ cfcₙAux_id hp₁ a ha
    case map_spec =>
      exact quasispectrum_eq_spectrum_inr' 𝕜 𝕜 (ψ f) ▸ coe_ψ _ ▸ spec_cfcₙAux hp₁ a ha f
    case isStarNormal => exact hp₁.mp <| coe_ψ _ ▸ cfcHom_predicate (R := 𝕜) (hp₁.mpr ha) _

end RCLike

/-!
### Continuous functional calculus for selfadjoint elements
-/

section SelfAdjointNonUnital

variable {A : Type*} [TopologicalSpace A] [NonUnitalRing A] [StarRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  [NonUnitalContinuousFunctionalCalculus ℂ (IsStarNormal : A → Prop)]

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

alias ⟨IsSelfAdjoint.quasispectrumRestricts, _⟩ :=
  isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts

/-- A normal element whose `ℂ`-quasispectrum is contained in `ℝ` is selfadjoint. -/
lemma QuasispectrumRestricts.isSelfAdjoint (a : A) (ha : QuasispectrumRestricts a Complex.reCLM)
    [IsStarNormal a] : IsSelfAdjoint a :=
  isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts.mpr ⟨‹_›, ha⟩

instance IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus :
    NonUnitalContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop) :=
  QuasispectrumRestricts.cfc (q := IsStarNormal) (p := IsSelfAdjoint) Complex.reCLM
    Complex.isometry_ofReal.isUniformEmbedding (.zero _)
    (fun _ ↦ isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts)

end SelfAdjointNonUnital

section SelfAdjointUnital


variable {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A] [Algebra ℂ A]
  [ContinuousFunctionalCalculus ℂ (IsStarNormal : A → Prop)]

/-
TODO: REMOVE
this is a duplicate of `isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts`, because of
`abbrev SpectrumRestricts := QuasispectrumRestricts` but we first need unital-to-non-unital
instance)
-/
/-- An element in a C⋆-algebra is selfadjoint if and only if it is normal and its spectrum is
contained in `ℝ`. -/
lemma isSelfAdjoint_iff_isStarNormal_and_spectrumRestricts {a : A} :
    IsSelfAdjoint a ↔ IsStarNormal a ∧ SpectrumRestricts a Complex.reCLM := by
  refine ⟨fun ha ↦ ⟨ha.isStarNormal, .of_rightInvOn Complex.ofReal_re fun x hx ↦ ?_⟩, ?_⟩
  · have := eqOn_of_cfc_eq_cfc <| (cfc_star (id : ℂ → ℂ) a).symm ▸ (cfc_id ℂ a).symm ▸ ha.star_eq
    exact Complex.conj_eq_iff_re.mp (by simpa using this hx)
  · rintro ⟨ha₁, ha₂⟩
    rw [isSelfAdjoint_iff]
    nth_rw 2 [← cfc_id ℂ a]
    rw [← cfc_star_id a (R := ℂ)]
    refine cfc_congr fun x hx ↦ ?_
    obtain ⟨x, -, rfl⟩ := ha₂.algebraMap_image.symm ▸ hx
    exact Complex.conj_ofReal _

-- TODO: REMOVE (duplicate; see comment on `isSelfAdjoint_iff_isStarNormal_and_spectrumRestricts`)
lemma IsSelfAdjoint.spectrumRestricts {a : A} (ha : IsSelfAdjoint a) :
    SpectrumRestricts a Complex.reCLM :=
  isSelfAdjoint_iff_isStarNormal_and_spectrumRestricts.mp ha |>.right

-- TODO: REMOVE (duplicate; see comment on `isSelfAdjoint_iff_isStarNormal_and_spectrumRestricts`)
/-- A normal element whose `ℂ`-spectrum is contained in `ℝ` is selfadjoint. -/
lemma SpectrumRestricts.isSelfAdjoint (a : A) (ha : SpectrumRestricts a Complex.reCLM)
    [IsStarNormal a] : IsSelfAdjoint a :=
  isSelfAdjoint_iff_isStarNormal_and_spectrumRestricts.mpr ⟨‹_›, ha⟩

instance IsSelfAdjoint.instContinuousFunctionalCalculus :
    ContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop) :=
  SpectrumRestricts.cfc (q := IsStarNormal) (p := IsSelfAdjoint) Complex.reCLM
    Complex.isometry_ofReal.isUniformEmbedding (.zero _)
    (fun _ ↦ isSelfAdjoint_iff_isStarNormal_and_spectrumRestricts)

lemma IsSelfAdjoint.spectrum_nonempty {A : Type*} [Ring A] [StarRing A]
    [TopologicalSpace A] [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]
    [Nontrivial A] {a : A} (ha : IsSelfAdjoint a) : (σ ℝ a).Nonempty :=
  CFC.spectrum_nonempty ℝ a ha

end SelfAdjointUnital

/-!
### Continuous functional calculus for nonnegative elements
-/

section Nonneg

lemma CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts {A : Type*} [NonUnitalRing A]
    [StarRing A] [TopologicalSpace A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A ]
    [NonUnitalContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]
    {a : A} (ha₁ : IsSelfAdjoint a) (ha₂ : QuasispectrumRestricts a ContinuousMap.realToNNReal) :
    ∃ x : A, IsSelfAdjoint x ∧ QuasispectrumRestricts x ContinuousMap.realToNNReal ∧ x * x = a := by
  use cfcₙ Real.sqrt a, cfcₙ_predicate Real.sqrt a
  constructor
  · simpa only [QuasispectrumRestricts.nnreal_iff, cfcₙ_map_quasispectrum Real.sqrt a,
      Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
        using fun x _ ↦ Real.sqrt_nonneg x
  · rw [← cfcₙ_mul ..]
    nth_rw 2 [← cfcₙ_id ℝ a]
    apply cfcₙ_congr fun x hx ↦ ?_
    rw [QuasispectrumRestricts.nnreal_iff] at ha₂
    apply ha₂ x at hx
    simp [← sq, Real.sq_sqrt hx]

variable {A : Type*} [NonUnitalRing A] [PartialOrder A] [StarRing A] [StarOrderedRing A]
variable [TopologicalSpace A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
variable [NonUnitalContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]
variable [NonnegSpectrumClass ℝ A]

lemma nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts {a : A} :
    0 ≤ a ↔ IsSelfAdjoint a ∧ QuasispectrumRestricts a ContinuousMap.realToNNReal := by
  refine ⟨fun ha ↦ ⟨.of_nonneg ha, .nnreal_of_nonneg ha⟩, ?_⟩
  rintro ⟨ha₁, ha₂⟩
  obtain ⟨x, hx, -, rfl⟩ := CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts ha₁ ha₂
  simpa [sq, hx.star_eq] using star_mul_self_nonneg x

open NNReal in
instance Nonneg.instNonUnitalContinuousFunctionalCalculus :
    NonUnitalContinuousFunctionalCalculus ℝ≥0 (fun x : A ↦ 0 ≤ x) :=
  QuasispectrumRestricts.cfc (q := IsSelfAdjoint) ContinuousMap.realToNNReal
    isUniformEmbedding_subtype_val le_rfl
    (fun _ ↦ nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts)

open NNReal in
lemma NNReal.spectrum_nonempty {A : Type*} [Ring A] [StarRing A] [LE A]
    [TopologicalSpace A] [Algebra ℝ≥0 A] [ContinuousFunctionalCalculus ℝ≥0 (fun x : A ↦ 0 ≤ x)]
    [Nontrivial A] {a : A} (ha : 0 ≤ a) : (spectrum ℝ≥0 a).Nonempty :=
  CFC.spectrum_nonempty ℝ≥0 a ha

end Nonneg


section Nonneg

-- TODO: REMOVE (duplicate; see comment on `isSelfAdjoint_iff_isStarNormal_and_spectrumRestricts`)
lemma CFC.exists_sqrt_of_isSelfAdjoint_of_spectrumRestricts {A : Type*} [Ring A] [StarRing A]
    [TopologicalSpace A] [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]
    {a : A} (ha₁ : IsSelfAdjoint a) (ha₂ : SpectrumRestricts a ContinuousMap.realToNNReal) :
    ∃ x : A, IsSelfAdjoint x ∧ SpectrumRestricts x ContinuousMap.realToNNReal ∧ x ^ 2 = a := by
  use cfc Real.sqrt a, cfc_predicate Real.sqrt a
  constructor
  · simpa only [SpectrumRestricts.nnreal_iff, cfc_map_spectrum Real.sqrt a, Set.mem_image,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] using fun x _ ↦ Real.sqrt_nonneg x
  · rw [← cfc_pow ..]
    nth_rw 2 [← cfc_id ℝ a]
    apply cfc_congr fun x hx ↦ ?_
    rw [SpectrumRestricts.nnreal_iff] at ha₂
    apply ha₂ x at hx
    simp [Real.sq_sqrt hx]

variable {A : Type*} [Ring A] [PartialOrder A] [StarRing A] [StarOrderedRing A] [TopologicalSpace A]
variable [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]
variable [NonnegSpectrumClass ℝ A]

-- TODO: REMOVE (duplicate; see comment on `isSelfAdjoint_iff_isStarNormal_and_spectrumRestricts`)
lemma nonneg_iff_isSelfAdjoint_and_spectrumRestricts {a : A} :
    0 ≤ a ↔ IsSelfAdjoint a ∧ SpectrumRestricts a ContinuousMap.realToNNReal := by
  refine ⟨fun ha ↦ ⟨.of_nonneg ha, .nnreal_of_nonneg ha⟩, ?_⟩
  rintro ⟨ha₁, ha₂⟩
  obtain ⟨x, hx, -, rfl⟩ := CFC.exists_sqrt_of_isSelfAdjoint_of_spectrumRestricts ha₁ ha₂
  simpa [sq, hx.star_eq] using star_mul_self_nonneg x

open NNReal in
instance Nonneg.instContinuousFunctionalCalculus :
    ContinuousFunctionalCalculus ℝ≥0 (fun x : A ↦ 0 ≤ x) :=
  SpectrumRestricts.cfc (q := IsSelfAdjoint) ContinuousMap.realToNNReal
    isUniformEmbedding_subtype_val le_rfl (fun _ ↦ nonneg_iff_isSelfAdjoint_and_spectrumRestricts)

end Nonneg

/-!
### The restriction of a continuous functional calculus is equal to the original one
-/
section RealEqComplex

variable {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A] [Algebra ℂ A]
  [ContinuousFunctionalCalculus ℂ (IsStarNormal : A → Prop)] [T2Space A]

lemma cfcHom_real_eq_restrict {a : A} (ha : IsSelfAdjoint a) :
    cfcHom ha =
      ha.spectrumRestricts.starAlgHom (R := ℝ) (S := ℂ)
        (cfcHom ha.isStarNormal) (f := Complex.reCLM) :=
  ha.spectrumRestricts.cfcHom_eq_restrict _ Complex.isometry_ofReal.isUniformEmbedding
    ha ha.isStarNormal

lemma cfc_real_eq_complex {a : A} (f : ℝ → ℝ) (ha : IsSelfAdjoint a := by cfc_tac)  :
    cfc f a = cfc (fun x ↦ f x.re : ℂ → ℂ) a := by
  replace ha : IsSelfAdjoint a := ha -- hack to avoid issues caused by autoParam
  exact ha.spectrumRestricts.cfc_eq_restrict (f := Complex.reCLM)
    Complex.isometry_ofReal.isUniformEmbedding ha ha.isStarNormal f

end RealEqComplex

section RealEqComplexNonUnital

variable {A : Type*} [TopologicalSpace A] [NonUnitalRing A] [StarRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [T2Space A]
  [NonUnitalContinuousFunctionalCalculus ℂ (IsStarNormal : A → Prop)]

lemma cfcₙHom_real_eq_restrict {a : A} (ha : IsSelfAdjoint a) :
    cfcₙHom ha = (ha.quasispectrumRestricts.2).nonUnitalStarAlgHom (cfcₙHom ha.isStarNormal)
      (R := ℝ) (S := ℂ) (f := Complex.reCLM) :=
  ha.quasispectrumRestricts.2.cfcₙHom_eq_restrict _ Complex.isometry_ofReal.isUniformEmbedding
    ha ha.isStarNormal

lemma cfcₙ_real_eq_complex {a : A} (f : ℝ → ℝ) (ha : IsSelfAdjoint a := by cfc_tac)  :
    cfcₙ f a = cfcₙ (fun x ↦ f x.re : ℂ → ℂ) a := by
  replace ha : IsSelfAdjoint a := ha -- hack to avoid issues caused by autoParam
  exact ha.quasispectrumRestricts.2.cfcₙ_eq_restrict (f := Complex.reCLM)
    Complex.isometry_ofReal.isUniformEmbedding ha ha.isStarNormal f

end RealEqComplexNonUnital

section NNRealEqReal

open NNReal

variable {A : Type*} [TopologicalSpace A] [Ring A] [PartialOrder A] [StarRing A]
  [StarOrderedRing A] [Algebra ℝ A] [TopologicalRing A] [T2Space A]
  [ContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]
  [NonnegSpectrumClass ℝ A]

lemma cfcHom_nnreal_eq_restrict {a : A} (ha : 0 ≤ a) :
    cfcHom ha = (SpectrumRestricts.nnreal_of_nonneg ha).starAlgHom
      (cfcHom (IsSelfAdjoint.of_nonneg ha)) := by
  apply (SpectrumRestricts.nnreal_of_nonneg ha).cfcHom_eq_restrict _ isUniformEmbedding_subtype_val

lemma cfc_nnreal_eq_real {a : A} (f : ℝ≥0 → ℝ≥0) (ha : 0 ≤ a := by cfc_tac)  :
    cfc f a = cfc (fun x ↦ f x.toNNReal : ℝ → ℝ) a := by
  replace ha : 0 ≤ a := ha -- hack to avoid issues caused by autoParam
  apply (SpectrumRestricts.nnreal_of_nonneg ha).cfc_eq_restrict _
    isUniformEmbedding_subtype_val ha (.of_nonneg ha)

end NNRealEqReal

section NNRealEqRealNonUnital

open NNReal

variable {A : Type*} [TopologicalSpace A] [NonUnitalRing A] [PartialOrder A] [StarRing A]
  [StarOrderedRing A] [Module ℝ A] [TopologicalRing A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
  [T2Space A] [NonUnitalContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]
  [NonnegSpectrumClass ℝ A]

lemma cfcₙHom_nnreal_eq_restrict {a : A} (ha : 0 ≤ a) :
    cfcₙHom ha = (QuasispectrumRestricts.nnreal_of_nonneg ha).nonUnitalStarAlgHom
      (cfcₙHom (IsSelfAdjoint.of_nonneg ha)) := by
  apply (QuasispectrumRestricts.nnreal_of_nonneg ha).cfcₙHom_eq_restrict _
    isUniformEmbedding_subtype_val

lemma cfcₙ_nnreal_eq_real {a : A} (f : ℝ≥0 → ℝ≥0) (ha : 0 ≤ a := by cfc_tac)  :
    cfcₙ f a = cfcₙ (fun x ↦ f x.toNNReal : ℝ → ℝ) a := by
  replace ha : 0 ≤ a := ha -- hack to avoid issues caused by autoParam
  apply (QuasispectrumRestricts.nnreal_of_nonneg ha).cfcₙ_eq_restrict _
    isUniformEmbedding_subtype_val ha (.of_nonneg ha)

end NNRealEqRealNonUnital

end
