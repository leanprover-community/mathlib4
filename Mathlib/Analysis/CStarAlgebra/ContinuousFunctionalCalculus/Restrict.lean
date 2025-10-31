/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital

/-! # Restriction of the continuous functional calculus to a scalar subring

The main declaration in this file is:

+ `SpectrumRestricts.cfc`: builds a continuous functional calculus over a subring of scalars.
  This is use for automatically deriving the continuous functional calculi on selfadjoint or
  positive elements from the one for normal elements.

This will allow us to take an instance of the
`ContinuousFunctionalCalculus ℂ A IsStarNormal` and produce both of the instances
`ContinuousFunctionalCalculus ℝ A IsSelfAdjoint` and `ContinuousFunctionalCalculus ℝ≥0 A (0 ≤ ·)`
simply by proving:

1. `IsSelfAdjoint x ↔ IsStarNormal x ∧ SpectrumRestricts Complex.re x`,
2. `0 ≤ x ↔ IsSelfAdjoint x ∧ SpectrumRestricts Real.toNNReal x`.
-/

open Set Topology

namespace SpectrumRestricts

/-- The homeomorphism `spectrum S a ≃ₜ spectrum R a` induced by `SpectrumRestricts a f`. -/
def homeomorph {R S A : Type*} [Semifield R] [Semifield S] [Ring A]
    [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [TopologicalSpace R]
    [TopologicalSpace S] [ContinuousSMul R S] {a : A} {f : C(S, R)} (h : SpectrumRestricts a f) :
    spectrum S a ≃ₜ spectrum R a where
  toFun := MapsTo.restrict f _ _ h.subset_preimage
  invFun := MapsTo.restrict (algebraMap R S) _ _ (image_subset_iff.mp h.algebraMap_image.subset)
  left_inv x := Subtype.ext <| h.rightInvOn x.2
  right_inv x := Subtype.ext <| h.left_inv x
  continuous_toFun := continuous_induced_rng.mpr <| f.continuous.comp continuous_induced_dom
  continuous_invFun := continuous_induced_rng.mpr <|
    continuous_algebraMap R S |>.comp continuous_induced_dom

lemma compactSpace {R S A : Type*} [Semifield R] [Semifield S] [Ring A]
    [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [TopologicalSpace R]
    [TopologicalSpace S] {a : A} (f : C(S, R)) (h : SpectrumRestricts a f)
    [h_cpct : CompactSpace (spectrum S a)] : CompactSpace (spectrum R a) := by
  rw [← isCompact_iff_compactSpace] at h_cpct ⊢
  exact h.image ▸ h_cpct.image (map_continuous f)

universe u v w

/-- If the spectrum of an element restricts to a smaller scalar ring, then a continuous functional
calculus over the larger scalar ring descends to the smaller one. -/
@[simps!]
def starAlgHom {R : Type u} {S : Type v} {A : Type w} [Semifield R]
    [StarRing R] [TopologicalSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [Semifield S]
    [StarRing S] [TopologicalSpace S] [IsTopologicalSemiring S] [ContinuousStar S] [Ring A]
    [StarRing A] [Algebra R S] [Algebra R A] [Algebra S A]
    [IsScalarTower R S A] [StarModule R S] [ContinuousSMul R S] {a : A}
    (φ : C(spectrum S a, S) →⋆ₐ[S] A) {f : C(S, R)} (h : SpectrumRestricts a f) :
    C(spectrum R a, R) →⋆ₐ[R] A :=
  (φ.restrictScalars R).comp <|
    (ContinuousMap.compStarAlgHom (spectrum S a) (.ofId R S) (algebraMapCLM R S).continuous).comp <|
      ContinuousMap.compStarAlgHom' R R
        ⟨Subtype.map f h.subset_preimage, (map_continuous f).subtype_map
          fun x (hx : x ∈ spectrum S a) => h.subset_preimage hx⟩

variable {R S A : Type*} {p q : A → Prop}
variable [Semifield R] [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R]
variable [Semifield S] [StarRing S] [MetricSpace S] [IsTopologicalSemiring S] [ContinuousStar S]
variable [Ring A] [StarRing A] [Algebra S A]
variable [Algebra R S] [Algebra R A] [IsScalarTower R S A] [StarModule R S] [ContinuousSMul R S]

lemma starAlgHom_id {a : A} {φ : C(spectrum S a, S) →⋆ₐ[S] A} {f : C(S, R)}
    (h : SpectrumRestricts a f) (h_id : φ (.restrict (spectrum S a) <| .id S) = a) :
    h.starAlgHom φ (.restrict (spectrum R a) <| .id R) = a := by
  simp only [SpectrumRestricts.starAlgHom_apply]
  convert h_id
  ext x
  exact h.rightInvOn x.2

variable [TopologicalSpace A] [ContinuousFunctionalCalculus S A q]
variable [CompleteSpace R]

lemma isClosedEmbedding_starAlgHom {a : A} {φ : C(spectrum S a, S) →⋆ₐ[S] A}
    (hφ : IsClosedEmbedding φ) {f : C(S, R)} (h : SpectrumRestricts a f)
    (halg : IsUniformEmbedding (algebraMap R S)) :
    IsClosedEmbedding (h.starAlgHom φ) :=
  hφ.comp <| IsUniformEmbedding.isClosedEmbedding <| .comp
    (ContinuousMap.isUniformEmbedding_comp _ halg)
    (UniformEquiv.arrowCongr h.homeomorph.symm (.refl _) |>.isUniformEmbedding)

/-- Given a `ContinuousFunctionalCalculus S A q`. If we form the predicate `p` for `a : A`
characterized by: `q a` and the spectrum of `a` restricts to the scalar subring `R` via
`f : C(S, R)`, then we can get a restricted functional calculus
`ContinuousFunctionalCalculus R A p`. -/
protected theorem cfc (f : C(S, R)) (halg : IsUniformEmbedding (algebraMap R S)) (h0 : p 0)
    (h : ∀ a, p a ↔ q a ∧ SpectrumRestricts a f) :
    ContinuousFunctionalCalculus R A p where
  predicate_zero := h0
  spectrum_nonempty a ha := ((h a).mp ha).2.image ▸
    (ContinuousFunctionalCalculus.spectrum_nonempty a ((h a).mp ha).1 |>.image f)
  compactSpace_spectrum a := by
    have := ContinuousFunctionalCalculus.compactSpace_spectrum (R := S) a
    rw [← isCompact_iff_compactSpace] at this ⊢
    simpa using halg.isClosedEmbedding.isCompact_preimage this
  exists_cfc_of_predicate a ha := by
    refine ⟨((h a).mp ha).2.starAlgHom (cfcHom ((h a).mp ha).1 (R := S)),
      ?hom_isClosedEmbedding, ?hom_id, ?hom_map_spectrum, ?predicate_hom⟩
    case hom_isClosedEmbedding =>
      exact ((h a).mp ha).2.isClosedEmbedding_starAlgHom
        (cfcHom_isClosedEmbedding ((h a).mp ha).1) halg
    case hom_id => exact ((h a).mp ha).2.starAlgHom_id <| cfcHom_id ((h a).mp ha).1
    case hom_map_spectrum =>
      intro g
      rw [SpectrumRestricts.starAlgHom_apply]
      simp only [← @spectrum.preimage_algebraMap (R := R) S, cfcHom_map_spectrum]
      ext x
      constructor
      · rintro ⟨y, hy⟩
        have := congr_arg f hy
        simp only [ContinuousMap.coe_mk, ContinuousMap.comp_apply, StarAlgHom.ofId_apply] at this
        rw [((h a).mp ha).2.left_inv _, ((h a).mp ha).2.left_inv _] at this
        exact ⟨_, this⟩
      · rintro ⟨y, rfl⟩
        rw [Set.mem_preimage]
        refine ⟨⟨algebraMap R S y, spectrum.algebraMap_mem S y.prop⟩, ?_⟩
        simp only [ContinuousMap.coe_mk, ContinuousMap.comp_apply, StarAlgHom.ofId_apply]
        congr
        exact Subtype.ext (((h a).mp ha).2.left_inv y)
    case predicate_hom =>
      intro g
      rw [h]
      refine ⟨cfcHom_predicate _ _, ?_⟩
      refine .of_rightInvOn (((h a).mp ha).2.left_inv) fun s hs ↦ ?_
      rw [SpectrumRestricts.starAlgHom_apply, cfcHom_map_spectrum] at hs
      obtain ⟨r, rfl⟩ := hs
      simp [((h a).mp ha).2.left_inv _]

variable [ContinuousFunctionalCalculus R A p] [ContinuousMap.UniqueHom R A]

lemma cfcHom_eq_restrict (f : C(S, R)) (halg : IsUniformEmbedding (algebraMap R S))
    {a : A} (hpa : p a) (hqa : q a) (h : SpectrumRestricts a f) :
    cfcHom hpa = h.starAlgHom (cfcHom hqa) := by
  apply cfcHom_eq_of_continuous_of_map_id
  · exact h.isClosedEmbedding_starAlgHom (cfcHom_isClosedEmbedding hqa) halg |>.continuous
  · exact h.starAlgHom_id (cfcHom_id hqa)

lemma cfc_eq_restrict (f : C(S, R)) (halg : IsUniformEmbedding (algebraMap R S)) {a : A} (hpa : p a)
    (hqa : q a) (h : SpectrumRestricts a f) (g : R → R) :
    cfc g a = cfc (fun x ↦ algebraMap R S (g (f x))) a := by
  by_cases hg : ContinuousOn g (spectrum R a)
  · rw [cfc_apply g a, cfcHom_eq_restrict f halg hpa hqa h, SpectrumRestricts.starAlgHom_apply,
      cfcHom_eq_cfc_extend 0]
    apply cfc_congr fun x hx ↦ ?_
    lift x to spectrum S a using hx
    simp [Function.comp]
  · have : ¬ ContinuousOn (fun x ↦ algebraMap R S (g (f x)) : S → S) (spectrum S a) := by
      refine fun hg' ↦ hg ?_
      rw [halg.isEmbedding.continuousOn_iff]
      simpa [halg.isEmbedding.continuousOn_iff, Function.comp_def, h.left_inv _] using
        hg'.comp halg.isEmbedding.continuous.continuousOn (fun _ : R ↦ spectrum.algebraMap_mem S)
    rw [cfc_apply_of_not_continuousOn a hg, cfc_apply_of_not_continuousOn a this]

end SpectrumRestricts


namespace QuasispectrumRestricts

local notation "σₙ" => quasispectrum
open ContinuousMapZero Set

/-- The homeomorphism `quasispectrum S a ≃ₜ quasispectrum R a` induced by
`QuasispectrumRestricts a f`. -/
def homeomorph {R S A : Type*} [Semifield R] [Field S] [NonUnitalRing A]
    [Algebra R S] [Module R A] [Module S A] [IsScalarTower R S A] [TopologicalSpace R]
    [TopologicalSpace S] [ContinuousSMul R S] [IsScalarTower S A A] [SMulCommClass S A A]
    {a : A} {f : C(S, R)} (h : QuasispectrumRestricts a f) :
    σₙ S a ≃ₜ σₙ R a where
  toFun := MapsTo.restrict f _ _ h.subset_preimage
  invFun := MapsTo.restrict (algebraMap R S) _ _ (image_subset_iff.mp h.algebraMap_image.subset)
  left_inv x := Subtype.ext <| h.rightInvOn x.2
  right_inv x := Subtype.ext <| h.left_inv x
  continuous_toFun := continuous_induced_rng.mpr <| f.continuous.comp continuous_induced_dom
  continuous_invFun := continuous_induced_rng.mpr <|
    continuous_algebraMap R S |>.comp continuous_induced_dom

universe u v w

open ContinuousMapZero
/-- If the quasispectrum of an element restricts to a smaller scalar ring, then a non-unital
continuous functional calculus over the larger scalar ring descends to the smaller one. -/
@[simps!]
def nonUnitalStarAlgHom {R : Type u} {S : Type v} {A : Type w} [Semifield R]
    [StarRing R] [TopologicalSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [Field S]
    [StarRing S] [TopologicalSpace S] [IsTopologicalRing S] [ContinuousStar S] [NonUnitalRing A]
    [StarRing A] [Algebra R S] [Module R A] [Module S A] [IsScalarTower S A A] [SMulCommClass S A A]
    [IsScalarTower R S A] [StarModule R S] [ContinuousSMul R S] {a : A}
    (φ : C(σₙ S a, S)₀ →⋆ₙₐ[S] A) {f : C(S, R)} (h : QuasispectrumRestricts a f) :
    C(σₙ R a, R)₀ →⋆ₙₐ[R] A :=
  (φ.restrictScalars R).comp <|
    (nonUnitalStarAlgHom_postcomp (σₙ S a) (StarAlgHom.ofId R S) (algebraMapCLM R S).continuous)
      |>.comp <| nonUnitalStarAlgHom_precomp R
        ⟨⟨Subtype.map f h.subset_preimage, (map_continuous f).subtype_map
          fun x (hx : x ∈ σₙ S a) => h.subset_preimage hx⟩, Subtype.ext h.map_zero⟩

variable {R S A : Type*} {p q : A → Prop}
variable [Semifield R] [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R]
variable [Field S] [StarRing S] [MetricSpace S] [IsTopologicalRing S] [ContinuousStar S]
variable [NonUnitalRing A] [StarRing A] [Module S A] [IsScalarTower S A A]
variable [SMulCommClass S A A]
variable [Algebra R S] [Module R A] [IsScalarTower R S A] [StarModule R S] [ContinuousSMul R S]

lemma nonUnitalStarAlgHom_id {a : A} {φ : C(σₙ S a, S)₀ →⋆ₙₐ[S] A} {f : C(S, R)}
    (h : QuasispectrumRestricts a f) (h_id : φ (.id _) = a) :
    h.nonUnitalStarAlgHom φ (.id _) = a := by
  simp only [QuasispectrumRestricts.nonUnitalStarAlgHom_apply]
  convert h_id
  ext x
  exact h.rightInvOn x.2

variable [TopologicalSpace A] [NonUnitalContinuousFunctionalCalculus S A q]
variable [CompleteSpace R]

lemma isClosedEmbedding_nonUnitalStarAlgHom {a : A} {φ : C(σₙ S a, S)₀ →⋆ₙₐ[S] A}
    (hφ : IsClosedEmbedding φ) {f : C(S, R)} (h : QuasispectrumRestricts a f)
    (halg : IsUniformEmbedding (algebraMap R S)) :
    IsClosedEmbedding (h.nonUnitalStarAlgHom φ) := by
  have : h.homeomorph.symm 0 = 0 := Subtype.ext (map_zero <| algebraMap _ _)
  refine hφ.comp <| IsUniformEmbedding.isClosedEmbedding <| .comp
    (ContinuousMapZero.isUniformEmbedding_comp _ halg)
    (UniformEquiv.arrowCongrLeft₀ h.homeomorph.symm this |>.isUniformEmbedding)

variable [IsScalarTower R A A] [SMulCommClass R A A]

/-- Given a `NonUnitalContinuousFunctionalCalculus S A q`. If we form the predicate `p` for `a : A`
characterized by: `q a` and the quasispectrum of `a` restricts to the scalar subring `R` via
`f : C(S, R)`, then we can get a restricted functional calculus
`NonUnitalContinuousFunctionalCalculus R A p`. -/
protected theorem cfc (f : C(S, R)) (halg : IsUniformEmbedding (algebraMap R S)) (h0 : p 0)
    (h : ∀ a, p a ↔ q a ∧ QuasispectrumRestricts a f) :
    NonUnitalContinuousFunctionalCalculus R A p where
  predicate_zero := h0
  compactSpace_quasispectrum a := by
    have := NonUnitalContinuousFunctionalCalculus.compactSpace_quasispectrum (R := S) a
    rw [← isCompact_iff_compactSpace] at this ⊢
    simpa using halg.isClosedEmbedding.isCompact_preimage this
  exists_cfc_of_predicate a ha := by
    refine ⟨((h a).mp ha).2.nonUnitalStarAlgHom (cfcₙHom ((h a).mp ha).1 (R := S)),
      ?hom_isClosedEmbedding, ?hom_id, ?hom_map_spectrum, ?predicate_hom⟩
    case hom_isClosedEmbedding =>
      exact ((h a).mp ha).2.isClosedEmbedding_nonUnitalStarAlgHom
        (cfcₙHom_isClosedEmbedding ((h a).mp ha).1) halg
    case hom_id => exact ((h a).mp ha).2.nonUnitalStarAlgHom_id <| cfcₙHom_id ((h a).mp ha).1
    case hom_map_spectrum =>
      intro g
      rw [nonUnitalStarAlgHom_apply]
      simp only [← @quasispectrum.preimage_algebraMap (R := R) S, cfcₙHom_map_quasispectrum]
      ext x
      constructor
      · rintro ⟨y, hy⟩
        have := congr_arg f hy
        simp only [comp_apply, coe_mk, ContinuousMap.coe_mk, StarAlgHom.ofId_apply]
          at this
        rw [((h a).mp ha).2.left_inv _, ((h a).mp ha).2.left_inv _] at this
        exact ⟨_, this⟩
      · rintro ⟨y, rfl⟩
        rw [Set.mem_preimage]
        refine ⟨⟨algebraMap R S y, quasispectrum.algebraMap_mem S y.prop⟩, ?_⟩
        simp only [comp_apply, coe_mk, ContinuousMap.coe_mk, StarAlgHom.ofId_apply]
        congr
        exact Subtype.ext (((h a).mp ha).2.left_inv y)
    case predicate_hom =>
      intro g
      rw [h]
      refine ⟨cfcₙHom_predicate _ _, ?_⟩
      refine { rightInvOn := fun s hs ↦ ?_, left_inv := ((h a).mp ha).2.left_inv }
      rw [nonUnitalStarAlgHom_apply,
        cfcₙHom_map_quasispectrum] at hs
      obtain ⟨r, rfl⟩ := hs
      simp [((h a).mp ha).2.left_inv _]

variable [NonUnitalContinuousFunctionalCalculus R A p]
variable [ContinuousMapZero.UniqueHom R A]

lemma cfcₙHom_eq_restrict (f : C(S, R)) (halg : IsUniformEmbedding (algebraMap R S)) {a : A}
    (hpa : p a) (hqa : q a) (h : QuasispectrumRestricts a f) :
    cfcₙHom hpa = h.nonUnitalStarAlgHom (cfcₙHom hqa) := by
  apply cfcₙHom_eq_of_continuous_of_map_id
  · exact h.isClosedEmbedding_nonUnitalStarAlgHom (cfcₙHom_isClosedEmbedding hqa) halg |>.continuous
  · exact h.nonUnitalStarAlgHom_id (cfcₙHom_id hqa)

lemma cfcₙ_eq_restrict (f : C(S, R)) (halg : IsUniformEmbedding (algebraMap R S)) {a : A}
    (hpa : p a) (hqa : q a) (h : QuasispectrumRestricts a f) (g : R → R) :
    cfcₙ g a = cfcₙ (fun x ↦ algebraMap R S (g (f x))) a := by
  by_cases hg : ContinuousOn g (σₙ R a) ∧ g 0 = 0
  · obtain ⟨hg, hg0⟩ := hg
    rw [cfcₙ_apply g a, cfcₙHom_eq_restrict f halg hpa hqa h, nonUnitalStarAlgHom_apply,
      cfcₙHom_eq_cfcₙ_extend 0]
    apply cfcₙ_congr fun x hx ↦ ?_
    lift x to σₙ S a using hx
    simp
  · simp only [not_and_or] at hg
    obtain (hg | hg) := hg
    · have : ¬ ContinuousOn (fun x ↦ algebraMap R S (g (f x)) : S → S) (σₙ S a) := by
        refine fun hg' ↦ hg ?_
        rw [halg.isEmbedding.continuousOn_iff]
        simpa [halg.isEmbedding.continuousOn_iff, Function.comp_def, h.left_inv _] using
          hg'.comp halg.isEmbedding.continuous.continuousOn
          (fun _ : R ↦ quasispectrum.algebraMap_mem S)
      rw [cfcₙ_apply_of_not_continuousOn a hg, cfcₙ_apply_of_not_continuousOn a this]
    · rw [cfcₙ_apply_of_not_map_zero a hg, cfcₙ_apply_of_not_map_zero a (by simpa [h.map_zero])]

end QuasispectrumRestricts
