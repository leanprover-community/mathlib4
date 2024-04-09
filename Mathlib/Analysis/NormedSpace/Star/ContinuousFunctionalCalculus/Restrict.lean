/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.ContinuousFunction.Compact
import Mathlib.Topology.ContinuousFunction.FunctionalCalculus

/-! # Restriction of the continuous functional calculus to a scalar subring

The main declaration in this file is:

+ `SpectrumRestricts.cfc`: builds a continuous functional calculus over a subring of scalars.
  This is use for automatically deriving the continuous functional calculi on selfadjoint or
  positive elements from the one for normal elements.

This will allow us to take an instance of the
`ContinuousFunctionalCalculus ℂ IsStarNormal` and produce both of the instances
`ContinuousFunctionalCalculus ℝ IsSelfAdjoint` and `ContinuousFunctionalCalculus ℝ≥0 (0 ≤ ·)`
simply by proving:

1. `IsSelfAdjoint x ↔ IsStarNormal x ∧ SpectrumRestricts Complex.re x`,
2. `0 ≤ x ↔ IsSelfAdjoint x ∧ SpectrumRestricts Real.toNNReal x`.
-/

namespace SpectrumRestricts

lemma compactSpace {R S A : Type*} [CommSemiring R] [CommSemiring S] [Ring A]
    [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [TopologicalSpace R]
    [TopologicalSpace S] {a : A} (f : C(S, R)) (h : SpectrumRestricts a f)
    [h_cpct : CompactSpace (spectrum S a)] : CompactSpace (spectrum R a) := by
  rw [← isCompact_iff_compactSpace] at h_cpct ⊢
  exact h.image ▸ h_cpct.image (map_continuous f)

universe u v w

/-- If the spectrum of an element restricts to a smaller scalar ring, then a continuous functional
calculus over the larger scalar ring descends to the smaller one. -/
@[simps!]
def starAlgHom {R : Type u} {S : Type v} {A : Type w} [CommSemiring R]
    [StarRing R] [TopologicalSpace R] [TopologicalSemiring R] [ContinuousStar R] [CommSemiring S]
    [StarRing S] [TopologicalSpace S] [TopologicalSemiring S] [ContinuousStar S] [Ring A]
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
variable [CommSemiring R] [StarRing R] [MetricSpace R] [TopologicalSemiring R] [ContinuousStar R]
variable [CommSemiring S] [StarRing S] [MetricSpace S] [TopologicalSemiring S] [ContinuousStar S]
variable [TopologicalSpace A] [Ring A] [StarRing A] [Algebra S A] [ContinuousFunctionalCalculus S q]
variable [Algebra R S] [Algebra R A] [IsScalarTower R S A] [StarModule R S] [ContinuousSMul R S]
variable [CompleteSpace R]

lemma closedEmbedding_starAlgHom {a : A} {φ : C(spectrum S a, S) →⋆ₐ[S] A}
    (hφ : ClosedEmbedding φ) {f : C(S, R)} (h : SpectrumRestricts a f)
    (h_isom : Isometry (algebraMap R S)) [h_cpct : CompactSpace (spectrum S a)] :
    ClosedEmbedding (h.starAlgHom φ) := by
  apply hφ.comp
  simp only [RingHom.coe_coe, StarAlgHom.coe_toAlgHom, StarAlgHom.comp_apply,
    ContinuousMap.compStarAlgHom'_apply, ContinuousMap.compStarAlgHom_apply]
  have : CompactSpace (spectrum R a) := h.compactSpace
  apply Isometry.closedEmbedding ?_
  simp only [isometry_iff_dist_eq]
  refine fun g₁ g₂ ↦ le_antisymm ?_ ?_
  all_goals refine (ContinuousMap.dist_le dist_nonneg).mpr fun x ↦ ?_
  · simpa [h_isom.dist_eq] using ContinuousMap.dist_apply_le_dist _
  · obtain ⟨y, y_mem, hy⟩ : (x : R) ∈ f '' spectrum S a := h.image.symm ▸ x.2
    lift y to spectrum S a using y_mem
    refine le_of_eq_of_le ?_ <| ContinuousMap.dist_apply_le_dist y
    simp only [ContinuousMap.coe_mk, ContinuousMap.comp_apply, StarAlgHom.ofId_apply]
    rw [h_isom.dist_eq]
    congr <;> exact Subtype.ext hy.symm

lemma starAlgHom_id {a : A} {φ : C(spectrum S a, S) →⋆ₐ[S] A} {f : C(S, R)}
    (h : SpectrumRestricts a f) (h_id : φ (.restrict (spectrum S a) <| .id S) = a) :
    h.starAlgHom φ (.restrict (spectrum R a) <| .id R) = a := by
  simp only [SpectrumRestricts.starAlgHom_apply]
  convert h_id
  ext x
  exact h.rightInvOn x.2

/-- Given a `ContinuousFunctionalCalculus S q`. If we form the predicate `p` for `a : A`
characterized by: `q a` and the spectrum of `a` restricts to the scalar subring `R` via
`f : C(S, R)`, then we can get a restricted functional calculus
`ContinuousFunctionalCalculus R p`. -/
protected theorem cfc (f : C(S, R)) (h_isom : Isometry (algebraMap R S))
    (h : ∀ a, p a ↔ q a ∧ SpectrumRestricts a f) (h_cpct : ∀ a, q a → CompactSpace (spectrum S a)) :
    ContinuousFunctionalCalculus R p where
  exists_cfc_of_predicate a ha := by
    refine ⟨((h a).mp ha).2.starAlgHom (cfcHom ((h a).mp ha).1 (R := S)),
      ?hom_closedEmbedding, ?hom_id, ?hom_map_spectrum, ?predicate_hom⟩
    case hom_closedEmbedding =>
      exact ((h a).mp ha).2.closedEmbedding_starAlgHom (cfcHom_closedEmbedding ((h a).mp ha).1)
        h_isom (h_cpct := h_cpct a ((h a).mp ha).1)
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
        refine' ⟨⟨algebraMap R S y, spectrum.algebraMap_mem S y.prop⟩, _⟩
        simp only [ContinuousMap.coe_mk, ContinuousMap.comp_apply, StarAlgHom.ofId_apply]
        congr
        exact Subtype.ext (((h a).mp ha).2.left_inv y)
    case predicate_hom =>
      intro g
      rw [h]
      refine ⟨cfcHom_predicate _ _, ?_⟩
      refine { rightInvOn := fun s hs ↦ ?_, left_inv := ((h a).mp ha).2.left_inv }
      rw [SpectrumRestricts.starAlgHom_apply, cfcHom_map_spectrum] at hs
      obtain ⟨r, rfl⟩ := hs
      simp [((h a).mp ha).2.left_inv _]

variable [ContinuousFunctionalCalculus R p] [UniqueContinuousFunctionalCalculus R A]

lemma cfcHom_eq_restrict (f : C(S, R)) (h_isom : Isometry (algebraMap R S)) {a : A} (hpa : p a)
    (hqa : q a) (h : SpectrumRestricts a f) [CompactSpace (spectrum S a)] :
    cfcHom hpa = h.starAlgHom (cfcHom hqa) := by
  apply cfcHom_eq_of_continuous_of_map_id
  · exact h.closedEmbedding_starAlgHom (cfcHom_closedEmbedding hqa) h_isom |>.continuous
  · exact h.starAlgHom_id (cfcHom_id hqa)

lemma cfc_eq_restrict (f : C(S, R)) (h_isom : Isometry (algebraMap R S)) {a : A} (hpa : p a)
    (hqa : q a) (h : SpectrumRestricts a f) [CompactSpace (spectrum S a)] (g : R → R) :
    cfc g a = cfc (fun x ↦ algebraMap R S (g (f x))) a := by
  by_cases hg : ContinuousOn g (spectrum R a)
  · rw [cfc_apply g a, cfcHom_eq_restrict f h_isom hpa hqa h, SpectrumRestricts.starAlgHom_apply,
      cfcHom_eq_cfc_extend 0]
    apply cfc_congr fun x hx ↦ ?_
    lift x to spectrum S a using hx
    simp [Function.comp, Subtype.val_injective.extend_apply]
  · have : ¬ ContinuousOn (fun x ↦ algebraMap R S (g (f x)) : S → S) (spectrum S a) := by
      refine fun hg' ↦ hg ?_
      rw [h_isom.embedding.continuousOn_iff]
      simpa [h_isom.embedding.continuousOn_iff, Function.comp, h.left_inv _] using
        hg'.comp h_isom.continuous.continuousOn (fun _ : R ↦ spectrum.algebraMap_mem S)
    rw [cfc_apply_of_not_continuousOn a hg, cfc_apply_of_not_continuousOn a this]

end SpectrumRestricts
