/-
Copyright (c) 2026 Tjeerd Jan Heeringa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tjeerd Jan Heeringa
-/
module

public import Mathlib.Analysis.InnerProductSpace.Reproducing

/-!
# Operations on RKHS
This file implements the maps that show how RKHSs created from kernels formed by applying operations
to a set of kernels relate to the RKHSs of the constituant kernels.

## main definitions
 - `linearIsometryEquiv`: isometric equivalence between the RKHS `OfKernel (K + K')` and the
    quotient space over `OfKernel K × OfKernel K'`.
 - `projection`: isometry yielding the elements of `OfKernel K × OfKernel K'` achieving the norm of
    `OfKernel (K + K')`.
-/

public noncomputable section

open ContinuousLinearMap InnerProductSpace Submodule ComplexConjugate RKHS

namespace RKHS

namespace Add

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
variable (K K' : Matrix X X (V →L[𝕜] V))
variable [Fact K.PosSemidef] [Fact K'.PosSemidef]

instance : NormedAddCommGroup (OfKernel K) := by infer_instance
instance : InnerProductSpace 𝕜 (OfKernel K) := by infer_instance
instance : AddLeftMono (V →L[𝕜] V) := by
  refine ⟨fun f g₁ g₂ hg₁₂ => ?_⟩
  constructor
  · simp only [add_sub_add_left_eq_sub, toLinearMap_sub]
    exact hg₁₂.1
  · intro v
    simp [hg₁₂.2 v]

instance : Fact (K + K').PosSemidef :=
  ⟨Matrix.PosSemidef.add (Fact.out : K.PosSemidef) (Fact.out : K'.PosSemidef)⟩

/-- The operator `(f,g) ↦ ↑f + ↑f`, where addition is in `X → V`. -/
def generator : WithLp 2 ((OfKernel K) × (OfKernel K')) →L[𝕜] (X → V) :=
  ((coeCLM (H:=OfKernel K) 𝕜).coprod (coeCLM (H:=OfKernel K') 𝕜)) ∘L
    (WithLp.prodContinuousLinearEquiv 2 𝕜 (OfKernel K) (OfKernel K')).toContinuousLinearMap

@[simp]
lemma generator_apply (f : OfKernel K) (g : OfKernel K') (x : X) :
    generator K K' (WithLp.toLp 2 (f,g)) x = f x + g x := by
  rfl

instance : IsClosed ((generator K K').ker : Set (WithLp 2 ((OfKernel K) × (OfKernel K')))) :=
  (generator K K').isClosed_ker

lemma kerFun_mem_orthogonal (x : X) (v : V) :
    (WithLp.toLp 2 (kerFun (OfKernel K) x v, kerFun (OfKernel K') x v))
      ∈ (generator K K').kerᗮ := by
  intro p hp
  rw [LinearMap.mem_ker, funext_iff] at hp
  simp_all [generator, ← inner_add_left]

/-- The orthogonal complement of the span of the kernel‑vector pairs is exactly the kernel of the
    generator map `(f,g) ↦ ↑f + ↑g`. -/
lemma generator_ker : (generator K K').ker = (Submodule.span 𝕜 {p : WithLp 2
    ((OfKernel K) × (OfKernel K')) | ∃ x v, p = WithLp.toLp 2
      (kerFun (OfKernel K) x v, kerFun (OfKernel K') x v)})ᗮ := by
  refine le_antisymm
    ((Submodule.le_orthogonal_orthogonal (generator K K').ker).trans <| Submodule.orthogonal_le <|
      Submodule.span_le.mpr fun p ⟨x, v, hp⟩ ↦ hp ▸ kerFun_mem_orthogonal K K' x v)
    (fun q hq ↦ ?_)
  obtain ⟨f, g⟩ := q
  funext x
  refine ext_inner_left 𝕜 fun v ↦ ?_
  simp [inner_add_right, ← kerFun_inner, WithLp.prod_inner_apply,
    ← hq _ (Submodule.subset_span ⟨x, v, rfl⟩)]

/-- Helper function for `linearIsometryAux`. -/
private def toKerOrthogonal :
    H₀ (K + K') →ₗᵢ[𝕜] (generator K K').kerᗮ where
  toLinearMap := Finsupp.linearCombination 𝕜 (fun xv =>
    (⟨WithLp.toLp 2 (kerFun (OfKernel K) xv.1 xv.2, kerFun (OfKernel K') xv.1 xv.2),
      kerFun_mem_orthogonal K K' xv.1 xv.2⟩ : (generator K K').kerᗮ))
  norm_map' f := by
    simp_rw [← Submodule.norm_coe, norm_eq_sqrt_re_inner (𝕜 := 𝕜)]
    congr 2
    simp_rw [inner_H₀_def, Finsupp.linearCombination_apply, Finsupp.sum, ← coe_inner, sum_inner,
      inner_sum, inner_smul_left, inner_smul_right, mul_assoc]
    simp [inner_add_left, kerFun_apply]

-- The map whose extention with `.complL` yields `linearIsometry`. -/
private def linearIsometryAux :
    H₀ (K + K') →ₗᵢ[𝕜] WithLp 2 ((OfKernel K) × (OfKernel K')) ⧸ (generator K K').ker :=
  (Submodule.quotientEquivOrthogonal (generator K K').ker).symm.toLinearIsometry.comp
    (toKerOrthogonal K K')

/-- The RKHS made from a sum of kernels is linearly isometrically isomorphic to a quotient space
formed by quotienting the pair of RKHS formed by the consituent kernels with the kernel of the map
`generator`. -/
def linearIsometry :
    OfKernel (K + K') →ₗᵢ[𝕜] WithLp 2 ((OfKernel K) × (OfKernel K')) ⧸ (generator K K').ker where
  toFun f := (linearIsometryAux K K').toContinuousLinearMap.extend
    UniformSpace.Completion.toComplL f
  map_add' := by simp [map_add]
  map_smul' := by simp [map_smul]
  norm_map' f := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    induction f using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_eq (((linearIsometryAux K K').toContinuousLinearMap.extend
          UniformSpace.Completion.toComplL).continuous.norm) continuous_norm
    | ih x =>
      rw [← UniformSpace.Completion.coe_toComplL (S := 𝕜), ContinuousLinearMap.extend_eq _
        (by simp [UniformSpace.Completion.denseRange_coe])
        (by simp [UniformSpace.Completion.isUniformInducing_coe])]
      simp [(linearIsometryAux K K').norm_map x]

private lemma linearIsometry_kerFun_apply_eq_mk (x : X) (v : V) :
    linearIsometry K K' (kerFun (OfKernel (K + K')) x v) =
    Submodule.Quotient.mk (WithLp.toLp 2 (kerFun (OfKernel K) x v, kerFun (OfKernel K') x v)) := by
  simp only [linearIsometry, LinearIsometry.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
  rw [OfKernel.kerFun_OfKernel_apply, ← UniformSpace.Completion.coe_toComplL (S := 𝕜),
    ContinuousLinearMap.extend_eq _
      (by simp [UniformSpace.Completion.denseRange_coe])
      (by simp [UniformSpace.Completion.isUniformInducing_coe])]
  simp [linearIsometryAux, toKerOrthogonal]

/-- The RKHS made from a sum of kernels is linearly isometrically equivalent to a quotient space
formed by quotienting the pair of RKHS formed by the consituent kernels with the kernel of the map
`generator`. -/
def linearIsometryEquiv :
    OfKernel (K + K') ≃ₗᵢ[𝕜] WithLp 2 ((OfKernel K) × (OfKernel K')) ⧸ (generator K K').ker :=
  .ofSurjective (linearIsometry K K') <| by
    set W := WithLp 2 (OfKernel K × OfKernel K')
    set L : Submodule 𝕜 W := (generator K K').ker
    set T : Submodule 𝕜 W := Submodule.span 𝕜
      {p : W | ∃ x v, p = WithLp.toLp 2 (kerFun (OfKernel K) x v, kerFun (OfKernel K') x v)}
    have hdense : Dense ((Submodule.Quotient.mk : W → W ⧸ L) '' T) := by
      refine dense_iff_closure_eq.mpr (Set.univ_subset_iff.mp ?_)
      apply subset_trans ?_ (image_closure_subset_closure_image continuous_quotient_mk')
      rw [← topologicalClosure_coe, ← orthogonal_orthogonal_eq_closure, ← generator_ker K K']
      exact Set.univ_subset_iff.mpr (Set.eq_univ_of_forall fun y ↦ ⟨
        (generator K K').ker.quotientEquivOrthogonal y,
        ((generator K K').ker.quotientEquivOrthogonal y).2, by
          rw [Quotient.mk'_eq_mk', coe_quotientEquivOrthogonal, mk_quotientEquivOfIsCompl_apply]⟩)
    have hMapRange : (Submodule.Quotient.mk : W → W ⧸ L) '' T ⊆ (linearIsometry K K').range := by
      rintro _ ⟨t, ht, rfl⟩
      induction ht using Submodule.span_induction with
      | mem p hp =>
        obtain ⟨x, v, rfl⟩ := hp
        exact ⟨kerFun (OfKernel (K + K')) x v, linearIsometry_kerFun_apply_eq_mk K K' x v⟩
      | zero => exact ⟨0, by simp⟩
      | add p q _ _ ihp ihq =>
        obtain ⟨a, ha⟩ := ihp; obtain ⟨b, hb⟩ := ihq
        exact ⟨a + b, by simp [-LinearIsometry.coe_toLinearMap, ha, hb]⟩
      | smul c p _ ih =>
        obtain ⟨a, ha⟩ := ih
        exact ⟨c • a, by simp [ha]⟩
    rw [← Set.range_eq_univ]
    refine le_antisymm (Set.subset_univ _) ?_
    rw [← hdense.closure_eq,
      ← (linearIsometry K K').isometry.isClosedEmbedding.isClosed_range.closure_eq]
    exact closure_mono hMapRange

/-- The map taking every function in `OfKernel (K + K')` to the elements from
`WithLp 2 ((OfKernel K) × (OfKernel K'))` that minimizes the quotient norm. -/
def projection : OfKernel (K + K') →ₗᵢ[𝕜] WithLp 2 ((OfKernel K) × (OfKernel K')) :=
  (generator K K').kerᗮ.subtypeₗᵢ.comp
    ((generator K K').ker.quotientEquivOrthogonal.toLinearIsometry.comp
      (linearIsometryEquiv K K').toLinearIsometry)

@[simp low]
lemma coe_orthogonalProjection :
    ⇑(projection K K') = (((generator K K').kerᗮ).subtype
      ∘ (generator K K').ker.quotientEquivOrthogonal ∘ (linearIsometryEquiv K K')) := by
  rfl

theorem projection_kerFun (x : X) (v : V) :
    projection K K' (kerFun (OfKernel (K + K')) x v) =
      .toLp 2 ⟨kerFun (OfKernel K) x v, kerFun (OfKernel K') x v⟩ := by
  simp [projection, linearIsometryEquiv, linearIsometry_kerFun_apply_eq_mk, kerFun_mem_orthogonal]

theorem range_projection : Set.range (projection K K') = (generator K K').kerᗮ := by
  simp [projection, Set.range_comp, Set.range_comp]

theorem norm_sq_kerFun_add (x : X) (v : V) :
    ‖kerFun (OfKernel (K + K')) x v‖ ^ 2 =
      ‖kerFun (OfKernel K) x v‖ ^ 2 + ‖kerFun (OfKernel K') x v‖ ^ 2 := by
  simp [← (projection K K').norm_map, projection_kerFun, WithLp.prod_norm_sq_eq_of_L2]

section sumSpace

variable (H H' : Type*) [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [RKHS 𝕜 H X V]
  [CompleteSpace H] [NormedAddCommGroup H'] [InnerProductSpace 𝕜 H'] [RKHS 𝕜 H' X V]
  [CompleteSpace H']

instance : Fact (kernel H + kernel H').PosSemidef := by
  simp [fact_iff, Matrix.PosSemidef.add (posSemidef_kernel H) (posSemidef_kernel H')]

/-- The sum of two RKHS embedding in the same space of functions `X → V`. -/
abbrev sumSpace := OfKernel (kernel H + kernel H')

/-- `H + H₁` is shorthand for the RKHS `sumSpace H H₁`, which is the sum of the two RKHS. -/
scoped infix:50 " + " => sumSpace

end sumSpace

end Add

end RKHS
