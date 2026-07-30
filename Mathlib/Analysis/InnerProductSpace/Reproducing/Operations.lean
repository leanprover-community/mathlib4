/-
Copyright (c) 2026 Tjeerd Jan Heeringa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tjeerd Jan Heeringa
-/
module

public import Mathlib.Analysis.InnerProductSpace.Reproducing

/-!
# main defintions
-/

public section

open ContinuousLinearMap InnerProductSpace Submodule ComplexConjugate RKHS

namespace RKHS

namespace Add

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
variable (K K' : Matrix X X (V →L[𝕜] V))
variable [Fact K.PosSemidef] [Fact K'.PosSemidef]

noncomputable instance : NormedAddCommGroup (OfKernel K) := by infer_instance
noncomputable instance : InnerProductSpace 𝕜 (OfKernel K) := by infer_instance
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
noncomputable def generator : WithLp 2 ((OfKernel K) × (OfKernel K')) →L[𝕜] (X → V) :=
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

/-- Helper function for `linearIsometryAux`. -/
private noncomputable def toKerOrthogonal : H₀ (K + K') →ₗ[𝕜] (generator K K').kerᗮ :=
  Finsupp.linearCombination 𝕜 (fun xv =>
    (⟨WithLp.toLp 2 (kerFun (OfKernel K) xv.1 xv.2, kerFun (OfKernel K') xv.1 xv.2),
      kerFun_mem_orthogonal K K' xv.1 xv.2⟩ : (generator K K').kerᗮ))

/-- The map whose extention with `.complL` yields `linearIsometry`. -/
private noncomputable def linearIsometryAux :
    H₀ (K + K') →ₗᵢ[𝕜] WithLp 2 ((OfKernel K) × (OfKernel K')) ⧸ (generator K K').ker where
  toFun f := Submodule.Quotient.mk (toKerOrthogonal K K' f)
  map_add' := by simp [map_add]
  map_smul' := by simp [map_smul]
  norm_map' := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    simp_rw [(Submodule.quotientEquivOrthogonal_symm_eq_mk _ _ (toKerOrthogonal K K' _).2).symm,
      LinearIsometryEquiv.norm_map]
    intro f
    simp_rw [norm_eq_sqrt_re_inner (𝕜 := 𝕜)]
    congr 2
    simp_rw [SetLike.eta, toKerOrthogonal, inner_H₀_def, Finsupp.linearCombination_apply,
      Finsupp.sum, sum_inner, inner_sum, inner_smul_left, inner_smul_right, mul_assoc]
    simp [kerFun_apply, ← OfKernel.kernel_ofKernel, inner_add_left]

/-- The RKHS made from a sum of kernels is linearly isometrically isomorphic to a quotient space
formed by quotienting the pair of RKHS formed by the consituent kernels with the kernel of the map
`generator`. -/
noncomputable def linearIsometry :
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
      rw [← UniformSpace.Completion.coe_toComplL (𝕜 := 𝕜), ContinuousLinearMap.extend_eq _
        (by simp [UniformSpace.Completion.denseRange_coe])
        (by simp [UniformSpace.Completion.isUniformInducing_coe])]
      simp [(linearIsometryAux K K').norm_map x]

lemma linearIsometry_kerFun_apply_eq_mk (x : X) (v : V) :
    linearIsometry K K' (kerFun (OfKernel (K + K')) x v) =
    Submodule.Quotient.mk (WithLp.toLp 2 (kerFun (OfKernel K) x v, kerFun (OfKernel K') x v)) := by
  simp only [linearIsometry, linearIsometry, LinearIsometry.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
  rw [OfKernel.kerFun_OfKernel_apply, ← UniformSpace.Completion.coe_toComplL (𝕜 := 𝕜),
    ContinuousLinearMap.extend_eq _
      (by simp [UniformSpace.Completion.denseRange_coe])
      (by simp [UniformSpace.Completion.isUniformInducing_coe])]
  simp [linearIsometryAux, toKerOrthogonal]

theorem linearIsometry_surjective : Function.Surjective (linearIsometry K K') := by
  set W := WithLp 2 (OfKernel K × OfKernel K')
  set L : Submodule 𝕜 W := (generator K K').ker
  set T : Submodule 𝕜 W := Submodule.span 𝕜
    {p : W | ∃ x v, p = WithLp.toLp 2 (kerFun (OfKernel K) x v, kerFun (OfKernel K') x v)}
  -- `T` and `L` are exact orthogonal complements of one another.
  have hTL : Tᗮ = L := by
    refine le_antisymm (fun q hq ↦ ?_)
      ((Submodule.le_orthogonal_orthogonal L).trans <| Submodule.orthogonal_le <|
        Submodule.span_le.mpr fun p ⟨x, v, hp⟩ ↦ hp ▸ kerFun_mem_orthogonal K K' x v)
    obtain ⟨f, g⟩ := q
    funext x
    refine ext_inner_left 𝕜 fun v ↦ ?_
    have := hq _ (Submodule.subset_span ⟨x, v, rfl⟩)
    rw [WithLp.prod_inner_apply] at this
    simp only [kerFun_inner] at this
    simp [inner_add_right, this]
  -- Hence the image of `T` in the quotient is dense.
  have hdense : Dense ((Submodule.Quotient.mk : W → W ⧸ L) '' (T : Set W)) := by
    have hLperp : closure (T : Set W) = (Lᗮ : Set W) := by
      rw [← Submodule.topologicalClosure_coe, ← orthogonal_orthogonal_eq_closure, hTL]
    have hsurj : (Submodule.Quotient.mk : W → W ⧸ L) '' (Lᗮ : Set W) = Set.univ :=
      Set.eq_univ_of_forall fun y ↦
        ⟨L.quotientEquivOrthogonal y, (L.quotientEquivOrthogonal y).2, by simp⟩
    have hsub : (Submodule.Quotient.mk : W → W ⧸ L) '' (closure (T : Set W)) ⊆
        closure ((Submodule.Quotient.mk : W → W ⧸ L) '' (T : Set W)) :=
      image_closure_subset_closure_image continuous_quotient_mk'
    rw [hLperp, hsurj] at hsub
    exact dense_iff_closure_eq.mpr (Set.univ_subset_iff.mp hsub)
  -- That image lies in the range of `linearIsometry K K'`.
  have hMapRange : (Submodule.Quotient.mk : W → W ⧸ L) '' (T : Set W) ⊆
      Set.range (linearIsometry K K') := by
    rintro _ ⟨t, ht, rfl⟩
    induction ht using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨x, v, rfl⟩ := hp
      exact ⟨kerFun (OfKernel (K + K')) x v, linearIsometry_kerFun_apply_eq_mk K K' x v⟩
    | zero => exact ⟨0, by simp⟩
    | add p q _ _ ihp ihq =>
      obtain ⟨a, ha⟩ := ihp; obtain ⟨b, hb⟩ := ihq
      exact ⟨a + b, by simp [ha, hb]⟩
    | smul c p _ ih =>
      obtain ⟨a, ha⟩ := ih
      exact ⟨c • a, by simp [ha]⟩
  -- The range is closed (isometric image of a complete space); a dense subset of a closed
  -- set fills it.
  rw [← Set.range_eq_univ]
  refine le_antisymm (Set.subset_univ _) ?_
  rw [← hdense.closure_eq,
    ← (linearIsometry K K').isometry.isClosedEmbedding.isClosed_range.closure_eq]
  exact closure_mono hMapRange

/-- The RKHS made from a sum of kernels is linearly isometrically equivalent to a quotient space
formed by quotienting the pair of RKHS formed by the consituent kernels with the kernel of the map
`generator`. -/
noncomputable def linearIsometryEquiv :
    OfKernel (K + K') ≃ₗᵢ[𝕜] WithLp 2 ((OfKernel K) × (OfKernel K')) ⧸ (generator K K').ker :=
  LinearIsometryEquiv.ofSurjective (linearIsometry K K') (linearIsometry_surjective K K')

/-- The map taking every function in `OfKernel (K + K')` to the elements from
`WithLp 2 ((OfKernel K) × (OfKernel K'))` that minimizes the quotient norm. -/
noncomputable def projection : OfKernel (K + K') →L[𝕜] WithLp 2 ((OfKernel K) × (OfKernel K')) :=
  ((generator K K').kerᗮ).subtypeL ∘L
    ((linearIsometryEquiv K K').trans (generator K K').ker.quotientEquivOrthogonal)

@[simp low]
lemma coe_orthogonalProjection_apply :
    ⇑(projection K K') = (((generator K K').kerᗮ).subtypeL
      ∘ (generator K K').ker.quotientEquivOrthogonal ∘ (linearIsometry K K')) := by
  rfl

lemma projection_apply (f : OfKernel (K + K')) :
    projection K K' f = (((generator K K').kerᗮ).subtypeL
      ∘ (generator K K').ker.quotientEquivOrthogonal ∘ (linearIsometry K K')) f := by
  rfl

lemma projection_inner (f g : OfKernel (K + K')) :
    ⟪projection K K' f, projection K K' g⟫_𝕜 = ⟪f, g⟫_𝕜 := by
  simp [← ((linearIsometryEquiv K K').trans
    (generator K K').ker.quotientEquivOrthogonal).inner_map_map, projection]

theorem projection_kerFun (x : X) (v : V) :
    projection K K' (kerFun (OfKernel (K + K')) x v) =
      .toLp 2 ⟨kerFun (OfKernel K) x v, kerFun (OfKernel K') x v⟩ := by
  simp [projection, linearIsometryEquiv, linearIsometry_kerFun_apply_eq_mk,
    kerFun_mem_orthogonal K K' x v]

lemma norm_projection_le :
    ‖projection K K'‖ ≤ 1 := by
  grw [projection, ContinuousLinearMap.opNorm_comp_linearIsometryEquiv, norm_subtypeL_le]

lemma norm_projection [Nontrivial ((generator K K')).kerᗮ] :
    ‖projection K K'‖ = 1 := by
  grw [projection, ContinuousLinearMap.opNorm_comp_linearIsometryEquiv, norm_subtypeL]

end Add

end RKHS
