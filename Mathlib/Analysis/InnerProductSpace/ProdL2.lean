/-
Copyright (c) 2023 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.ProdLp

/-!
# `L²` inner product space structure on products of inner product spaces

The `L²` norm on product of two inner product spaces is compatible with an inner product
$$
\langle x, y\rangle = \langle x_1, y_1 \rangle + \langle x_2, y_2 \rangle.
$$
This is recorded in this file as an inner product space instance on `WithLp 2 (E × F)`.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

open Module
open scoped InnerProductSpace

variable {𝕜 ι₁ ι₂ E F : Type*}
variable [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]
  [InnerProductSpace 𝕜 F]

namespace WithLp

noncomputable instance instProdInnerProductSpace :
    InnerProductSpace 𝕜 (WithLp 2 (E × F)) where
  inner x y := ⟪x.fst, y.fst⟫_𝕜 + ⟪x.snd, y.snd⟫_𝕜
  norm_sq_eq_re_inner x := by
    simp [prod_norm_sq_eq_of_L2]
  conj_inner_symm x y := by
    simp
  add_left x y z := by
    simp only [add_fst, add_snd, inner_add_left]
    ring
  smul_left x y r := by
    simp only [smul_fst, inner_smul_left, smul_snd]
    ring

@[simp]
theorem prod_inner_apply (x y : WithLp 2 (E × F)) :
    ⟪x, y⟫_𝕜 = ⟪(ofLp x).fst, (ofLp y).fst⟫_𝕜 + ⟪(ofLp x).snd, (ofLp y).snd⟫_𝕜 := rfl

end WithLp

noncomputable section
namespace OrthonormalBasis

variable [Fintype ι₁] [Fintype ι₂]

/-- The product of two orthonormal bases is a basis for the L2-product. -/
def prod (v : OrthonormalBasis ι₁ 𝕜 E) (w : OrthonormalBasis ι₂ 𝕜 F) :
    OrthonormalBasis (ι₁ ⊕ ι₂) 𝕜 (WithLp 2 (E × F)) :=
  ((v.toBasis.prod w.toBasis).map (WithLp.linearEquiv 2 𝕜 (E × F)).symm).toOrthonormalBasis
  (by
    constructor
    · simp
    · unfold Pairwise
      simp only [ne_eq, Basis.map_apply, Basis.prod_apply, LinearMap.coe_inl,
        OrthonormalBasis.coe_toBasis, LinearMap.coe_inr, WithLp.coe_symm_linearEquiv,
        WithLp.prod_inner_apply, Sum.forall, Sum.elim_inl, Function.comp_apply, inner_zero_right,
        add_zero, Sum.elim_inr, zero_add, Sum.inl.injEq, reduceCtorEq, not_false_eq_true,
        inner_zero_left, imp_self, implies_true, and_true, Sum.inr.injEq, true_and]
      exact ⟨v.orthonormal.2, w.orthonormal.2⟩)

@[simp] theorem prod_apply (v : OrthonormalBasis ι₁ 𝕜 E) (w : OrthonormalBasis ι₂ 𝕜 F) :
    ∀ i : ι₁ ⊕ ι₂, v.prod w i =
      Sum.elim ((WithLp.toLp 2) ∘ (LinearMap.inl 𝕜 E F) ∘ v)
        ((WithLp.toLp 2) ∘ (LinearMap.inr 𝕜 E F) ∘ w) i := by
  rw [Sum.forall]
  unfold OrthonormalBasis.prod
  aesop

end OrthonormalBasis

namespace Submodule

variable (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] (x : E)

/-- If a subspace `K` of an inner product space `E` admits an orthogonal projection, then `E` is
isometrically isomorphic to the `L²` product of `K` and `Kᗮ`. -/
@[simps! symm_apply]
def orthogonalDecomposition : E ≃ₗᵢ[𝕜] WithLp 2 (K × Kᗮ) where
  __ := (K.prodEquivOfIsCompl Kᗮ isCompl_orthogonal_of_hasOrthogonalProjection).symm
    ≪≫ₗ (WithLp.linearEquiv 2 𝕜 (K × Kᗮ)).symm
  norm_map' _ := by
    rw [← sq_eq_sq₀ (by positivity) (by positivity), WithLp.prod_norm_sq_eq_of_L2,
      K.norm_sq_eq_add_norm_sq_projection]
    simp [starProjection_apply_eq_isComplProjection]

@[simp]
theorem orthogonalDecomposition_apply :
    K.orthogonalDecomposition x =
      .toLp 2 (K.orthogonalProjection x, Kᗮ.orthogonalProjection x) := by
  simp [orthogonalDecomposition, orthogonalProjection_apply_eq_linearProjOfIsCompl]

theorem toLinearEquiv_orthogonalDecomposition :
    K.orthogonalDecomposition.toLinearEquiv =
      (K.prodEquivOfIsCompl Kᗮ isCompl_orthogonal_of_hasOrthogonalProjection).symm ≪≫ₗ
        (WithLp.linearEquiv 2 𝕜 (K × Kᗮ)).symm :=
  rfl

theorem toLinearEquiv_orthogonalDecomposition_symm :
    K.orthogonalDecomposition.symm.toLinearEquiv =
      WithLp.linearEquiv 2 𝕜 (K × Kᗮ) ≪≫ₗ
        K.prodEquivOfIsCompl Kᗮ isCompl_orthogonal_of_hasOrthogonalProjection :=
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem coe_orthogonalDecomposition :
    (K.orthogonalDecomposition : E →L[𝕜] WithLp 2 (K × Kᗮ)) =
      (WithLp.prodContinuousLinearEquiv 2 𝕜 K Kᗮ).symm ∘L
        K.orthogonalProjection.prod Kᗮ.orthogonalProjection := by
  ext; simp

set_option backward.isDefEq.respectTransparency false in
theorem coe_orthogonalDecomposition_symm :
    (K.orthogonalDecomposition.symm : WithLp 2 (K × Kᗮ) →L[𝕜] E) =
      K.subtypeL.coprod Kᗮ.subtypeL ∘L WithLp.prodContinuousLinearEquiv 2 𝕜 K Kᗮ :=
  rfl

theorem fst_orthogonalDecomposition_apply :
    (K.orthogonalDecomposition x).fst = K.orthogonalProjection x := by
  simp

theorem snd_orthogonalDecomposition_apply :
    (K.orthogonalDecomposition x).snd = Kᗮ.orthogonalProjection x := by
  simp

set_option backward.isDefEq.respectTransparency false in
theorem fstL_comp_coe_orthogonalDecomposition :
    WithLp.fstL 2 𝕜 K Kᗮ ∘L K.orthogonalDecomposition = K.orthogonalProjection := by
  ext; simp

set_option backward.isDefEq.respectTransparency false in
theorem sndL_comp_coe_orthogonalDecomposition :
    WithLp.sndL 2 𝕜 K Kᗮ ∘L K.orthogonalDecomposition = Kᗮ.orthogonalProjection := by
  ext; simp

end Submodule

end
