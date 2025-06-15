/-
Copyright (c) 2023 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.ProdLp

/-!
# `L²` inner product space structure on products of inner product spaces

The `L²` norm on product of two inner product spaces is compatible with an inner product
$$
\langle x, y\rangle = \langle x_1, y_1 \rangle + \langle x_2, y_2 \rangle.
$$
This is recorded in this file as an inner product space instance on `WithLp 2 (E × F)`.
-/

variable {𝕜 ι₁ ι₂ E F : Type*}
variable [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]
  [InnerProductSpace 𝕜 F]

namespace WithLp
open scoped InnerProductSpace

variable (E F)

noncomputable instance instProdInnerProductSpace :
    InnerProductSpace 𝕜 (WithLp 2 (E × F)) where
  inner x y := ⟪x.fst, y.fst⟫_𝕜 + ⟪x.snd, y.snd⟫_𝕜
  norm_sq_eq_re_inner x := by
    simp [prod_norm_sq_eq_of_L2, ← norm_sq_eq_re_inner]
  conj_inner_symm x y := by
    simp
  add_left x y z := by
    simp only [add_fst, add_snd, inner_add_left]
    ring
  smul_left x y r := by
    simp only [smul_fst, inner_smul_left, smul_snd]
    ring

variable {E F}

@[simp]
theorem prod_inner_apply (x y : WithLp 2 (E × F)) :
    ⟪x, y⟫_𝕜 = ⟪x.fst, y.fst⟫_𝕜 + ⟪x.snd, y.snd⟫_𝕜 := rfl

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
    · simp only [Sum.forall, norm_eq_sqrt_re_inner (𝕜 := 𝕜), Real.sqrt_eq_one]
      simp [← Real.sqrt_eq_one, ← norm_eq_sqrt_re_inner (𝕜 := 𝕜), v.orthonormal.1, w.orthonormal.1]
    · unfold Pairwise
      simp only [ne_eq, Basis.map_apply, Basis.prod_apply, LinearMap.coe_inl,
        OrthonormalBasis.coe_toBasis, LinearMap.coe_inr, WithLp.linearEquiv_symm_apply,
        WithLp.prod_inner_apply, WithLp.equiv_symm_fst, WithLp.equiv_symm_snd, Sum.forall,
        Sum.elim_inl, Function.comp_apply, inner_zero_right, add_zero, Sum.elim_inr, zero_add,
        Sum.inl.injEq, not_false_eq_true, inner_zero_left, forall_true_left, implies_true, and_true,
        Sum.inr.injEq, true_and]
      exact ⟨v.orthonormal.2, w.orthonormal.2⟩)

@[simp] theorem prod_apply (v : OrthonormalBasis ι₁ 𝕜 E) (w : OrthonormalBasis ι₂ 𝕜 F) :
    ∀ i : ι₁ ⊕ ι₂, v.prod w i =
      Sum.elim ((LinearMap.inl 𝕜 E F) ∘ v) ((LinearMap.inr 𝕜 E F) ∘ w) i := by
  rw [Sum.forall]
  unfold OrthonormalBasis.prod
  aesop

end OrthonormalBasis
end
