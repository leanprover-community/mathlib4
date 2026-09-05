/-
Copyright (c) 2026 Tjeerd Jan Heeringa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tjeerd Jan Heeringa
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Reproducing

/-!
# Operations on RKHS
This file implements the maps that show how RKHSs created from kernels formed by applying operations
to a set of kernels relate to the RKHSs of the constituant kernels.

## main definitions
The definitions are sorted by operation.

#### SMul
 - `generator`: the operator `f ↦ c • ↑f` inducing the RKHS `c • H`.

## Implementation notes


-/

public noncomputable section

namespace RKHS

namespace SMul

open Submodule InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [RKHS 𝕜 H X V]
variable (c : 𝕜)

/-- The operator `f ↦ c • ↑f`, where scalar multiplication is in `X → V`. -/
def generator : H →L[𝕜] (X → V) := c • coeCLM 𝕜

variable {H} in
omit [CompleteSpace H] [CompleteSpace V] in
@[simp]
lemma generator_apply (f : H) (x : X) : generator H c f x = c • f x := by rfl

instance : IsClosed ((generator H c).ker : Set H) := (generator H c).isClosed_ker

lemma kerFun_mem_orthogonal (x : X) (v : V) (hc : c ≠ 0) : kerFun H x v ∈ (generator H c).kerᗮ := by
  intro p hp
  rw [LinearMap.mem_ker, funext_iff] at hp
  simp_all

/-- The RKHS `H` multiplied by the scalar `c`, defined as quotient of the original `H`. -/
abbrev smulSpace := H ⧸ (generator H c).ker

instance : RKHS 𝕜 (smulSpace H c) X V where
  coeCLM := (generator H c).ker.liftQL (generator H c) (le_refl _)
  coeCLM_injective := fun f g hfg => by
    refine (Function.Injective.eq_iff ?_).mp hfg
    simp [← LinearMap.ker_eq_bot, ker_liftQ_eq_bot]

lemma kerFun_apply_eq_mk {c} (hc : c ≠ 0) (x : X) (v : V) :
    kerFun (smulSpace H c) x v = Submodule.Quotient.mk (starRingEnd 𝕜 c • kerFun H x v) := by
  rw [Quotient.mk_smul ((generator H c)).ker ((starRingEnd 𝕜) c) ((kerFun H x) v),
    ← quotientEquivOrthogonal_symm_eq_mk (generator H c).ker _ (kerFun_mem_orthogonal H c x v hc),
    ← LinearIsometryEquiv.map_smul, (generator H c).ker.quotientEquivOrthogonal.eq_symm_apply,
    ext_iff_inner_right (𝕜 := 𝕜)]
  intro f
  rw [(generator H c).ker.quotientEquivOrthogonal.inner_map_eq_flip,
    (generator H c).ker.quotientEquivOrthogonal_symm_eq_mk, kerFun_inner]
  simp only [SetLike.mk_smul_mk, coe_inner]
  change ⟪v, generator H c (↑f) x⟫_𝕜 = _
  simp [generator, inner_smul_left, inner_smul_right]

theorem kernel_smul_eq_norm_sq_smul_kernel : kernel (smulSpace H c) = (‖c‖ : 𝕜) ^ 2 • kernel H := by
  by_cases hc : c = 0
  · subst c
    have : Subsingleton (smulSpace H 0) := by
      simp [smulSpace, Submodule.Quotient.subsingleton_iff, generator]
    have hcoe : coeCLM 𝕜 (H := smulSpace H 0) = 0 := Subsingleton.eq_zero _
    ext
    simp only [kernel_apply, kerFun_def, hcoe, ContinuousLinearMap.comp_zero, map_zero, zero_apply,
      norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Matrix.smul_apply,
      ContinuousLinearMap.adjoint_adjoint, zero_smul]
  · ext
    simp only [← kerFun_apply, kerFun_apply_eq_mk H hc, Quotient.mk_smul, coe_smul, Pi.smul_apply,
      Matrix.smul_apply, smul_apply]
    change starRingEnd 𝕜 c • generator H c (kerFun H _ _ ) _ = _
    simp [generator_apply, smul_smul, RCLike.conj_mul]

end SMul

end RKHS
