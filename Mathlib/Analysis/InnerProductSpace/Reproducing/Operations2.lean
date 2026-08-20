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
 - `OfKernel_add_equiv`: isometric equivalence between the RKHS `OfKernel (K + K')` and the
    quotient space over `OfKernel K × OfKernel K'`.
 - `projection`: isometry yielding the elements of `H × H'` achieving the norm of `H + H'`.
-/

public noncomputable section

open InnerProductSpace Submodule RKHS

namespace RKHS

namespace Add

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable (H' : Type*) [NormedAddCommGroup H'] [InnerProductSpace 𝕜 H'] [CompleteSpace H']
variable [RKHS 𝕜 H X V] [RKHS 𝕜 H' X V]

/-- The operator `(f,g) ↦ ↑f + ↑f`, where addition is in `X → V`. -/
def generator : WithLp 2 (H × H') →L[𝕜] (X → V) :=
  ((coeCLM (H:=H) 𝕜).coprod (coeCLM (H:=H') 𝕜)) ∘L
    (WithLp.prodContinuousLinearEquiv 2 𝕜 H H').toContinuousLinearMap

variable {H H'} in
omit [CompleteSpace H] [CompleteSpace H'] [CompleteSpace V] in
@[simp]
lemma generator_apply (f : H) (g : H') (x : X) :
    generator H H' (WithLp.toLp 2 (f,g)) x = f x + g x := by
  rfl

instance : IsClosed ((generator H H').ker : Set (WithLp 2 (H × H'))) :=
  (generator H H').isClosed_ker

lemma kerFun_mem_orthogonal (x : X) (v : V) :
    (WithLp.toLp 2 (kerFun H x v, kerFun H' x v)) ∈ (generator H H').kerᗮ := by
  intro p hp
  rw [LinearMap.mem_ker, funext_iff] at hp
  simp_all [generator, ← inner_add_left]

/-- The sum of two RKHS embedding in the same space of functions `X → V`. -/
abbrev sumSpace := WithLp 2 (H × H') ⧸ (generator H H').ker

/-- `H + H'` is shorthand for the RKHS `sumSpace H H'`, which is the sum of the two RKHS. -/
scoped infix:50 " + " => sumSpace

instance : RKHS 𝕜 (H + H') X V where
  coeCLM := (generator H H').ker.liftQL (generator H H') (le_refl _)
  coeCLM_injective := fun f g hfg => by
    refine (Function.Injective.eq_iff ?_).mp hfg
    simp [← LinearMap.ker_eq_bot, ker_liftQ_eq_bot]

lemma kerFun_apply_eq_mk (x : X) (v : V) :
    kerFun (H + H') x v = Submodule.Quotient.mk (WithLp.toLp 2 (kerFun H x v, kerFun H' x v)) := by
  rw [← quotientEquivOrthogonal_symm_eq_mk (generator H H').ker _
    (kerFun_mem_orthogonal H H' x v), (generator H H').ker.quotientEquivOrthogonal.eq_symm_apply,
    ext_iff_inner_right (𝕜 := 𝕜)]
  intro f
  rw [(generator H H').ker.quotientEquivOrthogonal.inner_map_eq_flip,
    (generator H H').ker.quotientEquivOrthogonal_symm_eq_mk, kerFun_inner]
  simp only [coe_inner, WithLp.prod_inner_apply, WithLp.ofLp_fst, kerFun_inner, WithLp.ofLp_snd]
  change ⟪v, generator H H' (↑f) x⟫_𝕜 = _
  simp [generator, inner_add_right]

theorem kernel_sum_eq_sum_of_kernel : kernel (H + H') = kernel H + kernel H' := by
  ext
  simp [← kerFun_apply, kerFun_apply_eq_mk H H' _ _]
  rfl

section OfKernel

variable (K K' : Matrix X X (V →L[𝕜] V))
variable [Fact K.PosSemidef] [Fact K'.PosSemidef]

instance : Fact (K + K').PosSemidef :=
  ⟨Matrix.PosSemidef.add (Fact.out : K.PosSemidef) (Fact.out : K'.PosSemidef)⟩

def OfKernel_add_equiv : OfKernel (K + K') ≃ₗᵢ[𝕜] OfKernel K + OfKernel K' := equiv
  (by simp [OfKernel.kernel_ofKernel, kernel_sum_eq_sum_of_kernel])

end OfKernel

omit [CompleteSpace V]

/-- Projection that takes a function `f : Sum' H H'` to the unique pair in `WithLp 2 H × H'` that
achieves its norm. -/
def projection : H + H' →ₗᵢ[𝕜] WithLp 2 (H × H') :=
  ((generator H H').kerᗮ).subtypeₗᵢ.comp
    (generator H H').ker.quotientEquivOrthogonal.toLinearIsometry

@[simp low]
lemma coe_orthogonalProjection :
    ⇑(projection H H') = ((generator H H').kerᗮ).subtype
      ∘ (generator H H').ker.quotientEquivOrthogonal := by
  rfl

variable [CompleteSpace V] in
theorem projection_kerFun (x : X) (v : V) :
    projection H H' (kerFun (H + H') x v) = .toLp 2 ⟨kerFun H x v, kerFun H' x v⟩ := by
  simp [projection, kerFun_apply_eq_mk, kerFun_mem_orthogonal]

theorem range_projection : Set.range (projection H H') = (generator H H').kerᗮ := by
  simp [projection, Set.range_comp]

variable [CompleteSpace V] in
theorem norm_sq_kerFun_add (x : X) (v : V) :
    ‖kerFun (H + H') x v‖ ^ 2 = ‖kerFun H x v‖ ^ 2 + ‖kerFun H' x v‖ ^ 2 := by
  simp [← (projection H H').norm_map, projection_kerFun, WithLp.prod_norm_sq_eq_of_L2]

end Add

end RKHS
