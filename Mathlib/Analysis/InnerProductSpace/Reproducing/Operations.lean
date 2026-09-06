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

#### Add
 - `generator`: the operator `(f,g) ↦ ↑f + ↑f` inducing the RKHS `H + H'`.
 - `OfKernelAddEquiv`: isometric equivalence between the RKHS `OfKernel (K + K')` and the
    quotient space over `OfKernel K × OfKernel K'`.
 - `projection`: isometry yielding the elements of `H × H'` achieving the norm of `H + H'`.

#### SMul
 - `generator`: the operator `f ↦ c • ↑f` inducing the RKHS `c • H`.


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

omit [CompleteSpace V] [CompleteSpace H] [CompleteSpace H'] in
lemma range_generator :
    (generator H H').range = (coeCLM (H:=H) 𝕜).range + (coeCLM (H:=H') 𝕜).range := by
  simp only [generator, ContinuousLinearMap.toLinearMap_comp,
    ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap, LinearEquiv.range_comp,
    ContinuousLinearMap.range_coprod, Submodule.add_eq_sup]

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

/-- The RKHSS constructed from the sum of two kernels is linearly isometrically isomorphic to the
sum of the RKHSs created by the consituant kernels. -/
def OfKernelAddEquiv : OfKernel (K + K') ≃ₗᵢ[𝕜] OfKernel K + OfKernel K' := equiv
  (by simp [OfKernel.kernel_ofKernel, kernel_sum_eq_sum_of_kernel])

@[simp]
lemma coe_OfKernelAddEquiv (f : OfKernel (K + K')) : ⇑(OfKernelAddEquiv K K' f) = ⇑f := by
  simp [OfKernelAddEquiv]

end OfKernel

omit [CompleteSpace V]

/-- Projection that takes a function `f : H + H'` to the unique pair in `H × H'` that achieves
its norm. -/
def projection : H + H' →ₗᵢ[𝕜] WithLp 2 (H × H') :=
  ((generator H H').kerᗮ).subtypeₗᵢ.comp
    (generator H H').ker.quotientEquivOrthogonal.toLinearIsometry

@[simp low]
lemma coe_orthogonalProjection :
    ⇑(projection H H') = ((generator H H').kerᗮ).subtype
      ∘ (generator H H').ker.quotientEquivOrthogonal := by
  rfl

theorem range_projection : (projection H H').range = (generator H H').kerᗮ := by
  apply SetLike.coe_injective
  change Set.range (projection H H') = _
  simp [projection, Set.range_comp]

variable {H H'} in
lemma mk_projection (f : H + H') :
    Submodule.Quotient.mk (projection H H' f : WithLp 2 (H × H')) = f := by
  rw [← quotientEquivOrthogonal_symm_eq_mk _ _ _, LinearIsometryEquiv.symm_apply_eq]
  · simp
  rw [← range_projection H H']
  exact LinearMap.mem_range_self _ f

variable [CompleteSpace V] in
theorem projection_kerFun (x : X) (v : V) :
    projection H H' (kerFun (H + H') x v) = .toLp 2 ⟨kerFun H x v, kerFun H' x v⟩ := by
  simp [projection, kerFun_apply_eq_mk, kerFun_mem_orthogonal]

variable [CompleteSpace V] in
theorem norm_sq_kerFun_add (x : X) (v : V) :
    ‖kerFun (H + H') x v‖ ^ 2 = ‖kerFun H x v‖ ^ 2 + ‖kerFun H' x v‖ ^ 2 := by
  simp [← (projection H H').norm_map, projection_kerFun, WithLp.prod_norm_sq_eq_of_L2]

theorem exists_eq_add_and_norm_sq_eq_add (f : H + H') :
    ∃ (f₁ : H) (f₂ : H'), (⇑f = f₁ + f₂) ∧ ‖f‖ ^ 2 = ‖f₁‖ ^ 2 + ‖f₂‖ ^ 2 := by
  let p := projection H H' f
  have hp : projection H H' f = p := rfl
  use p.ofLp.1, p.ofLp.2
  constructor
  · rw [← mk_projection f, hp]
    ext
    change generator H H' p _ = _
    simp only [WithLp.ofLp_fst, WithLp.ofLp_snd, Pi.add_apply]
    exact generator_apply p.fst p.snd _
  · simp [← (projection H H').norm_map, hp, WithLp.prod_norm_sq_eq_of_L2]

theorem norm_sq_le (f : H + H') (f₁ : H) (f₂ : H') (h : ⇑f = f₁ + f₂) :
    ‖f‖ ^ 2 ≤ ‖f₁‖ ^ 2 + ‖f₂‖ ^ 2 := by
  calc
    ‖f‖ ^ 2 = ‖Submodule.Quotient.mk (p := (generator H H').ker) (WithLp.toLp 2 (f₁, f₂))‖ ^ 2 := by
      congr
      ext
      simp [h]
      rfl
    _ ≤ ‖WithLp.toLp 2 (f₁, f₂)‖ ^ 2 := by
      gcongr
      exact Submodule.Quotient.norm_mk_le _ _
    _ = ‖f₁‖ ^ 2 + ‖f₂‖ ^ 2 := WithLp.prod_norm_sq_eq_of_L2 _

end Add

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

omit [CompleteSpace V] [CompleteSpace H] in
lemma range_generator :
    (generator H c).range = (c • coeCLM (H:=H) 𝕜).range := by
  simp [generator]

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


section OfKernel

variable (K : Matrix X X (V →L[𝕜] V))
variable [Fact K.PosSemidef]

open ComplexOrder in
instance (c : ℝ) : Fact ((c : 𝕜) ^ 2 • K).PosSemidef := by
  rw [fact_iff]
  apply Matrix.PosSemidef.smul (Fact.out : K.PosSemidef)
  rw [← RCLike.ofReal_pow, RCLike.ofReal_nonneg]
  exact sq_nonneg c

/-- The RKHSS constructed from a scaled kernel is linearly isometrically isomorphic to the scaled
space of the original kernel. -/
def OfKernelSMulEquiv (c : 𝕜) : OfKernel ((‖c‖ : 𝕜) ^ 2 • K) ≃ₗᵢ[𝕜] smulSpace (OfKernel K) c :=
  equiv (by simp [OfKernel.kernel_ofKernel, kernel_smul_eq_norm_sq_smul_kernel])

@[simp]
lemma coe_OfKernelSMulEquiv (f : OfKernel ((‖c‖ : 𝕜) ^ 2 • K)) :
    ⇑(OfKernelSMulEquiv K c f) = ⇑f := by
  simp [OfKernelSMulEquiv]

end OfKernel


end SMul

end RKHS
