/-
Copyright (c) 2026 Hampus Nyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hampus Nyberg, Yaël Dillies
-/
module

public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.Normed.Lp.WithLp
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Reproducing Kernel Hilbert Spaces

This file defines vector-valued reproducing Kernel Hilbert spaces, which are Hilbert spaces of
functions, as well as characterizing these spaces in terms of infinite-dimensional
positive semidefinite matrices.

## Main results

- `RKHS`: the class of reproducing kernel Hilbert spaces
- `RKHS.kernel`: the kernel of a RKHS as a matrix.
- `RKHS.kerFun`: the kernel functions of a RKHS.
- `RKHS.kerFun_dense`: the kernel functions are dense in the Hilbert space.
- `RKHS.posSemidef_kernel`: The kernel is positive semidefinite.
- `RKHS.OfKernel`: RKHS constructed from a positive semidefinite matrix.
- `RKHS.kernel_ofKernel`: The kernel of the constructed RKHS is equal to the matrix, this is
    essentially Moore's theorem.

## TODO

- Privatize `RKHS.H₀`

## References
* [Paulsen, Vern I. and Raghupathi, Mrinal,
  *An introduction to the theory of reproducing kernel Hilbert spaces*][MR3526117]
-/

public noncomputable section

open ContinuousLinearMap InnerProductSpace Submodule ComplexConjugate

/--
A reproducing kernel Hilbert space is a Hilbert space with an
injection to functions mapping into another Hilbert space, such that point evaluation is continuous.
-/
class RKHS (𝕜 : outParam Type*) (H : Type*) (X V : outParam Type*) [RCLike 𝕜]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] where
  /-- Continuous injection to functions from the reproducing kernel Hilbert space `H` to functions
  from the domain `X` to the Hilbert space `V` -/
  coeCLM (𝕜) : H →L[𝕜] X → V
  coeCLM_injective : Function.Injective (coeCLM : H → X → V)

namespace RKHS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable [RKHS 𝕜 H X V]

/--
Each element of a reproducing kernel Hilbert space may be coerced into a function.
-/
instance instFunLike : FunLike H X V where
  coe f := coeCLM 𝕜 f
  coe_injective := coeCLM_injective

@[ext]
lemma ext {f g : H} (h : ∀ x, f x = g x) : f = g := DFunLike.ext _ _ h

@[simp]
lemma coeCLM_apply (f : H) : coeCLM 𝕜 f = f := rfl

@[simp]
lemma coe_zero : ⇑(0 : H) = 0 := (coeCLM 𝕜).map_zero ..

@[simp]
lemma coe_add (f g : H) : ⇑(f + g) = f + g := (coeCLM 𝕜).map_add ..

@[simp]
lemma coe_sub (f g : H) : ⇑(f - g) = f - g := (coeCLM 𝕜).map_sub (M₂ := X → V) ..

@[simp]
lemma coe_neg (f : H) : ⇑(-f) = -f := (coeCLM 𝕜).map_neg (M₂ := X → V) ..

@[simp]
lemma coe_smul (f : H) (c : 𝕜) : ⇑(c • f) = c • f := (coeCLM 𝕜).map_smul ..

@[simp]
lemma continuous_eval (x : X) : Continuous (fun (f : H) ↦ f x) := by
  simp_rw [← coeCLM_apply]
  fun_prop

variable (H) [CompleteSpace H] [CompleteSpace V]

/-- The kernel functions of a reproducing kernel Hilbert space are the adjoint of
the point evaluation. -/
def kerFun (x : X) : V →L[𝕜] H := (.proj x ∘L coeCLM 𝕜).adjoint

/-- The kernel of a reproducing kernel Hilbert space is a matrix of entries given by the
kernel functions. -/
def kernel : Matrix X X (V →L[𝕜] V) := .of fun x y ↦ (kerFun H x).adjoint ∘L kerFun H y

lemma kerFun_apply (y : X) (v : V) (x : X) : kerFun H y v x = kernel H x y v := by
  simp [kernel, kerFun]

lemma kernel_apply (x y : X) : kernel H x y = (kerFun H x).adjoint ∘L kerFun H y := by
  simp [kerFun, kernel]

variable {H} in
/-- Point evaluation `f ↦ f x` is the adjoint of the kernel function `kerFun H x`. -/
@[simp]
lemma adjoint_kerFun (x : X) (f : H) : (kerFun H x).adjoint f = f x := by
  simp [kerFun]

variable {H} in
/-- The "reproducing" property of the kernel functions, left version. -/
@[simp]
lemma kerFun_inner (x : X) (v : V) (f : H) : ⟪kerFun H x v, f⟫_𝕜 = ⟪v, f x⟫_𝕜 := by
  simp [kerFun, ← adjoint_inner_right]

variable {H} in
/-- The "reproducing" property of the kernel functions, right version. -/
@[simp]
lemma inner_kerFun (x : X) (v : V) (f : H) : ⟪f, kerFun H x v⟫_𝕜 = ⟪f x, v⟫_𝕜 := by
  simp [kerFun, ← adjoint_inner_left]

/-- The "reproducing" property of the kernel. -/
lemma kernel_inner (x y : X) (v w : V) :
    ⟪kernel H x y v, w⟫_𝕜 = ⟪kerFun H y v, kerFun H x w⟫_𝕜 := by
  simp [← adjoint_inner_left, kernel]

lemma norm_kernel_eq_norm_kerFun_sq (x) : ‖kernel H x x‖ = ‖kerFun H x‖ ^ 2 := by
  rw [sq, ← ContinuousLinearMap.norm_adjoint_comp_self, kernel_apply]

lemma norm_kerFun_eq_sqrt_norm_kernel (x) : ‖kerFun H x‖ = √‖kernel H x x‖ := by
  rw [norm_kernel_eq_norm_kerFun_sq, Real.sqrt_sq (norm_nonneg _)]

lemma norm_kernel_le (x y) : ‖kernel H x y‖ ≤ √‖kernel H x x‖ * √‖kernel H y y‖ := by
  grw [kernel_apply, opNorm_comp_le]
  simp [norm_kerFun_eq_sqrt_norm_kernel]

lemma norm_kernel_sq_le (x y) : ‖kernel H x y‖ ^ 2 ≤ ‖kernel H x x‖ * ‖kernel H y y‖ := by
  grw [norm_kernel_le]; simp [mul_pow]

variable {H} in
/-- The evaluation of an element `f` of a reproducing kernel Hilbert space at a point `x` is
bounded by `‖f‖` times the square root of the kernel diagonal `‖kernel H x x‖` at `x`. -/
lemma norm_apply_le (f : H) (x : X) : ‖f x‖ ≤ ‖f‖ * √‖kernel H x x‖ := by
  grw [← adjoint_kerFun, le_opNorm, norm_map, norm_kerFun_eq_sqrt_norm_kernel, mul_comm]

/-- The span of the kernel functions is dense. -/
theorem kerFun_dense : topologicalClosure (span 𝕜 {kerFun H x v | (x) (v)}) = ⊤ := by
  refine (orthogonal_eq_bot_iff.mp ((Submodule.eq_bot_iff _).mpr fun f fin ↦ DFunLike.ext f 0 ?_))
  refine fun x ↦ ext_inner_left 𝕜 fun v ↦ ?_
  simp only [← kerFun_inner, coe_zero, Pi.zero_apply, inner_zero_right]
  refine inner_right_of_mem_orthogonal (subset_closure ?_) fin
  simp [mem_span_of_mem]

lemma isHermitian_kernel : (kernel H).IsHermitian := by
  ext
  refine ext_inner_right 𝕜 fun w ↦ ?_
  simp only [Matrix.conjTranspose_apply, star, adjoint_inner_left,
    ← inner_conj_symm _ (kernel H _ _ _), kernel_inner, inner_conj_symm]

open scoped ComplexOrder in
/-- The kernel is a positive semidefinite matrix. -/
theorem posSemidef_kernel : (kernel H).PosSemidef := by
  refine ⟨isHermitian_kernel H, fun s ↦ (ContinuousLinearMap.isPositive_iff' _).2 ⟨?_, fun v ↦ ?_⟩⟩
  · rw [IsSelfAdjoint, sub_zero, star_finsuppSum, Finsupp.sum_comm]
    simp [← mul_assoc, (isHermitian_kernel H).apply]
  · simp [Finsupp.sum_apply'', Finsupp.sum_inner, star, adjoint_inner_left,
      kernel_inner, -inner_kerFun, -kerFun_inner]
    simp [← Finsupp.sum_inner, ← Finsupp.inner_sum, -kerFun_inner, -inner_kerFun]

/-!
## Construction of RKHS from kernel
-/

variable {H} {K : Matrix X X (V →L[𝕜] V)}

private lemma isSelfAdjoint_finsuppSum (h : K.IsHermitian) (f : X →₀ V →L[𝕜] V) :
    IsSelfAdjoint (f.sum fun i xi ↦ f.sum fun j xj ↦ star xi * K i j * xj) := by
  simp only [mul_assoc, isSelfAdjoint_iff, star_finsuppSum, Pi.star_apply, star_mul, h.apply,
    star_star]
  rw [Finsupp.sum_comm]

theorem posSemidef_tfae : List.TFAE [K.PosSemidef, K.IsHermitian ∧ ∀ (f : X × V →₀ 𝕜),
    0 ≤ RCLike.re (f.sum fun xv z ↦ f.sum fun xv' w ↦ conj z * w * ⟪K xv'.1 xv.1 xv.2, xv'.2⟫_𝕜),
    K.IsHermitian ∧ ∀ (vv : X →₀ V),
    0 ≤ RCLike.re (vv.sum fun x w ↦ vv.sum fun x' w' ↦ ⟪K x' x w, w'⟫_𝕜),
    ] := by
  have {h p1 p2 p3 : Prop} (htfae : h → List.TFAE [p1, p2, p3]) :
      List.TFAE [h ∧ p1, h ∧ p2, h ∧ p3] := by
    tfae_have 1 → 2 := fun ⟨h, t⟩ ↦ ⟨h, ((htfae h).out 0 1).mp t⟩
    tfae_have 2 → 3 := fun ⟨h, t⟩ ↦ ⟨h, ((htfae h).out 1 2).mp t⟩
    tfae_have 3 → 1 := fun ⟨h, t⟩ ↦ ⟨h, ((htfae h).out 2 0).mp t⟩
    tfae_finish
  refine this fun hHerm ↦ ?_
  simp only [nonneg_iff_isPositive, isPositive_def', isSelfAdjoint_finsuppSum hHerm,
    reApplyInnerSelf_apply, true_and]
  simp only [star_eq_adjoint, zero_apply, add_apply, implies_true, Finsupp.sum_apply'',
    FunLike.coe_mul_eq_comp, Function.comp_apply, Finsupp.sum_inner, adjoint_inner_left]
  -- FIXME: nontriviality should work here
  refine (subsingleton_or_nontrivial V).elim (fun h ↦ ?_) fun _ ↦ ?_
  · have : ∀ v : V, v = 0 := fun v ↦ Subsingleton.elim v 0
    simp [this]
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  tfae_have 1 → 2 := fun h ff ↦ by
    rw [Finsupp.sum_comm]
    convert! h (ff.sum fun xv z ↦ .single xv.1 ((z / ‖v‖ ^ 2) • (innerSL 𝕜 v).smulRight xv.2)) v
    simp [Finsupp.sum_sum_index, inner_add_right, inner_add_left, ← smul_assoc, hv]
    simp [inner_smul_left, inner_smul_right, ← mul_assoc, mul_comm]
  tfae_have 2 → 3 := fun h vv ↦ by
    simpa [add_mul, Finsupp.sum_sum_index] using (h (vv.sum fun x v ↦ .single ⟨x, v⟩ 1))
  tfae_have 3 → 1 := fun h ff v ↦ by
    rw [Finsupp.sum_comm]
    simpa [Finsupp.sum_sum_index, inner_add_right, inner_add_left] using
      h (ff.sum fun x T ↦ .single x (T v))
  tfae_finish

set_option linter.unusedVariables false in
/-- Auxiliary construction for `OfKernel`. TODO: Privatize -/
@[nolint unusedArguments]
abbrev H₀ (K : Matrix X X (V →L[𝕜] V)) := X × V →₀ 𝕜

variable [Fact K.PosSemidef]

instance instPreInnerProductSpaceCoreH₀ : PreInnerProductSpace.Core 𝕜 (H₀ K) where
  inner f g := f.sum fun ⟨y, u⟩ z ↦ g.sum fun ⟨x, v⟩ w ↦ star z * w * ⟪K x y u, v⟫_𝕜
  conj_inner_symm f g := by
    rw [Finsupp.sum_comm]
    simp only [map_finsuppSum]
    congr! 6
    rw [← (Fact.out : K.PosSemidef).isHermitian.apply]
    simp [star, adjoint_inner_right, mul_comm]
  add_left _ _ _ := by
    rw [Finsupp.sum_add_index'] <;> simp [← Finsupp.sum_add, add_mul]
  smul_left _ _ _ := by
    rw [Finsupp.sum_smul_index] <;> simp [Finsupp.mul_sum, ← mul_assoc]
  re_inner_nonneg := by
    have := (posSemidef_tfae.out 0 1).mp (Fact.out : K.PosSemidef)
    exact this.2

instance instSeminormedAddCommGroupH₀ : SeminormedAddCommGroup (H₀ K) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := 𝕜)

instance instInnerProductSpaceH₀ : InnerProductSpace 𝕜 (H₀ K) := .ofCore _

private lemma inner_H₀_def (f g : H₀ K) :
    ⟪f, g⟫_𝕜 = f.sum fun ⟨y, u⟩ z ↦ g.sum fun ⟨x, v⟩ w ↦ star z * w * ⟪K x y u, v⟫_𝕜 := rfl

variable (K) in
/-- The reproducing kernel Hilbert space generated by a positive semidefinite matrix.
TODO: Make nonexposed def once deriving is fixed. See
https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/backward.2EisDefEq.2ErespectTransparency/near/578850754 -/
abbrev OfKernel := UniformSpace.Completion (H₀ K)
--deriving SeminormedAddCommGroup, InnerProductSpace 𝕜, CompleteSpace

namespace OfKernel

private abbrev kerFunAux (x : X) : V →ₗ[𝕜] UniformSpace.Completion (H₀ K) where
  toFun v := .coe' (.single ⟨x, v⟩ 1)
  map_add' _ _ := by
    refine UniformSpace.Completion.denseRange_coe.eq_of_inner_left 𝕜 fun f ↦ ?_
    simp [inner_add_left, inner_H₀_def, ← Finsupp.sum_add, ← mul_add]
  map_smul' _ _ := by
    refine UniformSpace.Completion.denseRange_coe.eq_of_inner_left 𝕜 fun f ↦ ?_
    simp [inner_smul_left, inner_H₀_def, Finsupp.mul_sum, ← mul_assoc, mul_comm]

variable (K) in
/-- Explicit description of the kernel functions of `OfKernel K`.
This is marked as private because it equals `RKHS.kerFun`. However, it must be defined separately
since the `RKHS.kerFun` spelling depends on the `RKHS (OfKernel K)` instance, which itself
depends on `OfKernel.kerFun`. -/
private abbrev kerFun (x : X) :
    V →L[𝕜] UniformSpace.Completion (H₀ K) := (kerFunAux x).mkContinuous √‖K x x‖ fun v ↦ by
  refine (sq_le_sq₀ (by simp) (by simp [mul_nonneg])).mp ?_
  simp only [LinearMap.coe_mk, AddHom.coe_mk, UniformSpace.Completion.norm_coe,
    ← inner_self_eq_norm_sq (𝕜 := 𝕜), inner_self_re_eq_norm]
  simp only [inner_H₀_def, RCLike.star_def, mul_zero, zero_mul,
    Finsupp.sum_single_index, mul_one, map_zero, map_one, one_mul]
  calc
    _ ≤ ‖K x x v‖ * ‖v‖ := by simp [norm_inner_le_norm]
    _ ≤ ‖K x x‖ * ‖v‖ * ‖v‖ := by simp [mul_le_mul_of_nonneg_right, le_opNorm]
    _ ≤ _ := by simp [mul_pow, mul_assoc, ← sq]

@[no_expose]
instance instRKHS : RKHS 𝕜 (OfKernel K) X V where
  coeCLM := .pi fun x ↦ (OfKernel.kerFun K x).adjoint
  coeCLM_injective := by
    refine (injective_iff_map_eq_zero _).mpr fun f h ↦ ?_
    refine UniformSpace.Completion.denseRange_coe.eq_zero_of_inner_right 𝕜 fun ff ↦ ?_
    induction ff using Finsupp.induction with
    | zero =>
      have : @UniformSpace.Completion.coe' (H₀ K) PseudoMetricSpace.toUniformSpace 0 = 0 := rfl
      simp [this]
    | single_add i a =>
    simp only [UniformSpace.Completion.coe_add, inner_add_left, *, add_zero]
    rw [← UniformSpace.Completion.coe_toComplL (𝕜 := 𝕜)]
    have := (ext_iff_inner_left 𝕜).mp (congrFun h i.1) i.2
    have := by simpa [OfKernel.kerFun, adjoint_inner_right] using this
    rw [← mul_zero (conj a), ← this, ← inner_smul_left]
    refine (ext_iff_inner_right 𝕜).mp ?_ f
    simp [← UniformSpace.Completion.coe_toComplL (𝕜 := 𝕜),
      ← map_smul, -SeparationQuotient.mkCLM_apply, -UniformSpace.Completion.coe_toComplL]

/-- The kernel of the reproducing kernel Hilbert space
generated by a positive semidefinite matrix is the original positive semidefinite matrix.
-/
@[simp]
theorem kernel_ofKernel : kernel (OfKernel K) = K := by
  ext x y v
  refine ext_inner_right 𝕜 fun w ↦ ?_
  simp [kernel, adjoint_inner_left, -inner_kerFun, -kerFun_inner,
    coeCLM, OfKernel.kerFun, inner_H₀_def, RKHS.kerFun]

end OfKernel

section Mercer

open MeasureTheory

variable [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (μ : Measure X) [IsFiniteMeasure μ]

section attempt1

local instance : NormedSpace ℝ V := NormedSpace.restrictScalars ℝ 𝕜 V

variable (K) in
private noncomputable def integralOperatorAux (f : Lp V 2 μ) : X → V :=
  fun x => ∫ y, K x y (f y) ∂μ

omit [CompleteSpace V] [Fact K.PosSemidef] [BorelSpace X] in
private lemma integralOperatorAux_eLpNorm_le
    (hK : MemLp (fun p : X × X => K p.1 p.2) 2 (μ.prod μ)) (f : Lp V 2 μ) :
    AEStronglyMeasurable (integralOperatorAux K μ f) μ ∧
      eLpNorm (integralOperatorAux K μ f) 2 μ
        ≤ eLpNorm (fun p : X × X => K p.1 p.2) 2 (μ.prod μ) * eLpNorm f 2 μ := by
  unfold integralOperatorAux
  constructor
  · exact AEStronglyMeasurable.integral_prod_right'
      (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
        (hK.aestronglyMeasurable.prodMk ((Lp.aestronglyMeasurable f).comp_snd (μ:=μ))))
  · grw [eLpNorm_eq_lintegral_rpow_enorm_toReal (Ne.symm (NeZero.ne' 2)) ENNReal.ofNat_ne_top, enorm_integral_le_lintegral_enorm, le_opENorm]
    have hK_slice : ∀ᵐ x ∂μ, AEMeasurable (fun y ↦ ‖K x y‖ₑ) μ :=
      hK.aestronglyMeasurable.prodMk_left.mono (fun x hx => hx.enorm)
    have h' : ∀ᵐ x ∂μ,
        ∫⁻ y, ‖K x y‖ₑ * ‖f y‖ₑ ∂μ
          ≤ (∫⁻ y, ‖K x y‖ₑ ^ 2 ∂μ) ^ (2 : ℝ)⁻¹ * (∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ) ^ (2 : ℝ)⁻¹ := by
      filter_upwards [hK_slice] with x hx
      simpa using ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
        (f := fun y => ‖K x y‖ₑ) hx (Lp.aestronglyMeasurable f).enorm
    calc
       (∫⁻ (x : X), (∫⁻ (a : X), ‖K x a‖ₑ * ‖f a‖ₑ ∂μ) ^ (2:ℝ) ∂μ) ^ (1 / (2:ℝ))
          = (∫⁻ (x : X), (∫⁻ (a : X), ‖K x a‖ₑ * ‖f a‖ₑ ∂μ) ^ 2 ∂μ) ^ (2:ℝ)⁻¹ := by
        simp
       _ ≤ (∫⁻ (a : X), ((∫⁻ (y : X), ‖K a y‖ₑ ^ 2 ∂μ) ^ (2:ℝ)⁻¹
          * (∫⁻ (y : X), ‖f y‖ₑ ^ 2 ∂μ) ^ (2:ℝ)⁻¹) ^ 2 ∂μ) ^ (2:ℝ)⁻¹ := by
        grw [lintegral_mono_ae (h'.mono fun x hx => ENNReal.pow_le_pow_left (n:=2) hx)]
       _ = (∫⁻ (a : X), (∫⁻ (y : X), ‖K a y‖ₑ ^ 2 ∂μ)
          * (∫⁻ (y : X), ‖f y‖ₑ ^ 2 ∂μ) ∂μ) ^ (2:ℝ)⁻¹ := by
        have h : ∀ᵐ x ∂μ, ((∫⁻ (y : X), ‖K x y‖ₑ ^ 2 ∂μ) ^ (2:ℝ)⁻¹
            * (∫⁻ (y : X), ‖f y‖ₑ ^ 2 ∂μ) ^ (2:ℝ)⁻¹) ^ 2
            = (∫⁻ (y : X), ‖K x y‖ₑ ^ 2 ∂μ) * ∫⁻ (y : X), ‖f y‖ₑ ^ 2 ∂μ := by
          apply ae_of_all
          intro x
          simp_rw [mul_pow, ← ENNReal.rpow_mul_natCast _ 2⁻¹ 2]
          simp
        rw [lintegral_congr_ae (h.mono fun x hx => hx)]
       _ = (∫⁻ (a : X), (∫⁻ (y : X), ‖K a y‖ₑ ^ 2 ∂μ) ∂μ) ^ (2:ℝ)⁻¹
          * (∫⁻ (y : X), ‖f y‖ₑ ^ 2 ∂μ) ^ (2:ℝ)⁻¹ := by
        rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), lintegral_mul_const'']
        exact (hK.aestronglyMeasurable.enorm.pow_const 2).lintegral_prod_right'
       _ ≤ eLpNorm (fun p ↦ K p.1 p.2) 2 (μ.prod μ) * eLpNorm (↑↑f) 2 μ := by
        have h1 := eLpNorm_nnreal_eq_lintegral (μ:=μ.prod μ) (f:=(fun p ↦ ‖K p.1 p.2‖ₑ)) (by exact two_ne_zero)
        have h2 := eLpNorm_nnreal_eq_lintegral (μ:=μ) (f:=f) (by exact two_ne_zero)
        simp at h1 h2
        rw [h1, ← h2]
        rcases eq_or_ne (eLpNorm (↑↑f) 2 μ) 0 with hf0 | hf0
        · simp [hf0]
        rw [ENNReal.mul_le_mul_iff_left hf0 (Lp.eLpNorm_ne_top f),
          ← lintegral_prod _ (hK.aestronglyMeasurable.enorm.pow_const 2)]

private lemma integralOperatorAux_integrable_ae
    (hK : MemLp (fun p : X × X => K p.1 p.2) 2 (μ.prod μ)) (f : Lp V 2 μ) :
    ∀ᵐ x ∂μ, Integrable (fun y => K x y (f y)) μ := by sorry

variable [SMulCommClass ℝ 𝕜 V]

-- The integral operator as a continuous linear map from L^2 to L^2
def integralOperator' (hK : MemLp (fun ((x, y) : X × X) ↦ K x y) 2 (μ.prod μ)) :
    Lp V 2 μ →L[𝕜] Lp V 2 μ :=
  LinearMap.mkContinuous
    { toFun f := MemLp.toLp (fun x => ∫ y, K x y (f y) ∂μ)
        ⟨(integralOperatorAux_eLpNorm_le μ hK f).1,
          (lt_of_le_of_lt (integralOperatorAux_eLpNorm_le μ hK f).2
            (ENNReal.mul_lt_top hK.eLpNorm_lt_top (Lp.memLp f).eLpNorm_lt_top))⟩
      map_add' f g := by
        have hf_int := integralOperatorAux_integrable_ae μ hK f
        have hg_int := integralOperatorAux_integrable_ae μ hK g
        have hfg := Lp.coeFn_add f g
        simp only [← MemLp.toLp_add, Pi.add_def, MemLp.toLp_eq_toLp_iff]
        filter_upwards [hf_int, hg_int] with x hxf hxg
        have hcong : (fun y => K x y ((f + g) y)) =ᵐ[μ] fun y => K x y (f y) + K x y (g y) :=
          hfg.mono fun y hy => by simp_rw [hy]; simp [map_add]
        simp_rw [integral_congr_ae hcong, integral_add hxf hxg]
      map_smul' c f := by
        have hcf := Lp.coeFn_smul c f
        simp only [← MemLp.toLp_const_smul, RingHom.id_apply, MemLp.toLp_eq_toLp_iff]
        refine ae_of_all μ fun x => ?_
        have hcong : (fun y => K x y ((c • f) y)) =ᵐ[μ] fun y => c • K x y (f y) :=
          hcf.mono fun y hy => by simp_rw [hy]; simp [map_smul]
        simp_rw [integral_congr_ae hcong, Pi.smul_apply, integral_smul]
    }
    (eLpNorm (fun p : X × X => K p.1 p.2) 2 (μ.prod μ)).toReal
    (fun f ↦ by
      have h := (integralOperatorAux_eLpNorm_le μ hK f).2
      unfold integralOperatorAux at h
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp, ge_iff_le]
      grw [h, ENNReal.toReal_mul, ← Lp.norm_def f]
      rw [← lt_top_iff_ne_top]
      refine ENNReal.mul_lt_top hK.2 f.2
    )

end attempt1

section attempt2

variable (hK : MemLp (fun p : X × X => K p.1 p.2) 2 (μ.prod μ)) [MeasurableSpace V]

def mercerForm : Lp V 2 μ →L⋆[𝕜] Lp V 2 μ →L[𝕜] 𝕜 := LinearMap.mkContinuous₂
  (LinearMap.mk₂'ₛₗ (starRingEnd 𝕜) (RingHom.id 𝕜)
    (fun (f : Lp V 2 μ) (g : Lp V 2 μ) ↦ ∫ p : X × X, ⟪K p.1 p.2 (f p.2), (g p.1)⟫_𝕜 ∂ (μ.prod μ))
    (fun f₁ f₂ g ↦ by
      simp_rw [← integral_add (by sorry) (by sorry), ← inner_add_left, ← map_add]
      have hf : ∀ᵐ p ∂(μ.prod μ), (f₁ + f₂) p.2 = f₁ p.2 + f₂ p.2 := by
        rw [Measure.ae_prod_iff_ae_ae (by sorry), Measure.ae_ae_comm (by sorry)]
        filter_upwards [Lp.coeFn_add f₁ f₂] with p hp
        exact ae_of_all μ fun a ↦ hp
      apply integral_congr_ae
      filter_upwards [hf] with p hf
      rw [hf]
    )
    (fun c f g ↦ by
      simp_rw [← integral_smul, ← inner_smul_left_eq_star_smul, ← map_smul]
      have hf : ∀ᵐ p ∂(μ.prod μ), (c • f) p.2 = c • f p.2 := by
        rw [Measure.ae_prod_iff_ae_ae (by sorry), Measure.ae_ae_comm (by sorry)]
        filter_upwards [Lp.coeFn_smul c f] with p hp
        exact ae_of_all μ fun a ↦ hp
      apply integral_congr_ae
      filter_upwards [hf] with p hf
      rw [hf]
    )
    (fun f g₁ g₂ ↦ by
      rw [← integral_add (by sorry) (by sorry)]
      simp_rw [← inner_add_right]
      have hf : ∀ᵐ p ∂(μ.prod μ), (g₁ + g₂) p.1 = g₁ p.1 + g₂ p.1 := by
        rw [Measure.ae_prod_iff_ae_ae (by sorry)]
        filter_upwards [Lp.coeFn_add g₁ g₂] with p hp
        exact ae_of_all μ fun a ↦ hp
      apply integral_congr_ae
      filter_upwards [hf] with p hf
      rw [hf]
    )
    (fun c f g ↦ by
      simp_rw [← integral_smul, ← inner_smul_right_eq_smul, RingHom.id_apply]
      have hf : ∀ᵐ p ∂(μ.prod μ), (c • g) p.1 = c • g p.1 := by
        rw [Measure.ae_prod_iff_ae_ae (by sorry)]
        filter_upwards [Lp.coeFn_smul c g] with p hp
        exact ae_of_all μ fun a ↦ hp
      apply integral_congr_ae
      filter_upwards [hf] with p hf
      rw [hf]
    )
  )
  (eLpNorm (fun p : X × X => K p.1 p.2) 2 (μ.prod μ)).toReal
  (fun f g ↦ by
    simp
    have := hK
    grw [norm_integral_le_lintegral_norm, norm_inner_le_norm, le_opNorm]
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (Ne.symm (NeZero.ne' 2)) (ENNReal.ofNat_ne_top)]
    simp_rw [mul_assoc]
-- , ENNReal.ofReal_mul (norm_nonneg)
    sorry
    sorry
    sorry)

def integralOperator : Lp V 2 μ →L[𝕜] Lp V 2 μ := LinearMap.mkContinuous
  {
    toFun := fun (f : Lp V 2 μ) ↦ (InnerProductSpace.toDual 𝕜 (Lp V 2 μ)).symm (mercerForm μ hK f)
    map_add' f g := by ext; simp
    map_smul' c f := by simp [ContinuousLinearMap.map_smulₛₗ, LinearIsometryEquiv.map_smulₛₗ]
  }
  (eLpNorm (fun p : X × X => K p.1 p.2) 2 (μ.prod μ)).toReal
  (fun f ↦ by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, norm_map]
    unfold mercerForm
    grw [le_opNorm, LinearMap.mkContinuous₂_norm_le]
    exact ENNReal.toReal_nonneg
  )

end attempt2

end Mercer

end RKHS
