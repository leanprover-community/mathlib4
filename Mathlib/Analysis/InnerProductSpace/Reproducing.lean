/-
Copyright (c) 2026 Hampus Nyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hampus Nyberg, Yaël Dillies
-/
module

public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.Normed.Operator.Extend

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
  coe_injective' := coeCLM_injective

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
  simp only [star_eq_adjoint, zero_apply, add_apply, implies_true, Finsupp.sum_apply'', coe_mul',
    Function.comp_apply, Finsupp.sum_inner, adjoint_inner_left]
  -- FIXME: nontriviality should work here
  refine (subsingleton_or_nontrivial V).elim (fun h ↦ ?_) fun _ ↦ ?_
  · have : ∀ v : V, v = 0 := fun v ↦ Subsingleton.elim v 0
    simp [this]
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  tfae_have 1 → 2 := fun h ff ↦ by
    rw [Finsupp.sum_comm]
    convert h (ff.sum fun xv z ↦ .single xv.1
      ((z / ‖v‖ ^ 2) • (innerSL 𝕜 v).smulRight xv.2)) v
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

variable (𝕜) in
def outerKernel (f : X → V) : Matrix X X (V →L[𝕜] V) :=
  Matrix.of fun x y ↦ InnerProductSpace.rankOne 𝕜 (f x) (f y)

omit [CompleteSpace V] in
variable (𝕜) in
@[simp]
lemma outerKernel_def (f : X → V) (x y) :
    (outerKernel 𝕜 f) x y = InnerProductSpace.rankOne 𝕜 (f x) (f y) :=
  coe_inj.mp rfl

omit [CompleteSpace V] in
variable (𝕜) in
@[simp]
lemma outerKernel_apply (f : X → V) (xv₁ xv₂ : X × V) :
    ⟪ (outerKernel 𝕜 f xv₂.1 xv₁.1) xv₁.2, xv₂.2 ⟫_𝕜
    = (starRingEnd 𝕜) ⟪ f xv₁.1, xv₁.2⟫_𝕜 * ⟪ f xv₂.1, xv₂.2⟫_𝕜 := by
  simp_rw [outerKernel_def, rankOne_apply, inner_smul_left]

variable (𝕜) in
lemma outerKernel_posSemidef (f : X → V) : (outerKernel 𝕜 f).PosSemidef := by
  apply ((posSemidef_tfae (K := outerKernel 𝕜 f)).out 0 2).mpr
  refine ⟨?_, fun x ↦ ?_⟩
  · ext
    simp_rw [Matrix.conjTranspose_apply, outerKernel_def, star_eq_adjoint,
      InnerProductSpace.adjoint_rankOne]
  · simp_rw [outerKernel_def, rankOne_apply, inner_smul_left, Finsupp.sum, <-Finset.mul_sum,
      <-Finset.sum_mul, ← map_sum, RCLike.conj_mul]
    simp

lemma posSemidef_of_mem (f : H) : ((‖f‖ : 𝕜) ^ 2 • kernel H - outerKernel 𝕜 f).PosSemidef := by
  apply ((posSemidef_tfae (K := (‖f‖ : 𝕜) ^ 2 • kernel H - outerKernel 𝕜 f)).out 0 2).mpr
  refine ⟨((posSemidef_kernel H).1.smul
    (by rw [← RCLike.im_eq_zero_iff_isSelfAdjoint, RCLike.im_ofReal_pow])).sub
    (outerKernel_posSemidef 𝕜 f).1, fun x ↦ ?_⟩
  simp_rw [Matrix.sub_apply, Matrix.smul_apply, outerKernel_def, coe_sub', coe_smul',
    Pi.sub_apply, Pi.smul_apply, rankOne_apply, inner_sub_left, Finsupp.sum,
    Finset.sum_sub_distrib, map_sub, map_sum, sub_nonneg, inner_smul_left, ← inner_kerFun,
    kernel_inner, ← map_sum, ← Finset.mul_sum, ← Finset.sum_mul, ← map_sum, ← inner_sum,
    ← sum_inner, inner_self_eq_norm_sq_to_K, RCLike.conj_mul, RCLike.re_ofReal_pow, map_pow,
    RCLike.conj_ofReal, RCLike.mul_re, RCLike.im_ofReal_pow, mul_zero, sub_zero,
    RCLike.re_ofReal_pow, ← mul_pow]
  grw [norm_inner_le_norm]

lemma mem_of_posSemidef (f : X → V) {c : ℝ}
    (hc : ((c : 𝕜) ^ 2 • kernel H - outerKernel 𝕜 f).PosSemidef) : ∃ (g : H), (g : X → V) = f := by
  let Laux : (X × V →₀ 𝕜) →ₗ[𝕜] 𝕜 := Finsupp.linearCombination 𝕜 (fun xv => ⟪f xv.1, xv.2⟫_𝕜)
  let toSpan : (X × V →₀ 𝕜) →ₗ[𝕜] H := Finsupp.linearCombination 𝕜 (fun xv => kerFun H xv.1 xv.2)
  let toSpan' : (X × V →₀ 𝕜) →ₗ[𝕜] ↥(span 𝕜 {kerFun H x v | (x : X) (v : V)}) :=
    Finsupp.linearCombination 𝕜 (fun xv => ⟨kerFun H xv.1 xv.2, subset_span ⟨xv.1, xv.2, rfl⟩⟩)
  have h_ineq (φ : X × V →₀ 𝕜) : ‖Laux φ‖ ^2 ≤ c ^2 * ‖toSpan φ‖^2 := by
    apply ((posSemidef_tfae (K := (c : 𝕜) ^ 2 • kernel H - outerKernel 𝕜 f)).out 0 1).mp at hc
    simp_rw [Laux, toSpan, Finsupp.linearCombination_apply, Finsupp.sum,
      ← inner_self_eq_norm_sq (𝕜:=𝕜), ←RCLike.re_ofReal_mul]
    rw [← RCLike.conj_ofReal ((c ^ 2))]
    simp_rw [map_pow _ c 2]
    rw [← le_add_neg_iff_le]
    simp_rw [← AddMonoidHom.map_add_neg, ← sub_eq_add_neg, sum_inner, inner_sum, inner_smul_right,
      inner_smul_left, Finset.mul_sum, <-kernel_inner, RCLike.inner_apply', ← outerKernel_apply,
      ← Finset.sum_sub_distrib, mul_comm, mul_left_comm, ← mul_assoc, mul_comm,
      ← mul_sub_left_distrib, ← mul_sub_right_distrib, mul_comm ⟪(kernel H _ _) _, _⟫_𝕜  _,
      ← inner_smul_left, ← inner_sub_left, mul_comm _ (φ _), ← mul_assoc, ← smul_apply, ← sub_apply,
      ← Pi.smul_apply, ← Pi.sub_apply]
    exact hc.2 φ
  have hrange : span 𝕜 {kerFun H x v | (x : X) (v : V)} ≤ toSpan.range := by
    rw [Finsupp.range_linearCombination 𝕜]
    exact Submodule.span_mono fun _ ⟨x, v, h⟩ => ⟨⟨x, v⟩, h⟩
  let L_lin : ↥(span 𝕜 {kerFun H x v | (x : X) (v : V)}) →ₗ[𝕜] 𝕜 :=
    (toSpan.ker.liftQ Laux (fun φ hφ ↦ by have h := h_ineq φ; rw [hφ, norm_zero] at h; simp_all))
      |>.comp toSpan.quotKerEquivRange.symm.toLinearMap
      |>.comp (Submodule.inclusion hrange)
  have hL : L_lin.comp toSpan' = Laux := by
    apply Finsupp.lhom_ext
    intro ⟨x, v⟩ r
    simp only [LinearMap.comp_apply, toSpan', Finsupp.linearCombination_single,
               map_smul, Laux, Finsupp.linearCombination_single]
    congr 1
    have h1 : Submodule.inclusion hrange ⟨kerFun H x v, subset_span ⟨x, v, rfl⟩⟩ =
        (⟨toSpan (Finsupp.single (x, v) 1), LinearMap.mem_range_self _ _⟩ : toSpan.range) :=
      Subtype.ext (by simp [toSpan, Finsupp.linearCombination_single])
    have h2 : toSpan.quotKerEquivRange.symm ⟨toSpan _, LinearMap.mem_range_self _ _⟩ =
        Submodule.Quotient.mk (Finsupp.single (x, v) 1) :=
      (LinearEquiv.symm_apply_eq toSpan.quotKerEquivRange).mpr rfl
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, L_lin]
    simp_rw [h1, h2, Submodule.liftQ_apply, Laux, Finsupp.linearCombination_single, one_smul]
  let L : ↥(span 𝕜 {kerFun H x v | (x : X) (v : V)}) →L[𝕜] 𝕜 := L_lin.mkContinuous ‖c‖ (fun ξ ↦ by
    obtain ⟨y, hy⟩ := hrange ξ.2
    have hcomp : (Submodule.subtype _).comp toSpan' = toSpan :=
      Finsupp.lhom_ext fun ⟨a, v⟩ r ↦ by
        simp [toSpan, toSpan', Finsupp.linearCombination_single]
    have hξ : toSpan' y = ξ := Subtype.ext (LinearMap.congr_fun hcomp y |>.trans hy)
    calc ‖L_lin ξ‖
        = ‖Laux y‖          := by
          rw [← hξ, ← LinearMap.comp_apply, LinearMap.congr_fun hL _]
      _ ≤ ‖c‖ * ‖toSpan y‖  := by
          rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), mul_pow, Real.norm_eq_abs, sq_abs]
          exact h_ineq y
      _ = ‖c‖ * ‖ξ‖         := by rw [hy, ← hξ, Submodule.norm_coe]
  )
  let K := (span 𝕜 {kerFun H x v | (x : X) (v : V)}).subtypeL
  refine ⟨(InnerProductSpace.toDual 𝕜 H).symm (L.extend K), ?_⟩
  ext x
  apply ext_inner_left 𝕜
  intro v
  rw [← kerFun_inner, ← inner_conj_symm, toDual_symm_apply,
    show kerFun H x v = K (toSpan' (Finsupp.single (x, v) 1)) from
      (by simp [toSpan', Finsupp.linearCombination_single]; rfl),
    ContinuousLinearMap.extend_eq _ (by rw [DenseRange, dense_iff_closure_eq,
      show Set.range K = ↑(span 𝕜 {kerFun H x v | (x : X) (v : V)}) from Subtype.range_coe_subtype,
      ← topologicalClosure_coe, kerFun_dense, top_coe]) ({ comap_uniformity := rfl }) _,
    ← inner_conj_symm]
  apply RingHom.congr_arg (starRingEnd 𝕜)
  rw [LinearMap.mkContinuous_apply, ← LinearMap.comp_apply, LinearMap.congr_fun hL _,
    Finsupp.linearCombination_single]
  simp

theorem mem_iff (f : X → V) : (∃ (g : H), (g : X → V) = f) ↔
    ∃ (c : ℝ), 0 ≤ c ∧ ((c : 𝕜)^2 • kernel H - outerKernel 𝕜 f).PosSemidef :=
  ⟨fun ⟨g, hg⟩ => ⟨‖g‖, norm_nonneg _, hg ▸ posSemidef_of_mem g⟩,
   fun ⟨_, _, hc⟩ => mem_of_posSemidef f hc⟩
