/-
Copyright (c) 2026 Hampus Nyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hampus Nyberg, Yaël Dillies
-/
module

public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Data.Set.Operations

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

variable (H) in
/-- Point evaluation `fun f ↦ f x` formed using the projection `(X→V)→L[𝕜] V`,`(x,f x)↦ f x` after
the coercion `H→L[𝕜] (X→V)`. -/
def eval (x : X) : H →L[𝕜] V := .proj x ∘L coeCLM 𝕜

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

section Sum

variable {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
variable [RKHS 𝕜 H₁ X V]
omit [CompleteSpace H] [CompleteSpace V]

variable (H H₁) in
/-- The operator `(f,g) ↦ ↑f + ↑f`, where addition is in `X→V`. -/
def generator : WithLp 2 (H × H₁) →L[𝕜] (X → V) :=
  ((coeCLM (H:=H) 𝕜).coprod (coeCLM (H:=H₁) 𝕜)) ∘L
    (WithLp.prodContinuousLinearEquiv 2 𝕜 H H₁).toContinuousLinearMap

variable (H H₁) in
@[simp]
lemma generator_apply (f : H) (g : H₁) (x : X) :
    generator H H₁ (WithLp.toLp 2 (f,g)) x = f x + g x := by
  simp [generator]

instance : IsClosed ((generator H H₁).ker : Set (WithLp 2 (H × H₁))) :=
  (generator H H₁).isClosed_ker

-- ROUTE 2:

variable (H H₁) in
abbrev Sum' := WithLp 2 (H × H₁) ⧸ (generator H H₁).ker

variable [CompleteSpace H] [CompleteSpace H₁] [CompleteSpace V] in
instance : RKHS 𝕜 (Sum' H H₁) X V where
  coeCLM := {
    toLinearMap := (generator H H₁).ker.liftQ (generator H H₁).toLinearMap (le_refl _)
    cont := Continuous.quotient_lift (generator H H₁).continuous
      (fun a b hab => by
        have hker : -a + b ∈ (generator H H₁).ker := QuotientAddGroup.leftRel_apply.mp hab
        simp only [LinearMap.mem_ker, coe_coe, map_add, map_neg] at hker
        rw [← neg_add_eq_zero]
        exact hker) }
  coeCLM_injective := fun f g hfg => by
    have hinj : Function.Injective
        ((generator H H₁).ker.liftQ (generator H H₁).toLinearMap (le_refl _)) := by
      rw [← LinearMap.ker_eq_bot]
      exact Submodule.ker_liftQ_eq_bot _ _ (le_refl _) (le_refl _)
    exact hinj hfg

/-- The RKHS generator with its range restricted to the RKHS. -/
def generatorRestricted : WithLp 2 (H × H₁) →L[𝕜] Sum' H H₁ :=
  ((generator H H₁).ker.mkQ).mkContinuous 1
    (fun x => by rw [one_mul]; exact Submodule.Quotient.norm_mk_le _ x)

variable (𝕜 H H₁) in
variable [CompleteSpace H] [CompleteSpace H₁] in
@[simp]
lemma generatorRestricted_def (f : WithLp 2 (H × H₁)) :
    generatorRestricted f = (generator H H₁) f := by
  rw [generatorRestricted]
  rfl

variable (𝕜 H H₁) in
/-- Embedding of `H` into the RKHS `Sum' H H₁` -/
def coeL' : H →L[𝕜] (Sum' H H₁) := generatorRestricted
  ∘L (WithLp.prodContinuousLinearEquiv 2 𝕜 H H₁).symm.toContinuousLinearMap
  ∘L ContinuousLinearMap.prod (ContinuousLinearMap.id 𝕜 H) 0

variable (𝕜 H H₁) in
/-- Embedding of `H₁` into the RKHS `Sum' H H₁` -/
def coeR' : H₁ →L[𝕜] (Sum' H H₁) := generatorRestricted
  ∘L (WithLp.prodContinuousLinearEquiv 2 𝕜 H H₁).symm.toContinuousLinearMap
  ∘L ContinuousLinearMap.prod 0 (ContinuousLinearMap.id 𝕜 H₁)

variable (𝕜 H H₁) in
variable [CompleteSpace H] [CompleteSpace H₁] in
@[simp]
lemma coeL'_apply (f : H) (x : X) : (coeL' 𝕜 H H₁) f x = f x := by simp [coeL']

variable (𝕜 H H₁) in
variable [CompleteSpace H] [CompleteSpace H₁] in
@[simp]
lemma coeR'_apply (f : H₁) (x : X) : (coeR' 𝕜 H H₁) f x = f x := by simp [coeR']

variable [CompleteSpace H] [CompleteSpace H₁] [CompleteSpace V] in
lemma adjoint_coeL_add_adjoint_coeR_eq (f : Sum' H H₁) (x : X) :
    (adjoint (coeL' 𝕜 H H₁) f) x + (adjoint (coeR' 𝕜 H H₁) f) x = f x := by
  rw [ext_iff_inner_left (𝕜 := 𝕜)]
  intro v
  rw [inner_add_right]
  simp_rw [← kerFun_inner, adjoint_inner_right]
  rw [kerFun_inner x v f]

variable [CompleteSpace H] [CompleteSpace H₁] [CompleteSpace V] in
theorem kerFun_sum_eq_sum_of_kerFun' (x : X) :
    kerFun (Sum' H H₁) x = (coeL' 𝕜 H H₁) ∘L kerFun H x + (coeR' 𝕜 H H₁) ∘L kerFun H₁ x := by
  apply ContinuousLinearMap.ext
  intro v
  -- ext
  -- simp
  -- rw [coeL'_apply, coeR'_apply]
  rw [ext_iff_inner_left (𝕜 := 𝕜)]
  intro f
  obtain ⟨⟨p1,p2⟩ , hp⟩ := Quotient.exists_rep f
  have hs : p1 x + p2 x = f x := by sorry
  simp
  rw [← hs]
  rw [inner_add_right, ← adjoint_inner_left, inner_kerFun, ← adjoint_inner_left, inner_kerFun]
  -- rw [show (Submodule.Quotient.mk (WithLp.toLp 2 (p1, p2))) x = ↑(generator H H₁) (WithLp.toLp 2 (p1, p2)) x from rfl]
  rw [← adjoint_coeL_add_adjoint_coeR_eq, inner_add_left]

variable [CompleteSpace H] [CompleteSpace H₁] [CompleteSpace V] in
theorem kernel_sum_eq_sum_of_kernel : kernel (Sum' H H₁) = kernel H + kernel H₁ := by
  ext
  rw [Matrix.add_apply, add_apply]
  simp_rw [← kerFun_apply]
  rw [kerFun_sum_eq_sum_of_kerFun']
  simp

-- ROUTE 1:


variable (H H₁) in
abbrev Sum := (generator H H₁).range

/-- Norm on `Sum H H₁` by pulling back to the quotient. -/
instance : NormedAddCommGroup (Sum H H₁) :=
  NormedAddCommGroup.induced
    (Sum H H₁)
    (WithLp 2 (H × H₁) ⧸ (generator H H₁).ker)
    (generator H H₁).quotKerEquivRange.symm.toLinearMap
    (generator H H₁).quotKerEquivRange.symm.injective

/-- `Sum H H₁` comes equipped with the weaker subtype topology. This overrides it by the topology
induced by the norm. -/
instance : TopologicalSpace (Sum H H₁) := PseudoMetricSpace.toUniformSpace.toTopologicalSpace
instance : UniformSpace (Sum H H₁) := PseudoMetricSpace.toUniformSpace

variable (H H₁) in
private def evalLp2CLM (x : X) : WithLp 2 (H × H₁) →L[𝕜] V :=
  (eval H x).coprod (eval H₁ x) ∘L WithLp.prodContinuousLinearEquiv 2 𝕜 H H₁

@[simp]
private lemma evalLp2CLM_apply (x : X) (f : WithLp 2 (H × H₁)) :
    evalLp2CLM H H₁ x f = f.fst x + f.snd x := rfl

variable (H H₁) in
private lemma gen_ker_le_eval_ker (x : X) : (generator H H₁).ker ≤ (evalLp2CLM H H₁ x).ker := by
  rintro f hf
  simp_rw [LinearMap.mem_ker, funext_iff, coe_coe, Pi.zero_apply] at hf
  simp_rw [LinearMap.mem_ker, coe_coe, evalLp2CLM_apply]
  exact hf x

variable (H H₁) in
private def evalQCLM (x : X) : (WithLp 2 (H × H₁) ⧸ (generator H H₁).ker) →L[𝕜] V :=
  ⟨(generator H H₁).ker.liftQ (evalLp2CLM H H₁ x) (gen_ker_le_eval_ker H H₁ x),
    Continuous.quotient_lift ((evalLp2CLM H H₁ x).continuous)
  (by
    rintro f g hfg
    have heq := gen_ker_le_eval_ker H H₁ x
      ((generator H H₁).ker.neg_mem (QuotientAddGroup.leftRel_apply.mp hfg))
    simp_rw [neg_add', neg_neg, LinearMap.mem_ker, coe_coe, map_sub, evalLp2CLM_apply, sub_eq_zero] at heq
    simp_rw [evalLp2CLM_apply]
    exact heq
  )⟩

variable (H H₁) in
private def evalCLM_aux (x : X) : (Sum H H₁) →L[𝕜] V :=
  (evalQCLM H H₁ x) ∘L ((generator H H₁).quotKerEquivRange.symm.mkContinuous 1
    (fun q ↦ by simp_rw [LinearEquiv.coe_coe, one_mul]; exact le_refl _))

private lemma evalCLM_aux_apply (x : X) (f : Sum H H₁) :
    evalCLM_aux H H₁ x f = (f : X→V) x := by
  obtain ⟨p, hp⟩ := LinearMap.mem_range.mp f.2
  have hq : (generator H H₁).quotKerEquivRange.symm f = Submodule.Quotient.mk p := by
    rw [LinearEquiv.symm_apply_eq, ← SetLike.coe_eq_coe, ← hp, coe_coe,
      LinearMap.quotKerEquivRange_apply_mk]
    rfl
  simp [evalCLM_aux, evalQCLM, ← hp, hq]
  rfl

private lemma piEval_eq_subtype : (ContinuousLinearMap.pi fun x ↦ evalCLM_aux H H₁ x) =
    (Sum H H₁).subtype := by
  ext
  simp only [ContinuousLinearMap.coe_pi, LinearMap.pi_apply, coe_coe, evalCLM_aux_apply,
    subtype_apply]

variable [CompleteSpace H] [CompleteSpace H₁] [CompleteSpace V]

instance : InnerProductSpace 𝕜 (Sum H H₁) :=
  InnerProductSpace.induced (generator H H₁).quotKerEquivRange.symm.toLinearMap

instance : RKHS 𝕜 (Sum H H₁) X V where
  coeCLM := ⟨(Sum H H₁).subtype, by
    rw [← piEval_eq_subtype]
    exact (ContinuousLinearMap.pi fun x ↦ evalCLM_aux H H₁ x).cont
  ⟩
  coeCLM_injective := (Sum H H₁).subtype_injective

lemma norm_eq (f : Sum H H₁) :
    ‖f‖ = sInf (norm '' { g | generator H H₁ g = f} ) := by
  obtain ⟨g₀, hg₀⟩ : ∃ g, (generator H H₁) g = f := f.2
  have h1 : sInf (norm '' {g | (generator H H₁) g = f }) = sInf ((fun g ↦ ‖g₀ + g‖) '' {k | (generator H H₁) k = 0 }) := by
    congr 1; ext k
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨g, hTg, rfl⟩
      exact ⟨g-g₀, by simp only [map_sub, add_sub_cancel, and_true, hTg, <-hg₀, sub_self]⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g+g₀, by simp_rw [ContinuousLinearMap.map_add, hg, <-hg₀,zero_add, add_comm]; simp⟩
  rw [h1, show {k | (generator H H₁) k = 0 } = (generator H H₁).ker.toAddSubgroup from rfl,
    ← quotient_norm_mk_eq _ g₀]
  rw [show ‖f‖ = ‖(generator H H₁).quotKerEquivRange.symm f‖ from rfl]
  apply congrArg
  apply (LinearEquiv.symm_apply_eq ((generator H H₁).quotKerEquivRange)).mpr
  apply Subtype.val_injective
  rw [QuotientAddGroup.mk'_apply, SetLike.coe_eq_coe]
  exact SetLike.coe_eq_coe.mp (id (Eq.symm hg₀))

def generator' : WithLp 2 (H × H₁) →L[𝕜] Sum H H₁ :=
  (generator H H₁).toLinearMap.rangeRestrict.mkContinuous 1 (by
    intro p
    rw [norm_eq, one_mul]
    refine csInf_le ⟨0, ?_⟩ (Set.mem_image_of_mem norm rfl)
    rintro _ ⟨_, _, rfl⟩
    exact norm_nonneg _
  )

variable (𝕜 H H₁) in
/-- Composition of projection `H →L[𝕜] WithLp 2 (H × H₁)` with generator -/
def coeL : H →L[𝕜] (Sum H H₁) := generator'
  ∘L (WithLp.prodContinuousLinearEquiv 2 𝕜 H H₁).symm.toContinuousLinearMap
  ∘L ContinuousLinearMap.prod (ContinuousLinearMap.id 𝕜 H) 0

variable (𝕜 H H₁) in
/-- Composition of projection `H₁ →L[𝕜] WithLp 2 (H × H₁)` with generator -/
def coeR : H₁ →L[𝕜] (Sum H H₁) := generator'
  ∘L (WithLp.prodContinuousLinearEquiv 2 𝕜 H H₁).symm.toContinuousLinearMap
  ∘L ContinuousLinearMap.prod 0 (ContinuousLinearMap.id 𝕜 H₁)

instance [CompleteSpace H] [CompleteSpace H₁] : CompleteSpace (Sum H H₁) := by
  let ie : Sum H H₁ ≃ᵢ (WithLp 2 (H × H₁) ⧸ (generator H H₁).ker) := {
    toFun := (generator H H₁).quotKerEquivRange.symm.toLinearMap
    invFun := (generator H H₁).quotKerEquivRange.toLinearMap
    isometry_toFun x y := by rfl
    left_inv f := (generator H H₁).quotKerEquivRange.apply_symm_apply f
    right_inv f := (generator H H₁).quotKerEquivRange.symm_apply_apply f
  }
  exact IsometryEquiv.completeSpace ie

lemma adjoint_coeL_add_adjoint_coeR_eq (f : Sum H H₁) (x : X) :
    (adjoint (coeL 𝕜 H H₁) f) x + (adjoint (coeR 𝕜 H H₁) f) x = f x := sorry

theorem kerFun_sum_eq_sum_of_kerFun (x : X) :
    kerFun (Sum H H₁) x = (coeL 𝕜 H H₁) ∘L kerFun H x + (coeR 𝕜 H H₁) ∘L kerFun H₁ x := by
  apply ContinuousLinearMap.ext
  intro v
  rw [ext_iff_inner_left (𝕜 := 𝕜)]
  intro f
  simp
  rw [inner_add_right, ← adjoint_inner_left, inner_kerFun, ← adjoint_inner_left, inner_kerFun,
    ← adjoint_coeL_add_adjoint_coeR_eq, inner_add_left]

theorem kernel_sum_eq_sum_of_kernel : kernel (Sum H H₁) = kernel H + kernel H₁ := by
  ext
  rw [Matrix.add_apply, add_apply]
  simp_rw [← kerFun_apply]
  rw [kerFun_sum_eq_sum_of_kerFun]
  sorry


end Sum

end RKHS
