/-
Copyright (c) 2026 Hampus Nyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hampus Nyberg
-/
module

public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Reproducing Kernel Hilbert Spaces

This file defines vector-valued reproducing Kernel Hilbert spaces, which are Hilbert spaces of
functions, as well as characterizing these spaces in terms of infinite-dimensional
positive semidefinite matrices.

## Main results

- `RKHS` : the class of reproducing kernel Hilbert spaces
- `RKHS.kernel` : the kernel of a RKHS as a matrix.
- `RKHS.kerFun` : the kernel functions of a RKHS.
- `RKHS.kerFun_dense` : the kernel functions are dense in the Hilbert space.
- `RKHS.posSemidef_kernel`: The kernel is positive semidefinite.
- `KernelRKHS` : RKHS constructed from a positive semidefinite matrix.
- `Kernel_eq_Kernel` : The kernel of the constructed RKHS is equal to the matrix, this is
    essentially Moore's theorem.
## To Do:

- `Privatize KernelRKHS`
-/
open scoped ComplexOrder
open ContinuousLinearMap

public section

noncomputable section

--Move to better file
variable (𝕜 : Type*) {X V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

open InnerProductSpace in
theorem denseRange_ext_inner_zero {v : V} {X : Type*} {f : X → V} (hd : DenseRange f)
    (h : ∀ x, ⟪f x, v⟫_𝕜 = 0) : v = 0 := by
  rw [← @inner_self_eq_zero 𝕜, ← norm_eq_zero]
  refine le_antisymm (le_of_forall_pos_lt_add fun ε hε ↦ ?_) <| by simp
  by_cases h1 : ‖v‖ = 0
  · simp [h1, hε]
  obtain ⟨c,hc⟩ := hd.exists_dist_lt v <| div_pos hε <| lt_of_le_of_ne' (by simp) h1
  rw [dist_eq_norm v (f c)] at hc
  calc
    _ = ‖⟪v - f c + f c, v⟫_𝕜‖ := by simp
    _ = ‖⟪v - f c, v⟫_𝕜 + ⟪f c, v⟫_𝕜‖ := by simp only [inner_add_left]
    _ ≤ ‖v - f c‖ * ‖v‖ := by simp [h, norm_inner_le_norm]
    _ < ε / ‖v‖ * ‖v‖ := by simp [lt_of_le_of_ne' _ h1, hc]
    _ = _ := by simp[h1]

open InnerProductSpace in
theorem denseRange_ext_zero_inner {v : V} {X : Type*} {f : X → V} (hd : DenseRange f)
    (h : ∀ x, ⟪v, f x⟫_𝕜 = 0) : v = 0 := denseRange_ext_inner_zero 𝕜 hd (by
      conv =>
        enter [x, 1]
        rw [← inner_conj_symm]
      simp [h]
    )

/--
Class of vector valued Reproducing Kernel Hilbert Spaces.
-/
class RKHS (𝕜 X V : outParam Type*) (H : Type*) [RCLike 𝕜]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] where
  coeCLM (𝕜) : H →L[𝕜] X → V
  coeCLM_injective : Function.Injective (coeCLM : H → X → V)

namespace RKHS

open InnerProductSpace
open Submodule

variable {𝕜 : outParam Type*} [RCLike 𝕜] --ℝ or ℂ
variable {X : outParam Type*} --Domain
variable {V : outParam Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] --Co-domain
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] --Our space of functions
variable [RKHS 𝕜 X V H]
local notation :90 "†" => starRingEnd 𝕜

instance instFunLiketoFun : FunLike H X V where
  coe := fun f ↦ coeCLM 𝕜 f
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

variable [CompleteSpace H] [CompleteSpace V]

variable (H) in
def kerFun (x : X) : V →L[𝕜] H := ((ContinuousLinearMap.proj x) ∘L (coeCLM 𝕜)).adjoint --make priv

--simp?
lemma coeCLM_to_kerFun :
    coeCLM 𝕜 = ContinuousLinearMap.pi (fun x ↦ (kerFun H x).adjoint) := by simp [kerFun]

lemma coeCLM_to_kerFun' (f : H) :
    ⇑f = ContinuousLinearMap.pi (fun x ↦ (kerFun H x).adjoint) f := by simp [kerFun]

lemma coeCLM_to_kerFun'' (x : X) (f : H) : f x = (kerFun H x).adjoint f := by simp [kerFun]

variable (H) in
def kernel : Matrix X X (V →L[𝕜] V) := .of fun x y ↦ (kerFun H x).adjoint ∘L kerFun H y

lemma kerFun_apply (y : X) (v : V) : kerFun H y v = fun x ↦ kernel H x y v := by
  simp [kernel, kerFun]

lemma kernel_kerFun (x y : X) : kernel H x y = (kerFun H x).adjoint ∘L (kerFun H y) := by
  simp [kerFun, kernel]

@[simp]
lemma kerFun_inner (x : X) (v : V) (f : H) : ⟪kerFun H x v, f⟫_𝕜 = ⟪v, f x⟫_𝕜 := by
  simp [kerFun, ← adjoint_inner_right]

@[simp]
lemma inner_kerFun (x : X) (v : V) (f : H) : ⟪f, kerFun H x v⟫_𝕜 = ⟪f x, v⟫_𝕜 := by
  simp [kerFun, ← adjoint_inner_left]

lemma kernel_inner (x y : X) (v w : V) :
    ⟪(kernel H x y) v, w⟫_𝕜 = ⟪kerFun H y v, kerFun H x w⟫_𝕜 := by
  simp [← adjoint_inner_left, kernel_kerFun]

theorem kerFun_dense : topologicalClosure (span 𝕜 {kerFun H x v | (x) (v)}) = ⊤ := by
  refine (orthogonal_eq_bot_iff.mp ((Submodule.eq_bot_iff _).mpr fun f fin ↦ (DFunLike.ext f 0) ?_))
  refine fun x ↦ ext_inner_left 𝕜 (fun v ↦ ?_)
  simp only [← kerFun_inner, coe_zero, Pi.zero_apply, inner_zero_right]
  refine inner_right_of_mem_orthogonal (subset_closure ?_) fin
  simp [mem_span_of_mem]

variable (H) in
lemma isHermitian_kernel : (kernel H).IsHermitian := by
  ext _ _ _
  refine ext_inner_right 𝕜 fun w ↦ ?_
  simp only [Matrix.conjTranspose_apply, star, adjoint_inner_left,
    ← inner_conj_symm _ ((kernel H _ _) _), kernel_inner, inner_conj_symm]

variable (H) in
theorem posSemidef_kernel : (kernel H).PosSemidef := by
  refine ⟨isHermitian_kernel H, fun s ↦ (ContinuousLinearMap.isPositive_iff' _).mpr ⟨?_,fun v ↦ ?_⟩⟩
  · rw [IsSelfAdjoint, sub_zero, star_finsuppSum, Finsupp.sum_comm]
    simp [← mul_assoc, Matrix.IsHermitian.apply (isHermitian_kernel H)]
  · simp [Finsupp.sum_apply'', Finsupp.sum_inner, star, adjoint_inner_left,
      kernel_inner, -inner_kerFun, -kerFun_inner]
    simp only [← Finsupp.sum_inner, ← Finsupp.inner_sum,
      inner_self_eq_norm_sq_to_K, RCLike.ofReal_nonneg, norm_nonneg, pow_succ_nonneg]

end RKHS

/-!
## Construction of RKHS from kernel
-/

section

variable {X : Type*}
variable {𝕜 : Type*} [RCLike 𝕜] --ℝ or ℂ
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
local notation :90 "†" => starRingEnd 𝕜

open InnerProductSpace
open Submodule

variable {K : Matrix X X (V →L[𝕜] V)}

@[simp]
lemma Hermitian_IsSelfAdjoint_Finsupp_sum (h : K.IsHermitian) (f : X →₀ V →L[𝕜] V) :
    IsSelfAdjoint (f.sum fun i xi ↦ f.sum fun j xj ↦ star xi * K i j * xj) := by
  simp only [mul_assoc, isSelfAdjoint_iff, star_finsuppSum, Pi.star_apply, star_mul, h.apply,
    star_star]
  rw [Finsupp.sum_comm]

theorem PosSemidef_TFAE : List.TFAE [K.PosSemidef, K.IsHermitian ∧ ∀ (f : X × V →₀ 𝕜),
    0 ≤ RCLike.re (f.sum fun xv z ↦ f.sum fun xv' w ↦ (†) z * w * ⟪(K xv'.1 xv.1) xv.2, xv'.2⟫_𝕜),
    K.IsHermitian ∧ ∀ (vv : X →₀ V),
    0 ≤ RCLike.re (vv.sum fun x w ↦ (vv.sum fun x' w' ↦ ⟪(K x' x) w, w'⟫_𝕜)),
    ] := by
  have {h p1 p2 p3 : Prop} (htfae : h → List.TFAE [p1, p2, p3]) :
      List.TFAE [h ∧ p1, h ∧ p2, h ∧ p3] := by
    tfae_have 1 → 2 := fun ⟨h, t⟩ ↦ ⟨h, ((htfae h).out 0 1).mp t⟩
    tfae_have 2 → 3 := fun ⟨h, t⟩ ↦ ⟨h, ((htfae h).out 1 2).mp t⟩
    tfae_have 3 → 1 := fun ⟨h, t⟩ ↦ ⟨h, ((htfae h).out 2 0).mp t⟩
    tfae_finish
  refine this fun hHerm ↦ ?_
  simp only [nonneg_iff_isPositive, isPositive_def', Hermitian_IsSelfAdjoint_Finsupp_sum hHerm,
    reApplyInnerSelf_apply, true_and]
  simp only [star_eq_adjoint, zero_apply, add_apply, implies_true, Finsupp.sum_apply'', coe_mul,
    Function.comp_apply, Finsupp.sum_inner, adjoint_inner_left]
  refine (subsingleton_or_nontrivial V).elim (fun h ↦ ?_) (fun _ ↦ ?_) --nontriviality?
  · have : ∀ v : V, v = 0 := fun v ↦ Subsingleton.elim v 0
    simp [this]
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  tfae_have 1 → 2 := fun h ↦ fun ff ↦ by
    rw [Finsupp.sum_comm]
    convert h (ff.sum fun xv z ↦ .single xv.1
      ((z/‖v‖ ^ 2) • (innerSL 𝕜 v).smulRight xv.2)) v
    simp [Finsupp.sum_sum_index, inner_add_right, inner_add_left, ← smul_assoc, hv]
    simp [inner_smul_left, inner_smul_right, ← mul_assoc, mul_comm]
  tfae_have 2 → 3 := fun h ↦ fun vv ↦ by
    simpa [add_mul, Finsupp.sum_sum_index] using (h (vv.sum fun x v ↦ .single ⟨x, v⟩ 1))
  tfae_have 3 → 1 := fun h ↦ fun ff v ↦ by
    rw [Finsupp.sum_comm]
    simpa [Finsupp.sum_sum_index, inner_add_right, inner_add_left] using
      h (ff.sum fun x T ↦ .single x (T v))
  tfae_finish

set_option linter.unusedVariables false in
abbrev H₀ (K : Matrix X X (V →L[𝕜] V)) := (X × V →₀ 𝕜) --TODO: Privatize

variable [Fact K.PosSemidef]

instance instkernelToPreInnerCore :
    PreInnerProductSpace.Core 𝕜 (H₀ K) where
  inner := fun f g ↦ f.sum fun ⟨y, u⟩ z ↦ g.sum fun ⟨x, v⟩ w ↦ star z * w * ⟪(K x y) u, v⟫_𝕜
  conj_inner_symm := fun f g ↦ by
    rw [Finsupp.sum_comm]
    simp only [map_finsuppSum]
    congr! 6
    rw [← (Fact.out : K.PosSemidef).isHermitian.apply]
    simp [star, adjoint_inner_right, mul_comm]
  add_left := fun _ _ _ ↦ by
    rw [Finsupp.sum_add_index'] <;> simp [← Finsupp.sum_add, add_mul]
  smul_left := fun _ _ _ ↦ by
    rw [Finsupp.sum_smul_index] <;> simp [Finsupp.mul_sum, ← mul_assoc]
  re_inner_nonneg := by
    have := (PosSemidef_TFAE.out 0 1).mp (Fact.out : K.PosSemidef)
    exact this.2

instance instkernelToSeminormedAddCommGroup : SeminormedAddCommGroup (H₀ K) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := 𝕜)

instance kernelToPreInnerProductSpace : InnerProductSpace 𝕜 (H₀ K) :=
  InnerProductSpace.ofCore instkernelToPreInnerCore

private lemma H₀inner_def (f g : H₀ K) :
    ⟪f, g⟫_𝕜 = f.sum fun ⟨y, u⟩ z ↦ g.sum fun ⟨x, v⟩ w ↦ star z * w * ⟪(K x y) u, v⟫_𝕜 := rfl

variable (K) in
abbrev KernelRKHS := UniformSpace.Completion <| SeparationQuotient (H₀ K)
--deriving SeminormedAddCommGroup, InnerProductSpace 𝕜, CompleteSpace

namespace KernelRKHS

private abbrev kerFunAux' (x : X) : V →ₗ[𝕜] SeparationQuotient (H₀ K) where
  toFun v: SeparationQuotient (H₀ K) := SeparationQuotient.mk (Finsupp.single ⟨x,v⟩ 1)
  map_add' _ _ := by
    rw [ext_iff_inner_left 𝕜, SeparationQuotient.surjective_mk.forall]
    simp [← SeparationQuotient.mk_add, H₀inner_def, ← Finsupp.sum_add, mul_assoc,
    ← mul_add, inner_add_right]
  map_smul' _ _ := by
    rw [ext_iff_inner_left 𝕜, SeparationQuotient.surjective_mk.forall]
    simp [← SeparationQuotient.mk_smul, H₀inner_def, inner_smul_right, mul_assoc]

private abbrev kerFunAux (x : X) :
    V →L[𝕜] SeparationQuotient (H₀ K) := (kerFunAux' x).mkContinuous √‖K x x‖ fun v ↦ by
  refine (sq_le_sq₀ (by simp) (by simp [mul_nonneg])).mp ?_
  simp only [LinearMap.coe_mk, AddHom.coe_mk, SeparationQuotient.norm_mk,
    ← inner_self_eq_norm_sq (𝕜 := 𝕜), inner_self_re_eq_norm]
  simp only [H₀inner_def, RCLike.star_def, mul_zero, zero_mul,
      Finsupp.sum_single_index, mul_one, map_zero, map_one, one_mul]
  calc
    _ ≤ ‖K x x v‖ * ‖v‖ := by simp [norm_inner_le_norm]
    _ ≤ ‖K x x‖ * ‖v‖ * ‖v‖ := by simp [mul_le_mul_of_nonneg_right, le_opNorm]
    _ ≤ _ := by simp [mul_pow, mul_assoc, ← sq]

variable (K) in
def kerFun (x : X) : V →L[𝕜] (KernelRKHS K) := UniformSpace.Completion.toComplL ∘L kerFunAux x

instance instRKHS : RKHS 𝕜 X V (KernelRKHS K) where
  coeCLM := .pi fun x ↦ (kerFun K x).adjoint
  coeCLM_injective := by
    refine (injective_iff_map_eq_zero _).mpr fun f h ↦ ?_
    refine denseRange_ext_inner_zero 𝕜 UniformSpace.Completion.denseRange_coe ?_
    refine (Function.Surjective.forall SeparationQuotient.surjective_mk).mpr
      fun ff ↦ ?_
    have : ff = ff.sum fun xv z ↦ .single xv z := by simp
    rw [this, ← SeparationQuotient.mkCLM_apply 𝕜, ← UniformSpace.Completion.coe_toComplL (𝕜 := 𝕜)]
    simp only [map_finsuppSum, Finsupp.sum_inner]
    have (i : X × V) (a : 𝕜): ⟪UniformSpace.Completion.toComplL (𝕜 := 𝕜)
        ((SeparationQuotient.mkCLM 𝕜 (H₀ K)) (Finsupp.single i a)), f⟫_𝕜 = 0 := by
      have := (ext_iff_inner_left 𝕜).mp (congrFun h i.1) i.2
      simp only [kerFun, coe_pi', adjoint_inner_right, coe_comp',
        UniformSpace.Completion.coe_toComplL, Function.comp_apply, LinearMap.mkContinuous_apply,
        LinearMap.coe_mk, AddHom.coe_mk, Prod.mk.eta, Pi.zero_apply, inner_zero_right] at this
      rw [← mul_zero ((†) a), ← this, ← inner_smul_left]
      refine (ext_iff_inner_right 𝕜).mp ?_ f
      simp [← SeparationQuotient.mkCLM_apply 𝕜, ← UniformSpace.Completion.coe_toComplL (𝕜 := 𝕜),
        ← map_smul, -SeparationQuotient.mkCLM_apply, -UniformSpace.Completion.coe_toComplL]
    simp only [this]
    simp

lemma kerFun_apply (y : X) (v : V) : (kerFun K y) v = fun x ↦ (K x y) v := by
  rw [show ⇑((kerFun K y) v) = (RKHS.coeCLM 𝕜) ((kerFun K y) v) from rfl]
  simp only [RKHS.coeCLM]
  ext x
  refine ext_inner_right 𝕜 fun w ↦ ?_
  simp [adjoint_inner_left, kerFun, H₀inner_def]

@[simp]
theorem kernel_kernelToRKHS : RKHS.kernel (KernelRKHS K) = K := by
  ext x y v
  refine ext_inner_right 𝕜 fun w ↦ ?_
  simp [RKHS.kernel, adjoint_inner_left, -RKHS.inner_kerFun, -RKHS.kerFun_inner,
    RKHS.kerFun, RKHS.coeCLM, kerFun , H₀inner_def]

theorem kerFun_eq_KerFun : RKHS.kerFun (KernelRKHS K) = kerFun K := by
  ext y v x
  simp [kerFun_apply, RKHS.kerFun_apply, ← kernel_kernelToRKHS]
