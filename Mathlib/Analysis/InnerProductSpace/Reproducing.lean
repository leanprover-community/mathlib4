import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.TensorProduct


open scoped ComplexOrder
open ContinuousLinearMap

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
  have hpos : 0 < ‖v‖ := lt_of_le_of_ne' (by simp) h1
  obtain ⟨c,hc⟩ := hd.exists_dist_lt v <| div_pos hε <| lt_of_le_of_ne' (by simp) h1
  rw [dist_eq_norm v (f c)] at hc
  calc
    _ = ‖⟪v - f c + f c, v⟫_𝕜‖ := by simp
    _ = ‖⟪v - f c, v⟫_𝕜 + ⟪f c, v⟫_𝕜‖ := by simp only [inner_add_left]
    _ ≤ ‖v - f c‖ * ‖v‖ := by simp [h, norm_inner_le_norm]
    _ < ε / ‖v‖ * ‖v‖ := by simp [hpos, hc]
    _ = _ := by simp[h1]

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
def kerFun (x : X) : V →L[𝕜] H := ((ContinuousLinearMap.proj x) ∘L (coeCLM 𝕜)).adjoint

--simp?
lemma coeCLM_to_kerFun' :
    coeCLM 𝕜 = ContinuousLinearMap.pi (fun x ↦ (kerFun H x).adjoint) := by simp [kerFun]

lemma coeCLM_to_kerFun (x : X) (f : H) : (coeCLM 𝕜) f x = (kerFun H x).adjoint f := by simp [kerFun]

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

theorem kernelPossemiDef : (kernel H).PosSemidef := by
  refine ⟨isHermitian_kernel H, fun s ↦ (ContinuousLinearMap.isPositive_iff' _).mpr ⟨?_,fun v ↦ ?_⟩⟩
  · rw [IsSelfAdjoint, sub_zero, star_finsuppSum, Finsupp.sum_comm]
    simp [← mul_assoc, Matrix.IsHermitian.apply (isHermitian_kernel H)]
  · simp [Finsupp.sum_apply'', Finsupp.sum_inner, star, adjoint_inner_left,
      kernel_inner, -inner_kerFun, -kerFun_inner]
    simp only [← Finsupp.sum_inner, ← Finsupp.inner_sum,
      inner_self_eq_norm_sq_to_K, RCLike.ofReal_nonneg, norm_nonneg, pow_succ_nonneg]

end RKHS

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

theorem PosSemidef_iff : K.PosSemidef ↔ K.IsHermitian ∧
    ∀ (f : X × V →₀ 𝕜), 0 ≤ RCLike.re
    (f.sum fun xv z ↦ f.sum fun xv' w ↦ (†) z * w * ⟪(K xv'.1 xv.1) xv.2, xv'.2⟫_𝕜) := by
  have (T T' K: V →L[𝕜] V) (v : V) :
      ⟪(adjoint T) (K (T' v)), v⟫_𝕜 = ⟪K (((apply 𝕜 V) v) T'), ((apply 𝕜 V) v) T⟫_𝕜 := by
    simp [adjoint_inner_left]
  simp +contextual only [Matrix.PosSemidef, nonneg_iff_isPositive, isPositive_def',
    reApplyInnerSelf_apply, and_congr_right_iff, Hermitian_IsSelfAdjoint_Finsupp_sum, true_and]
  simp only [star_eq_adjoint, zero_apply, add_apply, implies_true, Finsupp.sum_apply'', coe_mul,
    Function.comp_apply, Finsupp.sum_inner, this]
  congr!
  refine (subsingleton_or_nontrivial V).elim (fun h ↦ ?_) (fun _ ↦ ?_) --nontriviality?
  · have : ∀ v : V, v = 0 := fun v ↦ Subsingleton.elim v 0
    simp [this]
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  letI p : Prop := ∀ (vv : X →₀ V),
      0 ≤ RCLike.re (vv.sum fun x w ↦ (vv.sum fun x' w' ↦ ⟪(K x' x) w, w'⟫_𝕜))
  have {a b : Prop} (c : Prop) (h : List.TFAE [a, b, c]) : a ↔ b := h.out 0 1
  refine this p ?_
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
abbrev H₀ (hK : K.PosSemidef) := (X × V →₀ 𝕜)

variable (hK : K.PosSemidef)

instance instkernelToPreInnerCore :
    PreInnerProductSpace.Core 𝕜 (H₀ hK) where
  inner := fun f g ↦ f.sum fun ⟨y, u⟩ z ↦ g.sum fun ⟨x, v⟩ w ↦ star z * w * ⟪(K x y) u, v⟫_𝕜
  conj_inner_symm := fun f g ↦ by
    rw [Finsupp.sum_comm]
    simp only [map_finsuppSum]
    congr! 6
    rw [← hK.isHermitian.apply]
    simp [star, adjoint_inner_right, mul_comm]
  add_left := fun _ _ _ ↦ by
    rw [Finsupp.sum_add_index'] <;> simp [← Finsupp.sum_add, add_mul]
  smul_left := fun _ _ _ ↦ by
    rw [Finsupp.sum_smul_index] <;> simp [Finsupp.mul_sum, ← mul_assoc]
  re_inner_nonneg := ((PosSemidef_iff).mp hK).2

instance instkernelToSeminormedAddCommGroup : SeminormedAddCommGroup (H₀ hK) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := 𝕜)

instance kernelToPreInnerProductSpace : InnerProductSpace 𝕜 (H₀ hK) :=
  InnerProductSpace.ofCore (instkernelToPreInnerCore hK)

lemma H₀inner_def (f g : H₀ hK) :
    ⟪f, g⟫_𝕜 = f.sum fun ⟨y, u⟩ z ↦ g.sum fun ⟨x, v⟩ w ↦ star z * w * ⟪(K x y) u, v⟫_𝕜 := rfl

abbrev H₁ := SeparationQuotient (H₀ hK)

abbrev kernelToRKHS := UniformSpace.Completion (H₁ hK)

abbrev pre_kerFun' (x : X) : V →ₗ[𝕜] (H₁ hK) where
  toFun : V → H₁ hK := fun v ↦ SeparationQuotient.mk (Finsupp.single ⟨x,v⟩ 1)
  map_add' := fun v w ↦ by
    refine (ext_iff_inner_left 𝕜).mpr <|
      (Function.Surjective.forall SeparationQuotient.surjective_mk).mpr fun ff ↦ ?_
    simp [← SeparationQuotient.mk_add, H₀inner_def hK, Finsupp.sum_add_index', mul_assoc,
      ← mul_add, add_mul, inner_add_right]
  map_smul' := fun z v ↦ by
    refine (ext_iff_inner_left 𝕜).mpr <|
       (Function.Surjective.forall SeparationQuotient.surjective_mk).mpr fun ff ↦ ?_
    simp [← SeparationQuotient.mk_smul, H₀inner_def hK, inner_smul_right, mul_assoc]

abbrev pre_kerFun (x : X) : V →L[𝕜] (H₁ hK) := (pre_kerFun' hK x).mkContinuous √‖K x x‖ <| by
  refine fun v ↦ (sq_le_sq₀ (by simp) (by simp [mul_nonneg])).mp ?_
  simp only [LinearMap.coe_mk, AddHom.coe_mk, SeparationQuotient.norm_mk,
    ← inner_self_eq_norm_sq (𝕜 := 𝕜), inner_self_re_eq_norm]
  simp only [H₀inner_def hK, RCLike.star_def, mul_zero, zero_mul, Finsupp.sum_single_index,
    mul_one, map_zero, map_one, one_mul]
  calc
    _ ≤ ‖K x x v‖ * ‖v‖ := by simp [norm_inner_le_norm]
    _ ≤ ‖K x x‖ * ‖v‖ * ‖v‖ := by simp [mul_le_mul_of_nonneg_right, le_opNorm]
    _ ≤ _ := by simp [mul_pow, mul_assoc, ← sq]

def kerFun (x : X) : V →L[𝕜] kernelToRKHS hK :=
  UniformSpace.Completion.toComplL ∘L pre_kerFun hK x

instance instKernelToRKHS : RKHS 𝕜 X V (kernelToRKHS hK) where
  coeCLM := ContinuousLinearMap.pi (fun x ↦ (kerFun hK x).adjoint)
  coeCLM_injective := by
    refine (injective_iff_map_eq_zero _).mpr fun f h ↦ ?_
    refine denseRange_ext_inner_zero 𝕜 UniformSpace.Completion.denseRange_coe ?_
    refine (Function.Surjective.forall SeparationQuotient.surjective_mk).mpr
      fun ff ↦ ?_
    have : ff = ff.sum fun xv z ↦ .single xv z := by simp
    rw [this, ← SeparationQuotient.mkCLM_apply 𝕜, ← UniformSpace.Completion.coe_toComplL (𝕜 := 𝕜)]
    simp only [map_finsuppSum, Finsupp.sum_inner]
    have (i : X × V) (a : 𝕜): ⟪UniformSpace.Completion.toComplL (𝕜 := 𝕜)
        ((SeparationQuotient.mkCLM 𝕜 (H₀ hK)) (Finsupp.single i a)), f⟫_𝕜 = 0 := by
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

theorem Kernel_eq_Kernel : K = RKHS.kernel (kernelToRKHS hK) := by
  ext x y v
  refine ext_inner_right 𝕜 fun w ↦ ?_
  simp [RKHS.kernel, adjoint_inner_left, -RKHS.inner_kerFun, -RKHS.kerFun_inner,
    RKHS.kerFun, RKHS.coeCLM, kerFun, H₀inner_def hK]

lemma kerFun_apply (y : X) (v : V) : (kerFun hK y) v = fun x ↦ (K x y) v := by
  rw [show ⇑((kerFun hK y) v) = (RKHS.coeCLM 𝕜) ((kerFun hK y) v) from rfl]
  simp only [RKHS.coeCLM]
  ext x
  refine ext_inner_right 𝕜 fun w ↦ ?_
  simp [adjoint_inner_left, kerFun, H₀inner_def hK]

theorem kerFun_eq_KerFun : RKHS.kerFun (kernelToRKHS hK) = kerFun hK := by
  ext y v x
  simp [kerFun_apply, RKHS.kerFun_apply, ← Kernel_eq_Kernel]

end
