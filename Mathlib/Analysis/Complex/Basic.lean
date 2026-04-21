/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.Complex.BigOperators
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Topology.Algebra.Algebra.Equiv
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Topology.Instances.RealVectorSpace

/-!

# Normed space structure on `ℂ`.

This file gathers basic facts of analytic nature on the complex numbers.

## Main results

This file registers `ℂ` as a normed field, expresses basic properties of the norm, and gives tools
on the real vector space structure of `ℂ`. Notably, it defines the following functions in the
namespace `Complex`.

|Name              |Type         |Description                                             |
|------------------|-------------|--------------------------------------------------------|
|`equivRealProdCLM`|ℂ ≃L[ℝ] ℝ × ℝ|The natural `ContinuousLinearEquiv` from `ℂ` to `ℝ × ℝ` |
|`reCLM`           |ℂ →L[ℝ] ℝ    |Real part function as a `ContinuousLinearMap`           |
|`imCLM`           |ℂ →L[ℝ] ℝ    |Imaginary part function as a `ContinuousLinearMap`      |
|`ofRealCLM`       |ℝ →L[ℝ] ℂ    |Embedding of the reals as a `ContinuousLinearMap`       |
|`ofRealLI`        |ℝ →ₗᵢ[ℝ] ℂ   |Embedding of the reals as a `LinearIsometry`            |
|`conjCLE`         |ℂ ≃L[ℝ] ℂ    |Complex conjugation as a `ContinuousLinearEquiv`        |
|`conjLIE`         |ℂ ≃ₗᵢ[ℝ] ℂ   |Complex conjugation as a `LinearIsometryEquiv`          |

We also register the fact that `ℂ` is an `RCLike` field.

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section


assert_not_exists Absorbs

/-- A shortcut instance to ensure computability; otherwise we get the noncomputable instance
`Complex.instNormedField.toNormedModule.toModule`. -/
instance Complex.instModuleSelf : Module ℂ ℂ := delta% inferInstance

noncomputable section

namespace Complex
variable {z : ℂ}

open ComplexConjugate Topology Filter

instance : NormedField ℂ where
  dist_eq _ _ := rfl
  norm_mul := Complex.norm_mul

instance : DenselyNormedField ℂ where
  lt_norm_lt r₁ r₂ h₀ hr :=
    let ⟨x, h⟩ := exists_between hr
    ⟨x, by rwa [norm_real, Real.norm_of_nonneg (h₀.trans_lt h.1).le]⟩

set_option backward.isDefEq.respectTransparency false in
instance {R : Type*} [NormedField R] [NormedAlgebra R ℝ] : NormedAlgebra R ℂ where
  norm_smul_le r x := by
    rw [← algebraMap_smul ℝ r x, real_smul, norm_mul, norm_real, norm_algebraMap']

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]

-- see Note [lower instance priority]
/-- The module structure from `Module.complexToReal` is a normed space. -/
instance (priority := 900) _root_.NormedSpace.complexToReal : NormedSpace ℝ E :=
  NormedSpace.restrictScalars ℝ ℂ E

-- see Note [lower instance priority]
/-- The algebra structure from `Algebra.complexToReal` is a normed algebra. -/
instance (priority := 900) _root_.NormedAlgebra.complexToReal {A : Type*} [SeminormedRing A]
    [NormedAlgebra ℂ A] : NormedAlgebra ℝ A :=
  NormedAlgebra.restrictScalars ℝ ℂ A

-- This result cannot be moved to `Data/Complex/Norm` since `ℤ` gets its norm from its
-- normed ring structure and that file does not know about rings
@[simp 1100, norm_cast] lemma nnnorm_intCast (n : ℤ) : ‖(n : ℂ)‖₊ = ‖n‖₊ := by
  ext; exact norm_intCast n

@[continuity, fun_prop]
theorem continuous_normSq : Continuous normSq := by
  simpa [← Complex.normSq_eq_norm_sq] using continuous_norm (E := ℂ).pow 2

theorem nnnorm_eq_one_of_pow_eq_one {ζ : ℂ} {n : ℕ} (h : ζ ^ n = 1) (hn : n ≠ 0) : ‖ζ‖₊ = 1 :=
  (pow_left_inj₀ zero_le' zero_le' hn).1 <| by rw [← nnnorm_pow, h, nnnorm_one, one_pow]

theorem norm_eq_one_of_pow_eq_one {ζ : ℂ} {n : ℕ} (h : ζ ^ n = 1) (hn : n ≠ 0) : ‖ζ‖ = 1 :=
  congr_arg Subtype.val (nnnorm_eq_one_of_pow_eq_one h hn)

lemma le_of_eq_sum_of_eq_sum_norm {ι : Type*} {a b : ℝ} (f : ι → ℂ) (s : Finset ι) (ha₀ : 0 ≤ a)
    (ha : a = ∑ i ∈ s, f i) (hb : b = ∑ i ∈ s, (‖f i‖ : ℂ)) : a ≤ b := by
  norm_cast at hb; rw [← Complex.norm_of_nonneg ha₀, ha, hb]; exact norm_sum_le s f

theorem equivRealProd_apply_le (z : ℂ) : ‖equivRealProd z‖ ≤ ‖z‖ := by
  simp [Prod.norm_def, abs_re_le_norm, abs_im_le_norm]

theorem equivRealProd_apply_le' (z : ℂ) : ‖equivRealProd z‖ ≤ 1 * ‖z‖ := by
  simpa using equivRealProd_apply_le z

theorem lipschitz_equivRealProd : LipschitzWith 1 equivRealProd := by
  simpa using AddMonoidHomClass.lipschitz_of_bound equivRealProdLm 1 equivRealProd_apply_le'

theorem antilipschitz_equivRealProd : AntilipschitzWith (NNReal.sqrt 2) equivRealProd :=
  AddMonoidHomClass.antilipschitz_of_bound equivRealProdLm fun z ↦ by
    simpa only [Real.coe_sqrt, NNReal.coe_ofNat] using norm_le_sqrt_two_mul_max z

theorem isUniformEmbedding_equivRealProd : IsUniformEmbedding equivRealProd :=
  antilipschitz_equivRealProd.isUniformEmbedding lipschitz_equivRealProd.uniformContinuous

instance : CompleteSpace ℂ :=
  (completeSpace_congr isUniformEmbedding_equivRealProd).mpr inferInstance

instance instT2Space : T2Space ℂ := TopologicalSpace.t2Space_of_metrizableSpace

/-- The natural `ContinuousLinearEquiv` from `ℂ` to `ℝ × ℝ`. -/
@[simps! +simpRhs apply symm_apply_re symm_apply_im]
def equivRealProdCLM : ℂ ≃L[ℝ] ℝ × ℝ :=
  equivRealProdLm.toContinuousLinearEquivOfBounds 1 (√2) equivRealProd_apply_le' fun p =>
    norm_le_sqrt_two_mul_max (equivRealProd.symm p)

theorem equivRealProdCLM_symm_apply (p : ℝ × ℝ) :
    Complex.equivRealProdCLM.symm p = p.1 + p.2 * Complex.I := Complex.equivRealProd_symm_apply p

instance : ProperSpace ℂ := lipschitz_equivRealProd.properSpace
  equivRealProdCLM.toHomeomorph.isProperMap

/-- The `normSq` function on `ℂ` is proper. -/
theorem tendsto_normSq_cocompact_atTop : Tendsto normSq (cocompact ℂ) atTop := by
  simpa [norm_mul_self_eq_normSq]
    using tendsto_norm_cocompact_atTop.atTop_mul_atTop₀ (tendsto_norm_cocompact_atTop (E := ℂ))

open ContinuousLinearMap

/-- Continuous linear map version of the real part function, from `ℂ` to `ℝ`. -/
def reCLM : ℂ →L[ℝ] ℝ :=
  reLm.mkContinuous 1 fun x => by simp [abs_re_le_norm]

@[continuity, fun_prop]
theorem continuous_re : Continuous re :=
  reCLM.continuous

lemma uniformContinuous_re : UniformContinuous re :=
  reCLM.uniformContinuous

@[deprecated (since := "2026-02-03")] alias uniformlyContinuous_re :=
  uniformContinuous_re

@[simp]
theorem reCLM_coe : (reCLM : ℂ →ₗ[ℝ] ℝ) = reLm :=
  rfl

@[simp]
theorem reCLM_apply (z : ℂ) : (reCLM : ℂ → ℝ) z = z.re :=
  rfl

/-- Continuous linear map version of the imaginary part function, from `ℂ` to `ℝ`. -/
def imCLM : ℂ →L[ℝ] ℝ :=
  imLm.mkContinuous 1 fun x => by simp [abs_im_le_norm]

@[continuity, fun_prop]
theorem continuous_im : Continuous im :=
  imCLM.continuous

lemma uniformContinuous_im : UniformContinuous im :=
  imCLM.uniformContinuous

@[deprecated (since := "2026-02-03")] alias uniformlyContinuous_im :=
  uniformContinuous_im

@[simp]
theorem imCLM_coe : (imCLM : ℂ →ₗ[ℝ] ℝ) = imLm :=
  rfl

@[simp]
theorem imCLM_apply (z : ℂ) : (imCLM : ℂ → ℝ) z = z.im :=
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem restrictScalars_toSpanSingleton' (x : E) :
    ContinuousLinearMap.restrictScalars ℝ (toSpanSingleton ℂ x : ℂ →L[ℂ] E) =
      reCLM.smulRight x + I • imCLM.smulRight x := by
  ext ⟨a, b⟩
  simp [map_add, mk_eq_add_mul_I, mul_smul, smul_comm I b x]

theorem restrictScalars_toSpanSingleton (x : ℂ) :
    ContinuousLinearMap.restrictScalars ℝ (toSpanSingleton ℂ x : ℂ →L[ℂ] ℂ) =
    x • (1 : ℂ →L[ℝ] ℂ) := by
  ext1 z
  dsimp
  apply mul_comm

@[deprecated (since := "2025-12-18")] alias restrictScalars_one_smulRight' :=
  restrictScalars_toSpanSingleton'
@[deprecated (since := "2025-12-18")] alias restrictScalars_one_smulRight :=
  restrictScalars_toSpanSingleton

/-- The complex-conjugation function from `ℂ` to itself is an isometric linear equivalence. -/
def conjLIE : ℂ ≃ₗᵢ[ℝ] ℂ :=
  ⟨conjAe.toLinearEquiv, norm_conj⟩

@[simp]
theorem conjLIE_apply (z : ℂ) : conjLIE z = conj z :=
  rfl

@[simp]
theorem conjLIE_symm : conjLIE.symm = conjLIE :=
  rfl

theorem isometry_conj : Isometry (conj : ℂ → ℂ) :=
  conjLIE.isometry

@[simp]
theorem dist_conj_conj (z w : ℂ) : dist (conj z) (conj w) = dist z w :=
  isometry_conj.dist_eq z w

@[simp]
theorem nndist_conj_conj (z w : ℂ) : nndist (conj z) (conj w) = nndist z w :=
  isometry_conj.nndist_eq z w

theorem dist_conj_comm (z w : ℂ) : dist (conj z) w = dist z (conj w) := by
  rw [← dist_conj_conj, conj_conj]

theorem nndist_conj_comm (z w : ℂ) : nndist (conj z) w = nndist z (conj w) :=
  Subtype.ext <| dist_conj_comm _ _

instance : ContinuousStar ℂ :=
  ⟨conjLIE.continuous⟩

@[continuity, fun_prop]
theorem continuous_conj : Continuous (conj : ℂ → ℂ) :=
  continuous_star

/-- The only continuous ring homomorphisms from `ℂ` to `ℂ` are the identity and the complex
conjugation. -/
theorem ringHom_eq_id_or_conj_of_continuous {f : ℂ →+* ℂ} (hf : Continuous f) :
    f = RingHom.id ℂ ∨ f = conj := by
  simpa only [DFunLike.ext_iff] using real_algHom_eq_id_or_conj (AlgHom.mk' f (map_real_smul f hf))

/-- The complex-conjugation function from `ℂ` to itself is a continuous `ℝ`-algebra isomorphism. -/
def conjCAE : ℂ ≃A[ℝ] ℂ := { conjAe, conjLIE.toContinuousLinearEquiv with }

/-- Continuous linear equiv version of the conj function, from `ℂ` to `ℂ`.

This is an abbreviation for `conjCAE` coerced to a continuous linear map. -/
abbrev conjCLE : ℂ ≃L[ℝ] ℂ := conjCAE.toContinuousLinearEquiv

@[simp] lemma conjLIE_toCLE : conjLIE.toContinuousLinearEquiv = conjCLE := rfl

@[simp]
theorem conjCAE_toAlgEquiv : conjCAE.toAlgEquiv = conjAe :=
  rfl

@[simp] theorem conjCLE_toLinearEquiv : conjCLE.toLinearEquiv = conjAe.toLinearEquiv :=
  rfl

@[simp] lemma conjCLE_coe_toLinearMap :
    (conjCLE : ℂ →ₗ[ℝ] ℂ) = conjAe.toLinearMap :=
  rfl

@[simp]
theorem conjCAE_apply (z : ℂ) : conjCAE z = conj z :=
  rfl

-- simp tag not needed because conjCLE is `abbrev`
theorem conjCLE_apply (z : ℂ) : conjCLE z = conj z :=
  rfl

@[simp] lemma conjCAE_toLinearMap : conjCAE.toLinearMap = conjAe.toLinearMap := rfl

/-- Linear isometry version of the canonical embedding of `ℝ` in `ℂ`. -/
def ofRealLI : ℝ →ₗᵢ[ℝ] ℂ :=
  ⟨ofRealAm.toLinearMap, norm_real⟩

@[simp]
theorem ofRealLI_apply (x : ℝ) : ofRealLI x = x := rfl

theorem isometry_ofReal : Isometry ((↑) : ℝ → ℂ) :=
  ofRealLI.isometry

@[continuity, fun_prop]
theorem continuous_ofReal : Continuous ((↑) : ℝ → ℂ) :=
  ofRealLI.continuous

theorem isUniformEmbedding_ofReal : IsUniformEmbedding ((↑) : ℝ → ℂ) :=
  ofRealLI.isometry.isUniformEmbedding

lemma _root_.RCLike.isUniformEmbedding_ofReal {𝕜 : Type*} [RCLike 𝕜] :
    IsUniformEmbedding ((↑) : ℝ → 𝕜) :=
  RCLike.ofRealLI.isometry.isUniformEmbedding

theorem _root_.Filter.tendsto_ofReal_iff {α : Type*} {l : Filter α} {f : α → ℝ} {x : ℝ} :
    Tendsto (fun x ↦ (f x : ℂ)) l (𝓝 (x : ℂ)) ↔ Tendsto f l (𝓝 x) :=
  isUniformEmbedding_ofReal.isClosedEmbedding.tendsto_nhds_iff.symm

lemma _root_.Filter.tendsto_ofReal_iff' {α 𝕜 : Type*} [RCLike 𝕜]
    {l : Filter α} {f : α → ℝ} {x : ℝ} :
    Tendsto (fun x ↦ (f x : 𝕜)) l (𝓝 (x : 𝕜)) ↔ Tendsto f l (𝓝 x) :=
  RCLike.isUniformEmbedding_ofReal.isClosedEmbedding.tendsto_nhds_iff.symm

lemma _root_.Filter.Tendsto.ofReal {α : Type*} {l : Filter α} {f : α → ℝ} {x : ℝ}
    (hf : Tendsto f l (𝓝 x)) : Tendsto (fun x ↦ (f x : ℂ)) l (𝓝 (x : ℂ)) :=
  tendsto_ofReal_iff.mpr hf

/-- The only continuous ring homomorphism from `ℝ` to `ℂ` is the identity. -/
theorem ringHom_eq_ofReal_of_continuous {f : ℝ →+* ℂ} (h : Continuous f) : f = ofRealHom := by
  convert congr_arg AlgHom.toRingHom <| Subsingleton.elim (AlgHom.mk' f <| map_real_smul f h)
    (Algebra.ofId ℝ ℂ)

/-- Continuous linear map version of the canonical embedding of `ℝ` in `ℂ`. -/
def ofRealCLM : ℝ →L[ℝ] ℂ :=
  ofRealLI.toContinuousLinearMap

@[simp]
theorem ofRealCLM_coe : (ofRealCLM : ℝ →ₗ[ℝ] ℂ) = ofRealAm.toLinearMap :=
  rfl

@[simp]
theorem ofRealCLM_apply (x : ℝ) : ofRealCLM x = x :=
  rfl

noncomputable instance : RCLike ℂ where
  re := ⟨⟨Complex.re, Complex.zero_re⟩, Complex.add_re⟩
  im := ⟨⟨Complex.im, Complex.zero_im⟩, Complex.add_im⟩
  I := Complex.I
  I_re_ax := I_re
  I_mul_I_ax := .inr Complex.I_mul_I
  re_add_im_ax := re_add_im
  ofReal_re_ax := ofReal_re
  ofReal_im_ax := ofReal_im
  mul_re_ax := mul_re
  mul_im_ax := mul_im
  conj_re_ax _ := rfl
  conj_im_ax _ := rfl
  conj_I_ax := conj_I
  norm_sq_eq_def_ax z := (normSq_eq_norm_sq z).symm
  mul_im_I_ax _ := mul_one _
  toPartialOrder := Complex.partialOrder
  le_iff_re_im := Iff.rfl

theorem _root_.RCLike.re_eq_complex_re : ⇑(RCLike.re : ℂ →+ ℝ) = Complex.re :=
  rfl

theorem _root_.RCLike.im_eq_complex_im : ⇑(RCLike.im : ℂ →+ ℝ) = Complex.im :=
  rfl

theorem _root_.RCLike.ofReal_eq_complex_ofReal : (RCLike.ofReal : ℝ → ℂ) = Complex.ofReal := rfl

-- TODO: Replace `mul_conj` and `conj_mul` once `norm` has replaced `abs`
lemma mul_conj' (z : ℂ) : z * conj z = ‖z‖ ^ 2 := RCLike.mul_conj z
lemma conj_mul' (z : ℂ) : conj z * z = ‖z‖ ^ 2 := RCLike.conj_mul z

lemma inv_eq_conj (hz : ‖z‖ = 1) : z⁻¹ = conj z := RCLike.inv_eq_conj hz

lemma exists_norm_eq_mul_self (z : ℂ) : ∃ c, ‖c‖ = 1 ∧ ‖z‖ = c * z :=
  RCLike.exists_norm_eq_mul_self _

lemma exists_norm_mul_eq_self (z : ℂ) : ∃ c, ‖c‖ = 1 ∧ c * ‖z‖ = z :=
  RCLike.exists_norm_mul_eq_self _

lemma im_eq_zero_iff_isSelfAdjoint (x : ℂ) : Complex.im x = 0 ↔ IsSelfAdjoint x := by
  rw [← RCLike.im_eq_complex_im]
  exact RCLike.im_eq_zero_iff_isSelfAdjoint

lemma re_eq_ofReal_of_isSelfAdjoint {x : ℂ} {y : ℝ} (hx : IsSelfAdjoint x) :
    Complex.re x = y ↔ x = y := by
  rw [← RCLike.re_eq_complex_re]
  exact RCLike.re_eq_ofReal_of_isSelfAdjoint hx

lemma ofReal_eq_re_of_isSelfAdjoint {x : ℂ} {y : ℝ} (hx : IsSelfAdjoint x) :
    y = Complex.re x ↔ y = x := by
  rw [← RCLike.re_eq_complex_re]
  exact RCLike.ofReal_eq_re_of_isSelfAdjoint hx

/-- The natural isomorphism between `𝕜` satisfying `RCLike 𝕜` and `ℂ` when
`RCLike.im RCLike.I = 1`. -/
@[simps]
def _root_.RCLike.complexRingEquiv {𝕜 : Type*} [RCLike 𝕜]
    (h : RCLike.im (RCLike.I : 𝕜) = 1) : 𝕜 ≃+* ℂ where
  toFun x := RCLike.re x + RCLike.im x * I
  invFun x := re x + im x * RCLike.I
  left_inv x := by simp
  right_inv x := by simp [h]
  map_add' x y := by simp only [map_add, ofReal_add]; ring
  map_mul' x y := by
    simp only [RCLike.mul_re, ofReal_sub, ofReal_mul, RCLike.mul_im, ofReal_add]
    ring_nf
    rw [I_sq]
    ring

open scoped ComplexOrder in
theorem _root_.RCLike.map_nonneg_iff {𝕜 𝕜' : Type*} [RCLike 𝕜] [RCLike 𝕜']
    (h : RCLike.im (RCLike.I : 𝕜') = 1) {a : 𝕜} :
    0 ≤ RCLike.map 𝕜 𝕜' a ↔ 0 ≤ a := by
  rw [RCLike.nonneg_iff, RCLike.nonneg_iff (K := 𝕜)]
  simp [h]

open scoped ComplexOrder in
@[simp] theorem _root_.RCLike.to_complex_nonneg_iff {𝕜 : Type*} [RCLike 𝕜] {a : 𝕜} :
    0 ≤ RCLike.re a + RCLike.im a * Complex.I ↔ 0 ≤ a := RCLike.map_nonneg_iff I_im

set_option backward.isDefEq.respectTransparency false in
/-- The natural `ℝ`-linear isometry equivalence between `𝕜` satisfying `RCLike 𝕜` and `ℂ` when
`RCLike.im RCLike.I = 1`. -/
@[simps]
def _root_.RCLike.complexLinearIsometryEquiv {𝕜 : Type*} [RCLike 𝕜]
    (h : RCLike.im (RCLike.I : 𝕜) = 1) : 𝕜 ≃ₗᵢ[ℝ] ℂ where
  map_smul' _ _ := by simp [RCLike.smul_re, RCLike.smul_im, ofReal_mul]; ring
  norm_map' _ := by
    rw [← sq_eq_sq₀ (by positivity) (by positivity), ← normSq_eq_norm_sq, ← RCLike.normSq_eq_def',
      RCLike.normSq_apply]
    simp [normSq_add]
  __ := RCLike.complexRingEquiv h

@[simp] theorem _root_.RCLike.toContinuousLinearMap_complexLinearIsometryEquiv
    {𝕜 : Type*} [RCLike 𝕜] (h : RCLike.im (RCLike.I : 𝕜) = 1) :
    (RCLike.complexLinearIsometryEquiv h : 𝕜 →L[ℝ] ℂ) = RCLike.map 𝕜 ℂ := rfl

@[simp] theorem _root_.RCLike.norm_to_complex {𝕜 : Type*} [RCLike 𝕜] (a : 𝕜) :
    ‖RCLike.re a + RCLike.im a * Complex.I‖ = ‖a‖ := by
  obtain (h | h) := RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜)
  · rw [← RCLike.re_add_im a, RCLike.im_eq_zero h]
    simp
  exact (RCLike.complexLinearIsometryEquiv h).norm_map a

theorem isometry_intCast : Isometry ((↑) : ℤ → ℂ) :=
  Isometry.of_dist_eq <| by simp_rw [← Complex.ofReal_intCast,
    Complex.isometry_ofReal.dist_eq, Int.dist_cast_real, implies_true]

theorem isClosedEmbedding_intCast : IsClosedEmbedding ((↑) : ℤ → ℂ) :=
  isometry_intCast.isClosedEmbedding

@[deprecated (since := "2026-04-15")] alias closedEmbedding_intCast := isClosedEmbedding_intCast

lemma isClosed_range_intCast : IsClosed (Set.range ((↑) : ℤ → ℂ)) :=
  Complex.isClosedEmbedding_intCast.isClosed_range

lemma isOpen_compl_range_intCast : IsOpen (Set.range ((↑) : ℤ → ℂ))ᶜ :=
  Complex.isClosed_range_intCast.isOpen_compl

section ComplexOrder

open ComplexOrder

theorem eq_coe_norm_of_nonneg {z : ℂ} (hz : 0 ≤ z) : z = ↑‖z‖ := by
  lift z to ℝ using hz.2.symm
  rw [norm_real, Real.norm_of_nonneg (id hz.1 : 0 ≤ z)]

/-- We show that the partial order and the topology on `ℂ` are compatible.
We turn this into an instance scoped to `ComplexOrder`. -/
lemma orderClosedTopology : OrderClosedTopology ℂ := RCLike.instOrderClosedTopology

scoped[ComplexOrder] attribute [instance] Complex.orderClosedTopology

theorem norm_of_nonneg' {x : ℂ} (hx : 0 ≤ x) : ‖x‖ = x := by
  rw [← RCLike.ofReal_eq_complex_ofReal]
  exact RCLike.norm_of_nonneg' hx

lemma re_nonneg_iff_nonneg {x : ℂ} (hx : IsSelfAdjoint x) : 0 ≤ re x ↔ 0 ≤ x := by
  rw [← RCLike.re_eq_complex_re]
  exact RCLike.re_nonneg_of_nonneg hx

@[gcongr]
lemma re_le_re {x y : ℂ} (h : x ≤ y) : re x ≤ re y := by
  rw [RCLike.le_iff_re_im] at h
  exact h.1

end ComplexOrder

end Complex

namespace RCLike

open ComplexConjugate

local notation "reC" => @RCLike.re ℂ _
local notation "imC" => @RCLike.im ℂ _
local notation "IC" => @RCLike.I ℂ _
local notation "norm_sqC" => @RCLike.normSq ℂ _

@[simp]
theorem re_to_complex {x : ℂ} : reC x = x.re :=
  rfl

@[simp]
theorem im_to_complex {x : ℂ} : imC x = x.im :=
  rfl

@[simp]
theorem I_to_complex : IC = Complex.I :=
  rfl

@[simp]
theorem normSq_to_complex {x : ℂ} : norm_sqC x = Complex.normSq x :=
  rfl

section tsum

variable {α : Type*} (𝕜 : Type*) [RCLike 𝕜] {L : SummationFilter α}

@[simp]
theorem hasSum_conj {f : α → 𝕜} {x : 𝕜} : HasSum (fun x => conj (f x)) x L ↔ HasSum f (conj x) L :=
  conjCLE.hasSum

theorem hasSum_conj' {f : α → 𝕜} {x : 𝕜} : HasSum (fun x => conj (f x)) (conj x) L ↔ HasSum f x L :=
  conjCLE.hasSum'

@[simp]
theorem summable_conj {f : α → 𝕜} : Summable (fun x => conj (f x)) L ↔ Summable f L :=
  summable_star_iff

variable {𝕜} in
theorem conj_tsum (f : α → 𝕜) : conj (∑'[L] a, f a) = ∑'[L] a, conj (f a) :=
  tsum_star

@[simp, norm_cast]
theorem hasSum_ofReal {f : α → ℝ} {x : ℝ} : HasSum (fun x => (f x : 𝕜)) x L ↔ HasSum f x L :=
  ⟨fun h => by simpa only [RCLike.reCLM_apply, RCLike.ofReal_re] using reCLM.hasSum h,
    ofRealCLM.hasSum⟩

@[simp, norm_cast]
theorem summable_ofReal {f : α → ℝ} : Summable (fun x => (f x : 𝕜)) L ↔ Summable f L :=
  ⟨fun h => by simpa only [RCLike.reCLM_apply, RCLike.ofReal_re] using reCLM.summable h,
    ofRealCLM.summable⟩

@[norm_cast]
theorem ofReal_tsum (f : α → ℝ) : (↑(∑'[L] a, f a) : 𝕜) = ∑'[L] a, (f a : 𝕜) :=
  Function.LeftInverse.map_tsum f ofRealCLM.continuous continuous_re (fun _ ↦ by simp)

theorem hasSum_re {f : α → 𝕜} {x : 𝕜} (h : HasSum f x L) : HasSum (fun x => re (f x)) (re x) L :=
  reCLM.hasSum h

theorem hasSum_im {f : α → 𝕜} {x : 𝕜} (h : HasSum f x L) : HasSum (fun x => im (f x)) (im x) L :=
  imCLM.hasSum h

theorem re_tsum [L.NeBot] {f : α → 𝕜} (h : Summable f L) : re (∑'[L] a, f a) = ∑'[L] a, re (f a) :=
  reCLM.map_tsum h

theorem im_tsum [L.NeBot] {f : α → 𝕜} (h : Summable f L) : im (∑'[L] a, f a) = ∑'[L] a, im (f a) :=
  imCLM.map_tsum h

variable {𝕜}

theorem hasSum_iff (f : α → 𝕜) (c : 𝕜) :
    HasSum f c L ↔ HasSum (fun x => re (f x)) (re c) L ∧ HasSum (fun x => im (f x)) (im c) L := by
  refine ⟨fun h => ⟨hasSum_re _ h, hasSum_im _ h⟩, ?_⟩
  rintro ⟨h₁, h₂⟩
  simpa only [re_add_im] using
    ((hasSum_ofReal 𝕜).mpr h₁).add (((hasSum_ofReal 𝕜).mpr h₂).mul_right I)

end tsum

end RCLike

namespace Complex

/-!
We have to repeat the lemmas about `RCLike.re` and `RCLike.im` as they are not syntactic
matches for `Complex.re` and `Complex.im`.

We do not have this problem with `ofReal` and `conj`, although we repeat them anyway for
discoverability and to avoid the need to unify `𝕜`.
-/


section tsum

variable {α : Type*} {L : SummationFilter α}

open ComplexConjugate

theorem hasSum_conj {f : α → ℂ} {x : ℂ} : HasSum (fun x => conj (f x)) x L ↔ HasSum f (conj x) L :=
  RCLike.hasSum_conj _

theorem hasSum_conj' {f : α → ℂ} {x : ℂ} : HasSum (fun x => conj (f x)) (conj x) L ↔ HasSum f x L :=
  RCLike.hasSum_conj' _

theorem summable_conj {f : α → ℂ} : (Summable fun x => conj (f x)) ↔ Summable f :=
  RCLike.summable_conj _

theorem conj_tsum (f : α → ℂ) : conj (∑'[L] a, f a) = ∑'[L] a, conj (f a) :=
  RCLike.conj_tsum _

@[simp, norm_cast]
theorem hasSum_ofReal {f : α → ℝ} {x : ℝ} : HasSum (fun x => (f x : ℂ)) x L ↔ HasSum f x L :=
  RCLike.hasSum_ofReal _

@[simp, norm_cast]
theorem summable_ofReal {f : α → ℝ} : (Summable (fun x => (f x : ℂ)) L) ↔ Summable f L :=
  RCLike.summable_ofReal _

@[norm_cast]
theorem ofReal_tsum (f : α → ℝ) : (↑(∑'[L] a, f a) : ℂ) = ∑'[L] a, ↑(f a) :=
  RCLike.ofReal_tsum _ _

theorem hasSum_re {f : α → ℂ} {x : ℂ} (h : HasSum f x L) : HasSum (fun x => (f x).re) x.re L :=
  RCLike.hasSum_re ℂ h

theorem hasSum_im {f : α → ℂ} {x : ℂ} (h : HasSum f x L) : HasSum (fun x => (f x).im) x.im L :=
  RCLike.hasSum_im ℂ h

theorem re_tsum [L.NeBot] {f : α → ℂ} (h : Summable f L) : (∑'[L] a, f a).re = ∑'[L] a, (f a).re :=
  RCLike.re_tsum _ h

theorem im_tsum [L.NeBot] {f : α → ℂ} (h : Summable f L) : (∑'[L] a, f a).im = ∑'[L] a, (f a).im :=
  RCLike.im_tsum _ h

theorem hasSum_iff (f : α → ℂ) (c : ℂ) :
    HasSum f c L ↔ HasSum (fun x => (f x).re) c.re L ∧ HasSum (fun x => (f x).im) c.im L :=
  RCLike.hasSum_iff _ _

end tsum

section slitPlane

/-!
### Define the "slit plane" `ℂ ∖ ℝ≤0` and provide some API
-/

open scoped ComplexOrder

/-- The *slit plane* is the complex plane with the closed negative real axis removed. -/
def slitPlane : Set ℂ := {z | 0 < z.re ∨ z.im ≠ 0}

lemma mem_slitPlane_iff {z : ℂ} : z ∈ slitPlane ↔ 0 < z.re ∨ z.im ≠ 0 := Set.mem_setOf

/- If `z` is non-zero, then either `z` or `-z` is in `slitPlane`. -/
lemma mem_slitPlane_or_neg_mem_slitPlane {z : ℂ} (hz : z ≠ 0) :
    z ∈ slitPlane ∨ -z ∈ slitPlane := by
  rw [mem_slitPlane_iff, mem_slitPlane_iff]
  rw [ne_eq, Complex.ext_iff] at hz
  push Not at hz
  simp_all only [ne_eq, zero_re, zero_im, neg_re, Left.neg_pos_iff, neg_im, neg_eq_zero]
  by_contra! contra
  exact hz (le_antisymm contra.1.1 contra.2.1) contra.1.2

lemma slitPlane_eq_union : slitPlane = {z | 0 < z.re} ∪ {z | z.im ≠ 0} := Set.setOf_or.symm

lemma isOpen_slitPlane : IsOpen slitPlane :=
  (isOpen_lt continuous_const continuous_re).union (isOpen_ne_fun continuous_im continuous_const)

@[simp]
lemma ofReal_mem_slitPlane {x : ℝ} : ↑x ∈ slitPlane ↔ 0 < x := by simp [mem_slitPlane_iff]

@[simp]
lemma neg_ofReal_mem_slitPlane {x : ℝ} : -↑x ∈ slitPlane ↔ x < 0 := by
  simpa using ofReal_mem_slitPlane (x := -x)

@[simp] lemma one_mem_slitPlane : 1 ∈ slitPlane := ofReal_mem_slitPlane.2 one_pos

@[simp]
lemma zero_notMem_slitPlane : 0 ∉ slitPlane := mt ofReal_mem_slitPlane.1 (lt_irrefl _)

@[simp]
lemma natCast_mem_slitPlane {n : ℕ} : ↑n ∈ slitPlane ↔ n ≠ 0 := by
  simpa [pos_iff_ne_zero] using @ofReal_mem_slitPlane n

@[simp]
lemma ofNat_mem_slitPlane (n : ℕ) [n.AtLeastTwo] : ofNat(n) ∈ slitPlane :=
  natCast_mem_slitPlane.2 (NeZero.ne n)

lemma mem_slitPlane_iff_not_le_zero {z : ℂ} : z ∈ slitPlane ↔ ¬z ≤ 0 :=
  mem_slitPlane_iff.trans not_le_zero_iff.symm

protected lemma compl_Iic_zero : (Set.Iic 0)ᶜ = slitPlane := Set.ext fun _ ↦
  mem_slitPlane_iff_not_le_zero.symm

lemma slitPlane_ne_zero {z : ℂ} (hz : z ∈ slitPlane) : z ≠ 0 :=
  ne_of_mem_of_not_mem hz zero_notMem_slitPlane

/-- The slit plane includes the open unit ball of radius `1` around `1`. -/
lemma ball_one_subset_slitPlane : Metric.ball 1 1 ⊆ slitPlane := by
  intro z hz
  apply Or.inl
  simpa using (re_le_norm _).trans_lt (mem_ball_iff_norm'.1 hz)

/-- The slit plane includes the open unit ball of radius `1` around `1`. -/
lemma mem_slitPlane_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) : 1 + z ∈ slitPlane :=
  ball_one_subset_slitPlane <| by simpa

open Metric in
/-- A subset of the circle centered at the origin in `ℂ` of radius `r` is a subset of
the `slitPlane` if it does not contain `-r`. -/
lemma subset_slitPlane_iff_of_subset_sphere {r : ℝ} {s : Set ℂ} (hs : s ⊆ sphere 0 r) :
    s ⊆ slitPlane ↔ (-r : ℂ) ∉ s := by
  simp_rw [Set.subset_def, mem_slitPlane_iff_not_le_zero]
  contrapose!
  refine ⟨?_, fun hr ↦ ⟨_, hr, by simpa using hs hr⟩⟩
  rintro ⟨z, hzs, hz⟩
  have : ‖z‖ = r := by simpa using hs hzs
  simpa [← this, ← norm_neg z ▸ eq_coe_norm_of_nonneg (neg_nonneg.mpr hz)]

end slitPlane

lemma _root_.IsCompact.reProdIm {s t : Set ℝ} (hs : IsCompact s) (ht : IsCompact t) :
    IsCompact (s ×ℂ t) :=
  equivRealProdCLM.toHomeomorph.isCompact_preimage.2 (hs.prod ht)

end Complex

section realPart_imaginaryPart

variable {A : Type*} [SeminormedAddCommGroup A] [StarAddMonoid A] [NormedSpace ℂ A] [StarModule ℂ A]
  [NormedStarGroup A]

lemma realPart.norm_le (x : A) : ‖realPart x‖ ≤ ‖x‖ := by
  rw [← inv_mul_cancel_left₀ two_ne_zero ‖x‖, ← AddSubgroup.norm_coe, realPart_apply_coe,
    norm_smul, norm_inv, Real.norm_ofNat]
  gcongr
  exact norm_add_le _ _ |>.trans <| by simp [two_mul]

lemma imaginaryPart.norm_le (x : A) : ‖imaginaryPart x‖ ≤ ‖x‖ := by
  calc ‖imaginaryPart x‖ = ‖realPart (Complex.I • (-x))‖ := by simp
    _ ≤ ‖x‖ := by simpa only [smul_neg, map_neg, realPart_I_smul, neg_neg,
        AddSubgroupClass.coe_norm, norm_neg, norm_smul, Complex.norm_I, one_mul] using
        realPart.norm_le (Complex.I • (-x))

end realPart_imaginaryPart
