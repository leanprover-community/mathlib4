/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Data.Complex.Module
import Mathlib.Data.Complex.Order
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Instances.RealVectorSpace

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


assert_not_exists Absorbs

noncomputable section

namespace Complex
variable {z : ℂ}

open ComplexConjugate Topology Filter

instance : Norm ℂ :=
  ⟨abs⟩

@[simp]
theorem norm_eq_abs (z : ℂ) : ‖z‖ = abs z :=
  rfl

lemma norm_I : ‖I‖ = 1 := abs_I

theorem norm_exp_ofReal_mul_I (t : ℝ) : ‖exp (t * I)‖ = 1 := by
  simp only [norm_eq_abs, abs_exp_ofReal_mul_I]

instance instNormedAddCommGroup : NormedAddCommGroup ℂ :=
  AddGroupNorm.toNormedAddCommGroup
    { abs with
      map_zero' := map_zero abs
      neg' := abs.map_neg
      eq_zero_of_map_eq_zero' := fun _ => abs.eq_zero.1 }

instance : NormedField ℂ where
  dist_eq _ _ := rfl
  norm_mul' := map_mul abs

instance : DenselyNormedField ℂ where
  lt_norm_lt r₁ r₂ h₀ hr :=
    let ⟨x, h⟩ := exists_between hr
    ⟨x, by rwa [norm_eq_abs, abs_ofReal, abs_of_pos (h₀.trans_lt h.1)]⟩

instance {R : Type*} [NormedField R] [NormedAlgebra R ℝ] : NormedAlgebra R ℂ where
  norm_smul_le r x := by
    rw [← algebraMap_smul ℝ r x, real_smul, norm_mul, norm_eq_abs, abs_ofReal, ← Real.norm_eq_abs,
      norm_algebraMap']

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

@[simp] lemma nnnorm_I : ‖I‖₊ = 1 := by simp [nnnorm]

theorem dist_eq (z w : ℂ) : dist z w = abs (z - w) :=
  rfl

theorem dist_eq_re_im (z w : ℂ) : dist z w = √((z.re - w.re) ^ 2 + (z.im - w.im) ^ 2) := by
  rw [sq, sq]
  rfl

@[simp]
theorem dist_mk (x₁ y₁ x₂ y₂ : ℝ) :
    dist (mk x₁ y₁) (mk x₂ y₂) = √((x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2) :=
  dist_eq_re_im _ _

theorem dist_of_re_eq {z w : ℂ} (h : z.re = w.re) : dist z w = dist z.im w.im := by
  rw [dist_eq_re_im, h, sub_self, zero_pow two_ne_zero, zero_add, Real.sqrt_sq_eq_abs, Real.dist_eq]

theorem nndist_of_re_eq {z w : ℂ} (h : z.re = w.re) : nndist z w = nndist z.im w.im :=
  NNReal.eq <| dist_of_re_eq h

theorem edist_of_re_eq {z w : ℂ} (h : z.re = w.re) : edist z w = edist z.im w.im := by
  rw [edist_nndist, edist_nndist, nndist_of_re_eq h]

theorem dist_of_im_eq {z w : ℂ} (h : z.im = w.im) : dist z w = dist z.re w.re := by
  rw [dist_eq_re_im, h, sub_self, zero_pow two_ne_zero, add_zero, Real.sqrt_sq_eq_abs, Real.dist_eq]

theorem nndist_of_im_eq {z w : ℂ} (h : z.im = w.im) : nndist z w = nndist z.re w.re :=
  NNReal.eq <| dist_of_im_eq h

theorem edist_of_im_eq {z w : ℂ} (h : z.im = w.im) : edist z w = edist z.re w.re := by
  rw [edist_nndist, edist_nndist, nndist_of_im_eq h]

theorem dist_conj_self (z : ℂ) : dist (conj z) z = 2 * |z.im| := by
  rw [dist_of_re_eq (conj_re z), conj_im, dist_comm, Real.dist_eq, sub_neg_eq_add, ← two_mul,
    _root_.abs_mul, abs_of_pos (zero_lt_two' ℝ)]

theorem nndist_conj_self (z : ℂ) : nndist (conj z) z = 2 * Real.nnabs z.im :=
  NNReal.eq <| by rw [← dist_nndist, NNReal.coe_mul, NNReal.coe_two, Real.coe_nnabs, dist_conj_self]

theorem dist_self_conj (z : ℂ) : dist z (conj z) = 2 * |z.im| := by rw [dist_comm, dist_conj_self]

theorem nndist_self_conj (z : ℂ) : nndist z (conj z) = 2 * Real.nnabs z.im := by
  rw [nndist_comm, nndist_conj_self]

@[simp 1100]
theorem comap_abs_nhds_zero : comap abs (𝓝 0) = 𝓝 0 :=
  comap_norm_nhds_zero

@[simp 1100, norm_cast] lemma norm_real (r : ℝ) : ‖(r : ℂ)‖ = ‖r‖ := abs_ofReal _
@[simp, norm_cast] lemma nnnorm_real (r : ℝ) : ‖(r : ℂ)‖₊ = ‖r‖₊ := by ext; exact norm_real _

@[simp 1100, norm_cast] lemma norm_natCast (n : ℕ) : ‖(n : ℂ)‖ = n := abs_natCast _
@[simp 1100, norm_cast] lemma norm_intCast (n : ℤ) : ‖(n : ℂ)‖ = |(n : ℝ)| := abs_intCast n
@[simp 1100, norm_cast] lemma norm_ratCast (q : ℚ) : ‖(q : ℂ)‖ = |(q : ℝ)| := norm_real _

@[simp 1100, norm_cast] lemma nnnorm_natCast (n : ℕ) : ‖(n : ℂ)‖₊ = n := Subtype.ext <| by simp
@[simp 1100, norm_cast] lemma nnnorm_intCast (n : ℤ) : ‖(n : ℂ)‖₊ = ‖n‖₊ := by
  ext; exact norm_intCast n
@[simp 1100, norm_cast] lemma nnnorm_ratCast (q : ℚ) : ‖(q : ℂ)‖₊ = ‖(q : ℝ)‖₊ := nnnorm_real q

@[simp 1100] lemma norm_ofNat (n : ℕ) [n.AtLeastTwo] :
    ‖(no_index (OfNat.ofNat n) : ℂ)‖ = OfNat.ofNat n := norm_natCast n

@[simp 1100] lemma nnnorm_ofNat (n : ℕ) [n.AtLeastTwo] :
    ‖(no_index (OfNat.ofNat n) : ℂ)‖₊ = OfNat.ofNat n := nnnorm_natCast n

@[deprecated (since := "2024-08-25")] alias norm_nat := norm_natCast
@[deprecated (since := "2024-08-25")] alias norm_int := norm_intCast
@[deprecated (since := "2024-08-25")] alias norm_rat := norm_ratCast
@[deprecated (since := "2024-08-25")] alias nnnorm_nat := nnnorm_natCast
@[deprecated (since := "2024-08-25")] alias nnnorm_int := nnnorm_intCast

@[simp 1100, norm_cast]
lemma norm_nnratCast (q : ℚ≥0) : ‖(q : ℂ)‖ = q := abs_of_nonneg q.cast_nonneg

@[simp 1100, norm_cast]
lemma nnnorm_nnratCast (q : ℚ≥0) : ‖(q : ℂ)‖₊ = q := by simp [nnnorm, -norm_eq_abs]

theorem norm_int_of_nonneg {n : ℤ} (hn : 0 ≤ n) : ‖(n : ℂ)‖ = n := by
  rw [norm_intCast, ← Int.cast_abs, _root_.abs_of_nonneg hn]

lemma normSq_eq_norm_sq (z : ℂ) : normSq z = ‖z‖ ^ 2 := by
  rw [normSq_eq_abs, norm_eq_abs]

@[continuity]
theorem continuous_abs : Continuous abs :=
  continuous_norm

@[continuity]
theorem continuous_normSq : Continuous normSq := by
  simpa [← normSq_eq_abs] using continuous_abs.pow 2


theorem nnnorm_eq_one_of_pow_eq_one {ζ : ℂ} {n : ℕ} (h : ζ ^ n = 1) (hn : n ≠ 0) : ‖ζ‖₊ = 1 :=
  (pow_left_inj zero_le' zero_le' hn).1 <| by rw [← nnnorm_pow, h, nnnorm_one, one_pow]

theorem norm_eq_one_of_pow_eq_one {ζ : ℂ} {n : ℕ} (h : ζ ^ n = 1) (hn : n ≠ 0) : ‖ζ‖ = 1 :=
  congr_arg Subtype.val (nnnorm_eq_one_of_pow_eq_one h hn)

lemma le_of_eq_sum_of_eq_sum_norm {ι : Type*} {a b : ℝ} (f : ι → ℂ) (s : Finset ι) (ha₀ : 0 ≤ a)
    (ha : a = ∑ i ∈ s, f i) (hb : b = ∑ i ∈ s, (‖f i‖ : ℂ)) : a ≤ b := by
  norm_cast at hb; rw [← Complex.abs_of_nonneg ha₀, ha, hb]; exact norm_sum_le s f

theorem equivRealProd_apply_le (z : ℂ) : ‖equivRealProd z‖ ≤ abs z := by
  simp [Prod.norm_def, abs_re_le_abs, abs_im_le_abs]

theorem equivRealProd_apply_le' (z : ℂ) : ‖equivRealProd z‖ ≤ 1 * abs z := by
  simpa using equivRealProd_apply_le z

theorem lipschitz_equivRealProd : LipschitzWith 1 equivRealProd := by
  simpa using AddMonoidHomClass.lipschitz_of_bound equivRealProdLm 1 equivRealProd_apply_le'

theorem antilipschitz_equivRealProd : AntilipschitzWith (NNReal.sqrt 2) equivRealProd :=
  AddMonoidHomClass.antilipschitz_of_bound equivRealProdLm fun z ↦ by
    simpa only [Real.coe_sqrt, NNReal.coe_ofNat] using abs_le_sqrt_two_mul_max z

theorem isUniformEmbedding_equivRealProd : IsUniformEmbedding equivRealProd :=
  antilipschitz_equivRealProd.isUniformEmbedding lipschitz_equivRealProd.uniformContinuous

@[deprecated (since := "2024-10-01")]
alias uniformEmbedding_equivRealProd := isUniformEmbedding_equivRealProd

instance : CompleteSpace ℂ :=
  (completeSpace_congr isUniformEmbedding_equivRealProd).mpr inferInstance

instance instT2Space : T2Space ℂ := TopologicalSpace.t2Space_of_metrizableSpace

/-- The natural `ContinuousLinearEquiv` from `ℂ` to `ℝ × ℝ`. -/
@[simps! (config := { simpRhs := true }) apply symm_apply_re symm_apply_im]
def equivRealProdCLM : ℂ ≃L[ℝ] ℝ × ℝ :=
  equivRealProdLm.toContinuousLinearEquivOfBounds 1 (√2) equivRealProd_apply_le' fun p =>
    abs_le_sqrt_two_mul_max (equivRealProd.symm p)

theorem equivRealProdCLM_symm_apply (p : ℝ × ℝ) :
    Complex.equivRealProdCLM.symm p = p.1 + p.2 * Complex.I := Complex.equivRealProd_symm_apply p

instance : ProperSpace ℂ :=
  (id lipschitz_equivRealProd : LipschitzWith 1 equivRealProdCLM.toHomeomorph).properSpace

/-- The `abs` function on `ℂ` is proper. -/
theorem tendsto_abs_cocompact_atTop : Tendsto abs (cocompact ℂ) atTop :=
  tendsto_norm_cocompact_atTop

/-- The `normSq` function on `ℂ` is proper. -/
theorem tendsto_normSq_cocompact_atTop : Tendsto normSq (cocompact ℂ) atTop := by
  simpa [mul_self_abs]
    using tendsto_abs_cocompact_atTop.atTop_mul_atTop tendsto_abs_cocompact_atTop

open ContinuousLinearMap

/-- Continuous linear map version of the real part function, from `ℂ` to `ℝ`. -/
def reCLM : ℂ →L[ℝ] ℝ :=
  reLm.mkContinuous 1 fun x => by simp [abs_re_le_abs]

@[continuity, fun_prop]
theorem continuous_re : Continuous re :=
  reCLM.continuous

lemma uniformlyContinous_re : UniformContinuous re :=
  reCLM.uniformContinuous

@[simp]
theorem reCLM_coe : (reCLM : ℂ →ₗ[ℝ] ℝ) = reLm :=
  rfl

@[simp]
theorem reCLM_apply (z : ℂ) : (reCLM : ℂ → ℝ) z = z.re :=
  rfl

/-- Continuous linear map version of the imaginary part function, from `ℂ` to `ℝ`. -/
def imCLM : ℂ →L[ℝ] ℝ :=
  imLm.mkContinuous 1 fun x => by simp [abs_im_le_abs]

@[continuity, fun_prop]
theorem continuous_im : Continuous im :=
  imCLM.continuous

lemma uniformlyContinous_im : UniformContinuous im :=
  imCLM.uniformContinuous

@[simp]
theorem imCLM_coe : (imCLM : ℂ →ₗ[ℝ] ℝ) = imLm :=
  rfl

@[simp]
theorem imCLM_apply (z : ℂ) : (imCLM : ℂ → ℝ) z = z.im :=
  rfl

theorem restrictScalars_one_smulRight' (x : E) :
    ContinuousLinearMap.restrictScalars ℝ ((1 : ℂ →L[ℂ] ℂ).smulRight x : ℂ →L[ℂ] E) =
      reCLM.smulRight x + I • imCLM.smulRight x := by
  ext ⟨a, b⟩
  simp [map_add, mk_eq_add_mul_I, mul_smul, smul_comm I b x]

theorem restrictScalars_one_smulRight (x : ℂ) :
    ContinuousLinearMap.restrictScalars ℝ ((1 : ℂ →L[ℂ] ℂ).smulRight x : ℂ →L[ℂ] ℂ) =
    x • (1 : ℂ →L[ℝ] ℂ) := by
  ext1 z
  dsimp
  apply mul_comm

/-- The complex-conjugation function from `ℂ` to itself is an isometric linear equivalence. -/
def conjLIE : ℂ ≃ₗᵢ[ℝ] ℂ :=
  ⟨conjAe.toLinearEquiv, abs_conj⟩

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

@[continuity]
theorem continuous_conj : Continuous (conj : ℂ → ℂ) :=
  continuous_star

/-- The only continuous ring homomorphisms from `ℂ` to `ℂ` are the identity and the complex
conjugation. -/
theorem ringHom_eq_id_or_conj_of_continuous {f : ℂ →+* ℂ} (hf : Continuous f) :
    f = RingHom.id ℂ ∨ f = conj := by
  simpa only [DFunLike.ext_iff] using real_algHom_eq_id_or_conj (AlgHom.mk' f (map_real_smul f hf))

/-- Continuous linear equiv version of the conj function, from `ℂ` to `ℂ`. -/
def conjCLE : ℂ ≃L[ℝ] ℂ :=
  conjLIE

@[simp]
theorem conjCLE_coe : conjCLE.toLinearEquiv = conjAe.toLinearEquiv :=
  rfl

@[simp]
theorem conjCLE_apply (z : ℂ) : conjCLE z = conj z :=
  rfl

/-- Linear isometry version of the canonical embedding of `ℝ` in `ℂ`. -/
def ofRealLI : ℝ →ₗᵢ[ℝ] ℂ :=
  ⟨ofRealAm.toLinearMap, norm_real⟩

theorem isometry_ofReal : Isometry ((↑) : ℝ → ℂ) :=
  ofRealLI.isometry

@[continuity, fun_prop]
theorem continuous_ofReal : Continuous ((↑) : ℝ → ℂ) :=
  ofRealLI.continuous

lemma _root_.Filter.Tendsto.ofReal {α : Type*} {l : Filter α} {f : α → ℝ} {x : ℝ}
    (hf : Tendsto f l (𝓝 x)) : Tendsto (fun x ↦ (f x : ℂ)) l (𝓝 (x : ℂ)) :=
  (continuous_ofReal.tendsto _).comp hf

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
  norm_sq_eq_def_ax z := (normSq_eq_abs z).symm
  mul_im_I_ax _ := mul_one _
  toPartialOrder := Complex.partialOrder
  le_iff_re_im := Iff.rfl

theorem _root_.RCLike.re_eq_complex_re : ⇑(RCLike.re : ℂ →+ ℝ) = Complex.re :=
  rfl

theorem _root_.RCLike.im_eq_complex_im : ⇑(RCLike.im : ℂ →+ ℝ) = Complex.im :=
  rfl

-- TODO: Replace `mul_conj` and `conj_mul` once `norm` has replaced `abs`
lemma mul_conj' (z : ℂ) : z * conj z = ‖z‖ ^ 2 := RCLike.mul_conj z
lemma conj_mul' (z : ℂ) : conj z * z = ‖z‖ ^ 2 := RCLike.conj_mul z

lemma inv_eq_conj (hz : ‖z‖ = 1) : z⁻¹ = conj z := RCLike.inv_eq_conj hz

lemma exists_norm_eq_mul_self (z : ℂ) : ∃ c, ‖c‖ = 1 ∧ ‖z‖ = c * z :=
  RCLike.exists_norm_eq_mul_self _

lemma exists_norm_mul_eq_self (z : ℂ) : ∃ c, ‖c‖ = 1 ∧ c * ‖z‖ = z :=
  RCLike.exists_norm_mul_eq_self _

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

/-- The natural `ℝ`-linear isometry equivalence between `𝕜` satisfying `RCLike 𝕜` and `ℂ` when
`RCLike.im RCLike.I = 1`. -/
@[simps]
def _root_.RCLike.complexLinearIsometryEquiv {𝕜 : Type*} [RCLike 𝕜]
    (h : RCLike.im (RCLike.I : 𝕜) = 1) : 𝕜 ≃ₗᵢ[ℝ] ℂ where
  map_smul' _ _ := by simp [RCLike.smul_re, RCLike.smul_im, ofReal_mul]; ring
  norm_map' _ := by
    rw [← sq_eq_sq (by positivity) (by positivity), ← normSq_eq_norm_sq, ← RCLike.normSq_eq_def',
      RCLike.normSq_apply]
    simp [normSq_add]
  __ := RCLike.complexRingEquiv h

theorem closedEmbedding_intCast : ClosedEmbedding ((↑) : ℤ → ℂ) := by
  apply Metric.closedEmbedding_of_pairwise_le_dist zero_lt_one
  convert Int.pairwise_one_le_dist
  simp_rw [dist_eq_norm]
  norm_cast
  rw [Int.norm_eq_abs]
  exact Int.cast_abs

lemma isClosed_range_intCast : IsClosed (Set.range ((↑) : ℤ → ℂ)) :=
  Complex.closedEmbedding_intCast.isClosed_range

lemma isOpen_compl_range_intCast : IsOpen (Set.range ((↑) : ℤ → ℂ))ᶜ :=
  Complex.isClosed_range_intCast.isOpen_compl

section ComplexOrder

open ComplexOrder

theorem eq_coe_norm_of_nonneg {z : ℂ} (hz : 0 ≤ z) : z = ↑‖z‖ := by
  lift z to ℝ using hz.2.symm
  rw [norm_eq_abs, abs_ofReal, _root_.abs_of_nonneg (id hz.1 : 0 ≤ z)]

/-- We show that the partial order and the topology on `ℂ` are compatible.
We turn this into an instance scoped to `ComplexOrder`. -/
lemma orderClosedTopology : OrderClosedTopology ℂ where
  isClosed_le' := by
    simp_rw [le_def, Set.setOf_and]
    refine IsClosed.inter (isClosed_le ?_ ?_) (isClosed_eq ?_ ?_) <;> continuity

scoped[ComplexOrder] attribute [instance] Complex.orderClosedTopology

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

variable {α : Type*} (𝕜 : Type*) [RCLike 𝕜]

@[simp]
theorem hasSum_conj {f : α → 𝕜} {x : 𝕜} : HasSum (fun x => conj (f x)) x ↔ HasSum f (conj x) :=
  conjCLE.hasSum

theorem hasSum_conj' {f : α → 𝕜} {x : 𝕜} : HasSum (fun x => conj (f x)) (conj x) ↔ HasSum f x :=
  conjCLE.hasSum'

@[simp]
theorem summable_conj {f : α → 𝕜} : (Summable fun x => conj (f x)) ↔ Summable f :=
  summable_star_iff

variable {𝕜}

theorem conj_tsum (f : α → 𝕜) : conj (∑' a, f a) = ∑' a, conj (f a) :=
  tsum_star

variable (𝕜)

@[simp, norm_cast]
theorem hasSum_ofReal {f : α → ℝ} {x : ℝ} : HasSum (fun x => (f x : 𝕜)) x ↔ HasSum f x :=
  ⟨fun h => by simpa only [RCLike.reCLM_apply, RCLike.ofReal_re] using reCLM.hasSum h,
    ofRealCLM.hasSum⟩

@[simp, norm_cast]
theorem summable_ofReal {f : α → ℝ} : (Summable fun x => (f x : 𝕜)) ↔ Summable f :=
  ⟨fun h => by simpa only [RCLike.reCLM_apply, RCLike.ofReal_re] using reCLM.summable h,
    ofRealCLM.summable⟩

@[norm_cast]
theorem ofReal_tsum (f : α → ℝ) : (↑(∑' a, f a) : 𝕜) = ∑' a, (f a : 𝕜) := by
  by_cases h : Summable f
  · exact ContinuousLinearMap.map_tsum ofRealCLM h
  · rw [tsum_eq_zero_of_not_summable h,
      tsum_eq_zero_of_not_summable ((summable_ofReal _).not.mpr h), ofReal_zero]

theorem hasSum_re {f : α → 𝕜} {x : 𝕜} (h : HasSum f x) : HasSum (fun x => re (f x)) (re x) :=
  reCLM.hasSum h

theorem hasSum_im {f : α → 𝕜} {x : 𝕜} (h : HasSum f x) : HasSum (fun x => im (f x)) (im x) :=
  imCLM.hasSum h

theorem re_tsum {f : α → 𝕜} (h : Summable f) : re (∑' a, f a) = ∑' a, re (f a) :=
  reCLM.map_tsum h

theorem im_tsum {f : α → 𝕜} (h : Summable f) : im (∑' a, f a) = ∑' a, im (f a) :=
  imCLM.map_tsum h

variable {𝕜}

theorem hasSum_iff (f : α → 𝕜) (c : 𝕜) :
    HasSum f c ↔ HasSum (fun x => re (f x)) (re c) ∧ HasSum (fun x => im (f x)) (im c) := by
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

variable {α : Type*}

open ComplexConjugate

-- Porting note: @[simp] unneeded due to `RCLike.hasSum_conj`
theorem hasSum_conj {f : α → ℂ} {x : ℂ} : HasSum (fun x => conj (f x)) x ↔ HasSum f (conj x) :=
  RCLike.hasSum_conj _

theorem hasSum_conj' {f : α → ℂ} {x : ℂ} : HasSum (fun x => conj (f x)) (conj x) ↔ HasSum f x :=
  RCLike.hasSum_conj' _

-- Porting note: @[simp] unneeded due to `RCLike.summable_conj`
theorem summable_conj {f : α → ℂ} : (Summable fun x => conj (f x)) ↔ Summable f :=
  RCLike.summable_conj _

theorem conj_tsum (f : α → ℂ) : conj (∑' a, f a) = ∑' a, conj (f a) :=
  RCLike.conj_tsum _

@[simp, norm_cast]
theorem hasSum_ofReal {f : α → ℝ} {x : ℝ} : HasSum (fun x => (f x : ℂ)) x ↔ HasSum f x :=
  RCLike.hasSum_ofReal _

@[simp, norm_cast]
theorem summable_ofReal {f : α → ℝ} : (Summable fun x => (f x : ℂ)) ↔ Summable f :=
  RCLike.summable_ofReal _

@[norm_cast]
theorem ofReal_tsum (f : α → ℝ) : (↑(∑' a, f a) : ℂ) = ∑' a, ↑(f a) :=
  RCLike.ofReal_tsum _ _

theorem hasSum_re {f : α → ℂ} {x : ℂ} (h : HasSum f x) : HasSum (fun x => (f x).re) x.re :=
  RCLike.hasSum_re _ h

theorem hasSum_im {f : α → ℂ} {x : ℂ} (h : HasSum f x) : HasSum (fun x => (f x).im) x.im :=
  RCLike.hasSum_im _ h

theorem re_tsum {f : α → ℂ} (h : Summable f) : (∑' a, f a).re = ∑' a, (f a).re :=
  RCLike.re_tsum _ h

theorem im_tsum {f : α → ℂ} (h : Summable f) : (∑' a, f a).im = ∑' a, (f a).im :=
  RCLike.im_tsum _ h

theorem hasSum_iff (f : α → ℂ) (c : ℂ) :
    HasSum f c ↔ HasSum (fun x => (f x).re) c.re ∧ HasSum (fun x => (f x).im) c.im :=
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
lemma zero_not_mem_slitPlane : 0 ∉ slitPlane := mt ofReal_mem_slitPlane.1 (lt_irrefl _)

@[simp]
lemma natCast_mem_slitPlane {n : ℕ} : ↑n ∈ slitPlane ↔ n ≠ 0 := by
  simpa [pos_iff_ne_zero] using @ofReal_mem_slitPlane n

@[deprecated (since := "2024-04-17")]
alias nat_cast_mem_slitPlane := natCast_mem_slitPlane

@[simp]
lemma ofNat_mem_slitPlane (n : ℕ) [n.AtLeastTwo] : no_index (OfNat.ofNat n) ∈ slitPlane :=
  natCast_mem_slitPlane.2 (NeZero.ne n)

lemma mem_slitPlane_iff_not_le_zero {z : ℂ} : z ∈ slitPlane ↔ ¬z ≤ 0 :=
  mem_slitPlane_iff.trans not_le_zero_iff.symm

protected lemma compl_Iic_zero : (Set.Iic 0)ᶜ = slitPlane := Set.ext fun _ ↦
  mem_slitPlane_iff_not_le_zero.symm

lemma slitPlane_ne_zero {z : ℂ} (hz : z ∈ slitPlane) : z ≠ 0 :=
  ne_of_mem_of_not_mem hz zero_not_mem_slitPlane

/-- The slit plane includes the open unit ball of radius `1` around `1`. -/
lemma ball_one_subset_slitPlane : Metric.ball 1 1 ⊆ slitPlane := fun z hz ↦ .inl <|
  have : -1 < z.re - 1 := neg_lt_of_abs_lt <| (abs_re_le_abs _).trans_lt hz
  by linarith

/-- The slit plane includes the open unit ball of radius `1` around `1`. -/
lemma mem_slitPlane_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) : 1 + z ∈ slitPlane :=
  ball_one_subset_slitPlane <| by simpa

end slitPlane

end Complex
