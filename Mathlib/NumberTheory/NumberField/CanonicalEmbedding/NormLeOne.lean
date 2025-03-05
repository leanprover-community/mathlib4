/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.PolarCoord
import Mathlib.NumberTheory.NumberField.Units.Regulator

/-!
# Fundamental Cone: elements of norm ≤ 1

In this file, we study the subset `NormLeOne` of the `fundamentalCone` of elements `x` with
`mixedEmbedding.norm x ≤ 1`.

Mainly, we prove that this is bounded, its frontier has volume zero and compute its volume.

## Strategy of proof

The proof is loosely based on the strategy given in [D. Marcus, *Number Fields*][marcus1977number].
-/

variable (K : Type*) [Field K]

namespace NumberField.mixedEmbedding

open Finset NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem

section normAtAllPlaces

variable {K}

theorem logMap_normAtAllPlaces [NumberField K] (x : mixedSpace K) :
    logMap (mixedSpaceOfRealSpace (normAtAllPlaces x)) = logMap x :=
  logMap_eq_of_normAtPlace_eq
    fun w ↦ by rw [normAtPlace_mixedSpaceOfRealSpace (normAtPlace_nonneg w x)]

theorem norm_normAtAllPlaces [NumberField K] (x : mixedSpace K) :
    mixedEmbedding.norm (mixedSpaceOfRealSpace (normAtAllPlaces x)) = mixedEmbedding.norm x := by
  simp_rw [mixedEmbedding.norm_apply,
    normAtPlace_mixedSpaceOfRealSpace (normAtAllPlaces_nonneg _ _)]

theorem normAtAllPlaces_mem_fundamentalCone_iff [NumberField K] {x : mixedSpace K} :
    mixedSpaceOfRealSpace (normAtAllPlaces x) ∈ fundamentalCone K ↔ x ∈ fundamentalCone K := by
  simp_rw [fundamentalCone, Set.mem_diff, Set.mem_preimage, logMap_normAtAllPlaces,
    Set.mem_setOf_eq, norm_normAtAllPlaces]

end normAtAllPlaces

section normLeOne

variable [NumberField K]

/--
Docstring.
-/
abbrev normLeOne  : Set (mixedSpace K) :=
  {x | x ∈ fundamentalCone K ∧ mixedEmbedding.norm x ≤ 1}

variable {K} in
-- incorporate?
theorem mem_normLeOne_iff (x : mixedSpace K):
    x ∈ normLeOne K ↔ mixedSpaceOfRealSpace (normAtAllPlaces x) ∈ normLeOne K := by
  simp only [normLeOne, Set.mem_setOf_eq, normAtAllPlaces_mem_fundamentalCone_iff,
    norm_normAtAllPlaces]

theorem normLeOne_eq_primeage_image :
    normLeOne K = normAtAllPlaces⁻¹' (normAtAllPlaces '' (normLeOne K)) :=
  mem_iff_normAtAllPlaces_mem_iff.mp fun x ↦ mem_normLeOne_iff x

end normLeOne

namespace NormLeOne

noncomputable section expMap

variable {K}

/--
Docstring.
-/
@[simps]
def expMap_single (w : InfinitePlace K) : PartialHomeomorph ℝ ℝ where
  toFun := fun x ↦ Real.exp ((w.mult : ℝ)⁻¹ * x)
  invFun := fun x ↦ w.mult * Real.log x
  source := Set.univ
  target := Set.Ioi 0
  open_source := isOpen_univ
  open_target := isOpen_Ioi
  map_source' _ _ := Real.exp_pos _
  map_target' _ _ := trivial
  left_inv' _ _ := by simp only [Real.log_exp, mul_inv_cancel_left₀ mult_coe_ne_zero]
  right_inv' _ h := by simp only [inv_mul_cancel_left₀ mult_coe_ne_zero, Real.exp_log h]
  continuousOn_toFun := (continuousOn_const.mul continuousOn_id).rexp
  continuousOn_invFun := continuousOn_const.mul (Real.continuousOn_log.mono (by aesop))

/--
Docstring.
-/
abbrev deriv_expMap_single (w : InfinitePlace K) (x : ℝ) : ℝ :=
  (expMap_single w x) * (w.mult : ℝ)⁻¹

theorem hasDerivAt_expMap_single (w : InfinitePlace K) (x : ℝ) :
    HasDerivAt (expMap_single w) (deriv_expMap_single w x) x := by
  simpa [expMap_single, mul_comm] using
    (HasDerivAt.comp x (Real.hasDerivAt_exp _) (hasDerivAt_mul_const (w.mult : ℝ)⁻¹))

variable [NumberField K]

/--
Docstring.
-/
def expMap : PartialHomeomorph (realSpace K) (realSpace K) := by
  refine PartialHomeomorph.pi fun w ↦ expMap_single w

variable (K)

theorem expMap_source :
    expMap.source = (Set.univ : Set (realSpace K)) := by
  simp_rw [expMap, PartialHomeomorph.pi_toPartialEquiv, PartialEquiv.pi_source, expMap_single,
    Set.pi_univ Set.univ]

theorem expMap_target :
    expMap.target = Set.univ.pi fun (_ : InfinitePlace K) ↦ Set.Ioi 0 := by
  simp_rw [expMap, PartialHomeomorph.pi_toPartialEquiv, PartialEquiv.pi_target, expMap_single]

theorem injective_expMap :
    Function.Injective (expMap : realSpace K → realSpace K) :=
  Set.injective_iff_injOn_univ.mpr ((expMap_source K) ▸ expMap.injOn)

theorem continuous_expMap :
    Continuous (expMap : realSpace K → realSpace K) :=
  continuous_iff_continuousOn_univ.mpr <| (expMap_source K) ▸ expMap.continuousOn

variable {K}

@[simp]
theorem expMap_apply (x : realSpace K) (w : InfinitePlace K) :
    expMap x w = Real.exp ((↑w.mult)⁻¹ * x w) := rfl

@[simp]
theorem expMap_symm_apply (x : realSpace K) (w : InfinitePlace K) :
    expMap.symm x w = ↑w.mult * Real.log (x w) := rfl

theorem logMap_expMap {x : realSpace K}
    (hx : mixedEmbedding.norm (mixedSpaceOfRealSpace (expMap x)) = 1) :
    logMap (mixedSpaceOfRealSpace (expMap x)) = fun w ↦ x w.1 := by
  ext
  rw [logMap, normAtPlace_mixedSpaceOfRealSpace (Real.exp_nonneg _), expMap_apply, Real.log_exp,
    mul_sub, mul_inv_cancel_left₀ mult_coe_ne_zero, hx, Real.log_one, zero_mul, mul_zero, sub_zero]

theorem expMap_pos (x : realSpace K) (w : InfinitePlace K) :
    0 < expMap x w := Real.exp_pos _

theorem expMap_add (x y : realSpace K) :
    expMap (x + y) = expMap x * expMap y := by
  ext
  simp [mul_add, Real.exp_add]

theorem expMap_sum {ι : Type*} (s : Finset ι) (f : ι → realSpace K) :
    expMap (∑ i ∈ s, f i) = ∏ i ∈ s, expMap (f i) := by
  ext
  simp [← Real.exp_sum, ← mul_sum]

theorem expMap_smul (c : ℝ) (x : realSpace K) :
    expMap (c • x) = (expMap x) ^ c := by
  ext
  simp [mul_comm c _, ← mul_assoc, Real.exp_mul]

theorem sum_expMap_symm_apply {x : K} (hx : x ≠ 0) :
    ∑ w : InfinitePlace K, expMap.symm ((normAtAllPlaces (mixedEmbedding K x))) w =
      Real.log (|Algebra.norm ℚ x| : ℚ) := by
  simp_rw [← prod_eq_abs_norm, Real.log_prod _ _ (fun _ _ ↦ pow_ne_zero _ ((map_ne_zero _).mpr hx)),
    Real.log_pow, expMap_symm_apply, normAtAllPlaces_mixedEmbedding]

/--
Docstring.
-/
abbrev fderiv_expMap (x : realSpace K) : realSpace K →L[ℝ] realSpace K :=
  .pi fun w ↦ (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (deriv_expMap_single w (x w))).comp
    (.proj w)

theorem hasFDerivAt_expMap (x : realSpace K): HasFDerivAt expMap (fderiv_expMap x) x := by
  simpa [expMap, fderiv_expMap, hasFDerivAt_pi', PartialHomeomorph.pi_apply,
    ContinuousLinearMap.proj_pi] using
    fun w ↦ (hasDerivAt_expMap_single w _).hasFDerivAt.comp x (hasFDerivAt_apply w x)

end expMap

noncomputable section completeBasis

variable [NumberField K]

variable {K}

open scoped Classical in
/--
Docstring.
-/
def equivFinRank : Fin (rank K) ≃ {w : InfinitePlace K // w ≠ w₀} :=
  Fintype.equivOfCardEq <| by
    rw [Fintype.card_subtype_compl, Fintype.card_ofSubsingleton, Fintype.card_fin, rank]

/--
Docstring.
-/
def realSpaceToLogSpace : realSpace K →ₗ[ℝ] ({w : InfinitePlace K // w ≠ w₀} → ℝ) where
  toFun := fun x w ↦ x w.1 - w.1.mult * (∑ w', x w') * (Module.finrank ℚ K : ℝ)⁻¹
  map_add' := fun _ _ ↦ funext fun _ ↦ by simpa [sum_add_distrib] using by ring
  map_smul' := fun _ _ ↦ funext fun _ ↦ by simpa [← mul_sum] using by ring

theorem realSpaceToLogSpace_apply (x :realSpace K) (w : {w : InfinitePlace K // w ≠ w₀}) :
    realSpaceToLogSpace x w = x w - w.1.mult * (∑ w', x w') * (Module.finrank ℚ K : ℝ)⁻¹ := rfl

theorem realSpaceToLogSpace_expMap_symm {x : K} (hx : x ≠ 0) :
    realSpaceToLogSpace (expMap.symm (normAtAllPlaces (mixedEmbedding K x))) =
      logMap (mixedEmbedding K x) := by
  ext w
  simp_rw [realSpaceToLogSpace_apply, sum_expMap_symm_apply hx, expMap_symm_apply,
    logMap, normAtPlace_apply, mul_sub, mul_assoc, norm_eq_norm]

variable (K) in
/--
Docstring.
-/
def completeFamily : InfinitePlace K → realSpace K := by
  intro i
  by_cases hi : i = w₀
  · exact fun w ↦ mult w
  · exact expMap.symm
      (normAtAllPlaces (mixedEmbedding K (fundSystem K (equivFinRank.symm ⟨i, hi⟩))))

theorem realSpaceToLogSpace_completeFamily_of_eq :
    realSpaceToLogSpace (completeFamily K w₀) = 0 := by
  ext
  rw [realSpaceToLogSpace_apply, completeFamily, dif_pos rfl, ← Nat.cast_sum, sum_mult_eq,
    mul_inv_cancel_right₀ (Nat.cast_ne_zero.mpr Module.finrank_pos.ne'), sub_self, Pi.zero_apply]

theorem realSpaceToLogSpace_completeFamily_of_ne (i : {w : InfinitePlace K // w ≠ w₀}) :
    realSpaceToLogSpace (completeFamily K i) =
      (logEmbedding K) (Additive.ofMul (fundSystem K (equivFinRank.symm i))) := by
  ext
  rw [← logMap_eq_logEmbedding, completeFamily, dif_neg, realSpaceToLogSpace_expMap_symm]
  exact coe_ne_zero _

theorem sum_eq_zero_of_mem_span_completeFamily {x : realSpace K}
    (hx : x ∈ Submodule.span ℝ (Set.range fun w : {w // w ≠ w₀} ↦ completeFamily K w.1)) :
    ∑ w, x w = 0 := by
  induction hx using Submodule.span_induction with
  | mem _ h =>
      obtain ⟨w, rfl⟩ := h
      simp_rw [completeFamily,  dif_neg w.prop, sum_expMap_symm_apply (coe_ne_zero _),
        Units.norm, Rat.cast_one, Real.log_one]
  | zero => simp
  | add _ _ _ _ hx hy => simp [sum_add_distrib, hx, hy]
  | smul _ _ _ hx => simp [← mul_sum, hx]

variable (K)

theorem linearIndependent_completeFamily :
    LinearIndependent ℝ (completeFamily K) := by
  classical
  have h₁ : LinearIndependent ℝ (fun w : {w // w ≠ w₀} ↦ completeFamily K w.1) := by
    refine LinearIndependent.of_comp realSpaceToLogSpace ?_
    simp_rw [Function.comp_def, realSpaceToLogSpace_completeFamily_of_ne, logEmbedding_fundSystem]
    convert (((basisUnitLattice K).ofZLatticeBasis ℝ _).reindex equivFinRank).linearIndependent
    simp
  have h₂ : completeFamily K w₀ ∉ Submodule.span ℝ
      (Set.range (fun w : {w // w ≠ w₀} ↦ completeFamily K w.1)) := by
    intro h
    have := sum_eq_zero_of_mem_span_completeFamily h
    rw [completeFamily, dif_pos rfl, ← Nat.cast_sum, sum_mult_eq, Nat.cast_eq_zero] at this
    exact Module.finrank_pos.ne' this
  rw [← linearIndependent_equiv (Equiv.optionSubtypeNe w₀), linearIndependent_option]
  exact ⟨h₁, h₂⟩

/--
Docstring.
-/
def completeBasis : Basis (InfinitePlace K) ℝ (realSpace K) :=
  basisOfLinearIndependentOfCardEqFinrank (linearIndependent_completeFamily K)
    (Module.finrank_fintype_fun_eq_card _).symm

theorem completeBasis_apply_of_eq :
    completeBasis K w₀ = fun w ↦ (mult w : ℝ) := by
  rw [completeBasis, coe_basisOfLinearIndependentOfCardEqFinrank, completeFamily, dif_pos rfl]

theorem completeBasis_apply_of_ne (i : {w : InfinitePlace K // w ≠ w₀}) :
    completeBasis K i =
      expMap.symm (normAtAllPlaces (mixedEmbedding K (fundSystem K (equivFinRank.symm i)))) := by
  rw [completeBasis, coe_basisOfLinearIndependentOfCardEqFinrank, completeFamily, dif_neg]

theorem expMap_basis_of_eq :
    expMap (completeBasis K w₀) = fun _ ↦ Real.exp 1 := by
  ext
  simp_rw [expMap_apply, completeBasis_apply_of_eq, inv_mul_cancel₀ mult_coe_ne_zero]

theorem expMap_basis_of_ne (i : {w : InfinitePlace K // w ≠ w₀}) :
    expMap (completeBasis K i) =
      normAtAllPlaces (mixedEmbedding K (fundSystem K (equivFinRank.symm i))) := by
  rw [completeBasis_apply_of_ne, PartialHomeomorph.right_inv _ (by simp [expMap_target])]

theorem abs_det_completeBasis_equivFunL_symm :
    |((completeBasis K).equivFunL.symm : realSpace K →L[ℝ] realSpace K).det| =
      Module.finrank ℚ K * regulator K := by
  classical
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (completeBasis K), ← Matrix.det_transpose,
    finrank_mul_regulator_eq_det K w₀ equivFinRank.symm]
  congr 2 with w i
  rw [Matrix.transpose_apply, LinearMap.toMatrix_apply, Matrix.of_apply, ← Basis.equivFunL_apply,
    ContinuousLinearMap.coe_coe, ContinuousLinearEquiv.coe_apply,
    (completeBasis K).equivFunL.apply_symm_apply]
  split_ifs with hw
  · rw [hw, completeBasis_apply_of_eq]
  · simp_rw [completeBasis_apply_of_ne K ⟨w, hw⟩, expMap_symm_apply, normAtAllPlaces_mixedEmbedding]

end completeBasis

noncomputable section expMapBasis

variable [NumberField K]

variable {K}

/--
Docstring.
-/
def expMapBasis : PartialHomeomorph (realSpace K) (realSpace K) :=
  (completeBasis K).equivFunL.symm.toHomeomorph.transPartialHomeomorph expMap

variable (K)

theorem injective_expMapBasis :
    Function.Injective (expMapBasis : realSpace K → realSpace K) :=
  (injective_expMap K).comp (completeBasis K).equivFun.symm.injective

theorem continuous_expMapBasis :
    Continuous (expMapBasis : realSpace K → realSpace K) :=
  (continuous_expMap K).comp (ContinuousLinearEquiv.continuous _)

theorem expMapBasis_source :
    expMapBasis.source = (Set.univ : Set (realSpace K)) := by
  simp [expMapBasis, expMap_source]

variable {K}

theorem expMapBasis_pos (x : realSpace K) (w : InfinitePlace K) :
    0 < expMapBasis x w := expMap_pos _ _

theorem expMapBasis_nonneg (x : realSpace K) (w : InfinitePlace K) :
    0 ≤ expMapBasis x w := (expMapBasis_pos _ _).le

theorem expMapBasis_apply (x : realSpace K) :
    expMapBasis x = expMap ((completeBasis K).equivFun.symm x) := rfl

open scoped Classical in
theorem expMapBasis_apply' (x : realSpace K) :
    expMapBasis x = Real.exp (x w₀) •
      fun w : InfinitePlace K ↦
         ∏ i : {w // w ≠ w₀}, w (fundSystem K (equivFinRank.symm i)) ^ x i := by
  simp_rw [expMapBasis_apply, Basis.equivFun_symm_apply, Fintype.sum_eq_add_sum_subtype_ne _ w₀,
    expMap_add, expMap_smul, expMap_basis_of_eq, Pi.pow_def, Real.exp_one_rpow, Pi.mul_def,
    expMap_sum, expMap_smul, expMap_basis_of_ne, Pi.smul_def, smul_eq_mul, prod_apply, Pi.pow_apply,
    normAtAllPlaces_mixedEmbedding]

open scoped Classical in
theorem expMapBasis_apply'' (x : realSpace K) :
    expMapBasis x = Real.exp (x w₀) • expMapBasis (fun i ↦ if i = w₀ then 0 else x i) := by
 rw [expMapBasis_apply', expMapBasis_apply', if_pos rfl, smul_smul, ← Real.exp_add, add_zero]
 conv_rhs =>
   enter [2, w, 2, i]
   rw [if_neg i.prop]

theorem normAtAllPlaces_expMapBasis (x : realSpace K) :
    normAtAllPlaces (mixedSpaceOfRealSpace (expMapBasis x)) = expMapBasis x := by
  rw [normAtAllPlaces_mixedSpaceOfRealSpace fun _ ↦ expMapBasis_nonneg _ _]

theorem prod_expMapBasis_pow (x : realSpace K) :
    ∏ w, (expMapBasis x w) ^ w.mult = Real.exp (x w₀) ^ Module.finrank ℚ K := by
  simp_rw [expMapBasis_apply', Pi.smul_def, smul_eq_mul, mul_pow, prod_mul_distrib,
    prod_pow_eq_pow_sum, sum_mult_eq, ← prod_pow]
  rw [prod_comm]
  simp_rw [Real.rpow_pow_comm (apply_nonneg _ _), Real.finset_prod_rpow _ _
    fun _ _ ↦ pow_nonneg (apply_nonneg _ _) _, prod_eq_abs_norm, Units.norm, Rat.cast_one,
    Real.one_rpow, prod_const_one, mul_one]

open scoped Classical in
theorem prod_deriv_expMap_single (x : realSpace K) :
    ∏ w, deriv_expMap_single w ((completeBasis K).equivFun.symm x w) =
      Real.exp (x w₀) ^ Module.finrank ℚ K * (∏ w : {w // IsComplex w}, expMapBasis x w.1)⁻¹ *
        (2⁻¹) ^ nrComplexPlaces K := by
  simp only [deriv_expMap_single, expMap_single_apply]
  rw [Finset.prod_mul_distrib]
  congr 1
  · simp_rw [← prod_expMapBasis_pow, prod_eq_prod_mul_prod, expMapBasis_apply, expMap_apply,
      mult_isReal, mult_isComplex, pow_one, Finset.prod_pow, pow_two, mul_assoc, mul_inv_cancel₀
      (Finset.prod_ne_zero_iff.mpr <| fun _ _ ↦ Real.exp_ne_zero _), mul_one]
  · simp [prod_eq_prod_mul_prod, mult_isReal, mult_isComplex]

theorem norm_expMapBasis (x : realSpace K) :
    mixedEmbedding.norm (mixedSpaceOfRealSpace (expMapBasis x)) =
      Real.exp (x w₀) ^ Module.finrank ℚ K := by
  simpa only [mixedEmbedding.norm_apply,
    normAtPlace_mixedSpaceOfRealSpace (expMapBasis_pos _ _).le] using prod_expMapBasis_pow x

theorem norm_expMapBasis_ne_zero (x : realSpace K) :
    mixedEmbedding.norm (mixedSpaceOfRealSpace (expMapBasis x)) ≠ 0 :=
  norm_expMapBasis x ▸ pow_ne_zero _ (Real.exp_ne_zero _)

open scoped Classical in
theorem logMap_expMapBasis (x : realSpace K) :
    logMap (mixedSpaceOfRealSpace (expMapBasis x)) ∈
        ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ (unitLattice K))
      ↔ ∀ w, w ≠ w₀ → x w ∈ Set.Ico 0 1 := by
  classical
  simp_rw [ZSpan.mem_fundamentalDomain, equivFinRank.forall_congr_left, Subtype.forall]
  refine forall₂_congr fun w hw ↦ ?_
  rw [expMapBasis_apply'', map_smul, logMap_real_smul (norm_expMapBasis_ne_zero _)
    (Real.exp_ne_zero _), expMapBasis_apply, logMap_expMap (by rw [← expMapBasis_apply,
    norm_expMapBasis, if_pos rfl, Real.exp_zero, one_pow]), Basis.equivFun_symm_apply,
    Fintype.sum_eq_add_sum_subtype_ne _ w₀, if_pos rfl, zero_smul, zero_add]
  conv_lhs =>
    enter [2, 1, 2, w, 2, i]
    rw [if_neg i.prop]
  simp_rw [sum_apply, ← sum_fn, map_sum, Pi.smul_apply, ← Pi.smul_def, map_smul,
    completeBasis_apply_of_ne, expMap_symm_apply, normAtAllPlaces_mixedEmbedding,
    ← logEmbedding_component, logEmbedding_fundSystem, Finsupp.coe_finset_sum, Finsupp.coe_smul,
    sum_apply, Pi.smul_apply, Basis.ofZLatticeBasis_repr_apply, Basis.repr_self,
    Finsupp.single_apply, EmbeddingLike.apply_eq_iff_eq, Int.cast_ite, Int.cast_one, Int.cast_zero,
    smul_ite, smul_eq_mul, mul_one, mul_zero, Fintype.sum_ite_eq']

theorem normAtAllPlaces_image_preimage_expMapBasis (s : Set (realSpace K)) :
    normAtAllPlaces '' (normAtAllPlaces ⁻¹' (expMapBasis '' s)) = expMapBasis '' s := by
  apply normAtAllPlaces_image_preimage_of_nonneg
  rintro _ ⟨x, _, rfl⟩ w
  exact (expMapBasis_pos _ _).le

section setLIntegral

open ENNReal MeasureTheory

variable (K)

/--
Docstring.
-/
abbrev fderiv_expMapBasis (x : realSpace K) : realSpace K →L[ℝ] realSpace K :=
  (fderiv_expMap ((completeBasis K).equivFun.symm x)).comp
    (completeBasis K).equivFunL.symm.toContinuousLinearMap

theorem hasFDerivAt_expMapBasis (x : realSpace K) :
    HasFDerivAt expMapBasis (fderiv_expMapBasis K x) x := by
  change HasFDerivAt (expMap ∘ (completeBasis K).equivFunL.symm) (fderiv_expMapBasis K x) x
  exact (hasFDerivAt_expMap _).comp x (completeBasis K).equivFunL.symm.hasFDerivAt

open Classical ContinuousLinearMap in
theorem abs_det_fderiv_expMapBasis (x : realSpace K) :
    |(fderiv_expMapBasis K x).det| =
      Real.exp (x w₀ * Module.finrank ℚ K) *
      (∏ w : {w // IsComplex w}, expMapBasis x w.1)⁻¹ * 2⁻¹ ^ nrComplexPlaces K *
        (Module.finrank ℚ K) * regulator K := by
  simp_rw [fderiv_expMapBasis, det, coe_comp, LinearMap.det_comp, fderiv_expMap, coe_pi, coe_comp,
    coe_proj, LinearMap.det_pi, LinearMap.det_ring, ContinuousLinearMap.coe_coe, smulRight_apply,
    one_apply, one_smul, abs_mul, abs_det_completeBasis_equivFunL_symm, prod_deriv_expMap_single]
  simp_rw [abs_mul, Real.exp_mul, abs_pow, Real.rpow_natCast, abs_of_nonneg (Real.exp_nonneg _),
    abs_inv, abs_prod, abs_of_nonneg (expMapBasis_nonneg _ _), Nat.abs_ofNat]
  ring

open scoped Classical in
theorem setLIntegral_expMapBasis_image {s : Set (realSpace K)} (hs : MeasurableSet s)
    {f : (InfinitePlace K → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x in expMapBasis '' s, f x =
      (2 : ℝ≥0∞)⁻¹ ^ nrComplexPlaces K * ENNReal.ofReal (regulator K) * (Module.finrank ℚ K) *
        ∫⁻ x in s, ENNReal.ofReal (Real.exp (x w₀ * Module.finrank ℚ K)) *
          (∏ i : {w : InfinitePlace K // IsComplex w},
            .ofReal (expMapBasis (fun w ↦ x w) i))⁻¹ * f (expMapBasis x) := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
    (fun x _ ↦ (hasFDerivAt_expMapBasis K x).hasFDerivWithinAt) (injective_expMapBasis K).injOn]
  simp_rw [abs_det_fderiv_expMapBasis]
  have : Measurable expMapBasis := (continuous_expMapBasis K).measurable
  rw [← lintegral_const_mul _ (by fun_prop)]
  congr with x
  have : 0 ≤ (∏ w : {w // IsComplex w}, expMapBasis x w.1)⁻¹ :=
    inv_nonneg.mpr <| Finset.prod_nonneg fun _ _ ↦ (expMapBasis_pos _ _).le
  rw [ofReal_mul (by positivity), ofReal_mul (by positivity), ofReal_mul (by positivity),
    ofReal_mul (by positivity), ofReal_pow (by positivity), ofReal_inv_of_pos (Finset.prod_pos
    fun _ _ ↦ expMapBasis_pos _ _), ofReal_inv_of_pos zero_lt_two, ofReal_ofNat, ofReal_natCast,
    ofReal_prod_of_nonneg (fun _ _ ↦ (expMapBasis_pos _ _).le)]
  ring

end setLIntegral

end expMapBasis

section param

variable [NumberField K]

open scoped Classical in
/--
Docstring.
-/
abbrev paramSet : Set (realSpace K) :=
  Set.univ.pi fun w ↦ if w = w₀ then Set.Iic 0 else Set.Ico 0 1

theorem measurableSet_paramSet :
    MeasurableSet (paramSet K) := by
  refine MeasurableSet.univ_pi fun _ ↦ ?_
  split_ifs
  · exact measurableSet_Iic
  · exact measurableSet_Ico

open scoped Classical in
theorem closure_paramSet :
    closure (paramSet K) = Set.univ.pi fun w ↦ if w = w₀ then Set.Iic 0 else Set.Icc 0 1 := by
  simp [closure_pi_set, apply_ite]

open scoped Classical in
theorem interior_paramSet :
    interior (paramSet K) = Set.univ.pi fun w ↦ if w = w₀ then Set.Iio 0 else Set.Ioo 0 1 := by
  simp [interior_pi_set Set.finite_univ, apply_ite]

theorem measurableSet_interior_paramSet :
    MeasurableSet (interior (paramSet K)) := by
  rw [interior_paramSet]
  refine MeasurableSet.univ_pi fun _ ↦ ?_
  split_ifs
  · exact measurableSet_Iio
  · exact measurableSet_Ioo

open scoped Classical in
theorem normAtAllPlaces_normLeOne :
    normAtAllPlaces '' (normLeOne K) = {x | (∀ w, 0 ≤ x w) ∧
      logMap (mixedSpaceOfRealSpace x) ∈
      ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ (unitLattice K)) ∧
      mixedEmbedding.norm (mixedSpaceOfRealSpace x) ≠ 0 ∧
      mixedEmbedding.norm (mixedSpaceOfRealSpace x) ≤ 1} := by
  ext x
  refine ⟨?_, fun ⟨hx₁, hx₂, hx₃, hx₄⟩ ↦ ?_⟩
  · rintro ⟨a, ⟨⟨ha₁, ha₂⟩, ha₃⟩, rfl⟩
    refine ⟨fun w ↦ normAtPlace_nonneg w a, ?_⟩
    exact (logMap_normAtAllPlaces a) ▸ (norm_normAtAllPlaces a) ▸ ⟨ha₁, ha₂, ha₃⟩
  · exact ⟨mixedSpaceOfRealSpace x, ⟨⟨hx₂, hx₃⟩, hx₄⟩, normAtAllPlaces_mixedSpaceOfRealSpace hx₁⟩

theorem normAtAllPlaces_normLeOne_eq_image :
    normAtAllPlaces '' (normLeOne K) = expMapBasis '' (paramSet K) := by
  ext x
  by_cases hx : ∀ w, 0 < x w
  · rw [← expMapBasis.right_inv (Set.mem_univ_pi.mpr hx), (injective_expMapBasis K).mem_set_image]
    simp only [normAtAllPlaces_normLeOne, ne_eq, Set.mem_setOf_eq, expMapBasis_nonneg,
      implies_true, logMap_expMapBasis, norm_expMapBasis, pow_eq_zero_iff', Real.exp_ne_zero,
      false_and, not_false_eq_true, pow_le_one_iff_of_nonneg (Real.exp_nonneg _)
      Module.finrank_pos.ne', Real.exp_le_one_iff, true_and, Set.mem_univ_pi]
    refine ⟨fun ⟨h₁, h₂⟩ w ↦ ?_, fun h ↦ ⟨fun w hw ↦ by simpa [hw] using h w, by simpa using h w₀⟩⟩
    split_ifs with hw
    · exact hw ▸ h₂
    · exact h₁ w hw
  · refine ⟨?_, ?_⟩
    · rintro ⟨a, ⟨ha, _⟩, rfl⟩
      exact (hx fun w ↦ fundamentalCone.normAtPlace_pos_of_mem ha w).elim
    · rintro ⟨a, _, rfl⟩
      exact (hx fun w ↦ expMapBasis_pos a w).elim

theorem normLeOne_eq_preimage :
    normLeOne K = normAtAllPlaces⁻¹' (expMapBasis '' (paramSet K)) := by
  rw [normLeOne_eq_primeage_image, normAtAllPlaces_normLeOne_eq_image]

theorem subset_interior_normLeOne :
    normAtAllPlaces⁻¹' (expMapBasis '' interior (paramSet K)) ⊆ interior (normLeOne K) := by
  rw [normLeOne_eq_preimage]
  refine subset_trans (Set.preimage_mono ?_) <|
    preimage_interior_subset_interior_preimage (continuous_normAtAllPlaces K)
  have : IsOpen (expMapBasis '' (interior (paramSet K))) :=
    expMapBasis.isOpen_image_of_subset_source isOpen_interior (by simp [expMapBasis_source])
  exact interior_maximal (Set.image_mono interior_subset) this

open ENNReal MeasureTheory MeasureTheory.Measure

theorem closure_paramSet_eq_interior :
  closure (paramSet K) =ᵐ[volume] interior (paramSet K) := by
  rw [closure_paramSet, interior_paramSet, volume_pi]
  refine ae_eq_set_pi fun w _ ↦ ?_
  split_ifs
  · exact Iio_ae_eq_Iic.symm
  · exact Ioo_ae_eq_Icc.symm

theorem setLIntegral_paramSet_exp {n : ℕ} (hn : 0 < n) :
    ∫⁻ (x : realSpace K) in paramSet K, .ofReal (Real.exp (x w₀ * n)) = (n : ℝ≥0∞)⁻¹ := by
  classical
  rw [volume_pi, paramSet, Measure.restrict_pi_pi, lintegral_eq_lmarginal_univ 0,
    lmarginal_erase' _ (by fun_prop) (Finset.mem_univ w₀), if_pos rfl]
  simp_rw [Function.update_self, lmarginal, lintegral_const, Measure.pi_univ, if_neg
    (Finset.ne_of_mem_erase (Subtype.prop _)), restrict_apply_univ, Real.volume_Ico, sub_zero,
    ofReal_one, prod_const_one, mul_one]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [← setIntegral_congr_set Iio_ae_eq_Iic, integral_comp_mul_right_Iio _ _
      (Nat.cast_pos.mpr hn), zero_mul, setIntegral_congr_set Iio_ae_eq_Iic, integral_exp_Iic,
      Real.exp_zero, smul_eq_mul, mul_one, ofReal_inv_of_pos (Nat.cast_pos.mpr hn), ofReal_natCast]
  · rw [← IntegrableOn, integrableOn_Iic_iff_integrableOn_Iio, integrableOn_Iio_comp_mul_right_iff _
      _ (Nat.cast_pos.mpr hn), zero_mul, ← integrableOn_Iic_iff_integrableOn_Iio]
    exact integrableOn_exp_Iic 0
  · filter_upwards with _ using Real.exp_nonneg _

end param

section compactSet

variable [NumberField K]

open Pointwise

open scoped Classical in
/--
Docstring.
-/
abbrev compactSet : Set (realSpace K) :=
  (Set.Icc (0 : ℝ) 1) • (expMapBasis '' Set.univ.pi fun w ↦ if w = w₀ then {0} else Set.Icc 0 1)

theorem zero_mem_compactSet :
    0 ∈ compactSet K := by
  refine Set.zero_mem_smul_iff.mpr (Or.inl ⟨Set.left_mem_Icc.mpr zero_le_one, ?_⟩)
  exact Set.image_nonempty.mpr (Set.univ_pi_nonempty_iff.mpr (by aesop))

theorem nonneg_of_mem_compactSet {x : realSpace K} (hx : x ∈ compactSet K) (w : InfinitePlace K) :
    0 ≤ x w := by
  obtain ⟨c, hc, ⟨_, ⟨⟨a, ha, rfl⟩, _, rfl⟩⟩⟩ := hx
  exact mul_nonneg hc.1 (expMapBasis_pos _ _).le

theorem isCompact_compactSet :
    IsCompact (compactSet K) := by
  refine isCompact_Icc.smul_set <| (isCompact_univ_pi fun w ↦ ?_).image_of_continuousOn
    (continuous_expMapBasis K).continuousOn
  split_ifs
  · exact isCompact_singleton
  · exact isCompact_Icc

theorem compactSet_eq_union :
    compactSet K = expMapBasis '' closure (paramSet K) ∪ {0} := by
  classical
  ext x
  by_cases hx₀ : x = 0
  · simpa [hx₀] using zero_mem_compactSet K
  · simp only [Set.union_singleton, Set.mem_insert_iff, hx₀, false_or, closure_paramSet,
      Set.mem_image, Set.mem_smul, exists_exists_and_eq_and]
    refine ⟨?_, ?_⟩
    · rintro ⟨c, hc, ⟨a, ha, rfl⟩⟩
      have hc' : c > 0 := by
        contrapose! hx₀
        rw [le_antisymm hx₀ hc.1, zero_smul]
      refine ⟨fun w ↦ if w = w₀ then Real.log c else a w, Set.mem_univ_pi.mpr fun w ↦ ?_, ?_⟩
      · split_ifs with h
        · exact Real.log_nonpos hc.1 hc.2
        · simpa [h] using ha w (Set.mem_univ _)
      · rw [expMapBasis_apply'', if_pos rfl, Real.exp_log hc']
        congr with w
        split_ifs with h
        · simpa [h, eq_comm] using ha w₀
        · rfl
    · rintro ⟨a, ha, rfl⟩
      refine ⟨Real.exp (a w₀), ⟨Real.exp_nonneg _, ?_⟩,
        fun i ↦ if i = w₀ then 0 else a i, Set.mem_univ_pi.mpr fun w ↦ ?_,
        by rw [expMapBasis_apply'' a]⟩
      · exact Real.exp_le_one_iff.mpr (by simpa using ha w₀ (Set.mem_univ _))
      · split_ifs with h
        · rfl
        · simpa [h] using ha w (Set.mem_univ _)

theorem expMapBasis_closure_subset_compactSet :
    expMapBasis '' closure (paramSet K) ⊆ compactSet K := by
  rw [compactSet_eq_union]
  exact Set.subset_union_left

theorem closure_normLeOne_subset :
    closure (normLeOne K) ⊆ normAtAllPlaces⁻¹' (compactSet K) := by
  rw [normLeOne_eq_preimage]
  refine ((continuous_normAtAllPlaces K).closure_preimage_subset _).trans (Set.preimage_mono ?_)
  refine (isCompact_compactSet K).isClosed.closure_subset_iff.mpr ?_
  exact (Set.image_mono subset_closure).trans (expMapBasis_closure_subset_compactSet _)

open MeasureTheory

theorem compactSet_ae :
    compactSet K =ᵐ[volume] expMapBasis '' closure (paramSet K) := by
  rw [compactSet_eq_union]
  exact union_ae_eq_left_of_ae_eq_empty (by simp)

end compactSet

end NormLeOne

variable [NumberField K]

open ENNReal Bornology MeasureTheory NormLeOne

theorem measurableSet_normLeOne :
    MeasurableSet (normLeOne K) :=
  (measurableSet_fundamentalCone K).inter <|
    measurableSet_le (mixedEmbedding.continuous_norm K).measurable measurable_const

theorem isBounded_normLeOne :
    IsBounded (normLeOne K) := by
  classical
  rw [normLeOne_eq_preimage]
  suffices IsBounded (expMapBasis '' paramSet K) by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp this
    refine isBounded_iff_forall_norm_le.mpr ⟨C, fun x hx ↦ ?_⟩
    rw [norm_eq_sup'_normAtPlace]
    refine sup'_le _ _ fun w _ ↦ ?_
    simpa [normAtAllPlaces_apply, Real.norm_of_nonneg (normAtPlace_nonneg w x)]
      using (pi_norm_le_iff_of_nonempty _).mp (hC _ hx) w
  refine IsBounded.subset ?_ (Set.image_mono subset_closure)
  exact (isCompact_compactSet K).isBounded.subset (expMapBasis_closure_subset_compactSet K)

open scoped Classical in
theorem volume_normLeOne : volume (normLeOne K) =
    2 ^ nrRealPlaces K * NNReal.pi ^ nrComplexPlaces K * .ofReal (regulator K) := by
  rw [volume_eq_two_pow_mul_two_pi_pow_mul_integral (fun x ↦ mem_normLeOne_iff x)
    (measurableSet_normLeOne K), normLeOne_eq_preimage,
    normAtAllPlaces_image_preimage_expMapBasis,
    setLIntegral_expMapBasis_image K (measurableSet_paramSet K) (by fun_prop)]
  simp_rw [ENNReal.inv_mul_cancel_right
    (Finset.prod_ne_zero_iff.mpr fun _ _ ↦ ofReal_ne_zero_iff.mpr (expMapBasis_pos _ _))
    (prod_ne_top fun _ _ ↦ ofReal_ne_top)]
  rw [setLIntegral_paramSet_exp K Module.finrank_pos, ofReal_mul zero_le_two, mul_pow,
    ofReal_ofNat, ENNReal.mul_inv_cancel_right (Nat.cast_ne_zero.mpr Module.finrank_pos.ne')
    (natCast_ne_top _), coe_nnreal_eq, NNReal.coe_real_pi, mul_mul_mul_comm, ← ENNReal.inv_pow,
    ← mul_assoc, ← mul_assoc, ENNReal.inv_mul_cancel_right (pow_ne_zero _ two_ne_zero)
    (pow_ne_top ENNReal.ofNat_ne_top)]

open scoped Classical in
theorem volume_interior_eq_volume_closure :
    volume (interior (normLeOne K)) = volume (closure (normLeOne K)) := by
  have h₁ : MeasurableSet (normAtAllPlaces ⁻¹' compactSet K) :=
    (isCompact_compactSet K).measurableSet.preimage (continuous_normAtAllPlaces K).measurable
  have h₂ :  MeasurableSet (normAtAllPlaces ⁻¹' (↑expMapBasis '' interior (paramSet K))) := by
    refine MeasurableSet.preimage ?_ (continuous_normAtAllPlaces K).measurable
    refine MeasurableSet.image_of_continuousOn_injOn ?_ (continuous_expMapBasis K).continuousOn
      (injective_expMapBasis K).injOn
    exact measurableSet_interior_paramSet K
  refine le_antisymm (measure_mono interior_subset_closure) ?_
  refine (measure_mono (closure_normLeOne_subset K)).trans ?_
  refine le_of_eq_of_le ?_ (measure_mono (subset_interior_normLeOne K))
  rw [volume_eq_two_pow_mul_two_pi_pow_mul_integral (forall_mem_iff_normAtAllPlaces_mem rfl) h₁,
    normAtAllPlaces_image_preimage_of_nonneg (fun x a w ↦ nonneg_of_mem_compactSet K a w),
    volume_eq_two_pow_mul_two_pi_pow_mul_integral (forall_mem_iff_normAtAllPlaces_mem rfl) h₂,
    normAtAllPlaces_image_preimage_expMapBasis, setLIntegral_congr (compactSet_ae K),
    setLIntegral_expMapBasis_image K measurableSet_closure (by fun_prop),
    setLIntegral_expMapBasis_image K measurableSet_interior (by fun_prop),
    setLIntegral_congr (closure_paramSet_eq_interior K)]

open scoped Classical in
theorem volume_frontier_normLeOne :
     volume (frontier (normLeOne K)) = 0 := by
  rw [frontier, measure_diff, volume_interior_eq_volume_closure, tsub_self]
  · exact interior_subset_closure
  · exact measurableSet_interior.nullMeasurableSet
  · refine lt_top_iff_ne_top.mp <| lt_of_le_of_lt (measure_mono interior_subset) ?_
    rw [volume_normLeOne]
    exact Batteries.compareOfLessAndEq_eq_lt.mp rfl

end NumberField.mixedEmbedding
