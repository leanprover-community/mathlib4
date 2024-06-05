/-
Copyright (c) 2022 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

#align_import number_theory.number_field.canonical_embedding from "leanprover-community/mathlib"@"60da01b41bbe4206f05d34fd70c8dd7498717a30"

/-!
# Convex Bodies

The file contains the definitions of several convex bodies lying in the space `ℝ^r₁ × ℂ^r₂`
associated to a number field of signature `K` and proves several existence theorems by applying
*Minkowski Convex Body Theorem* to those.

## Main definitions and results

* `NumberField.mixedEmbedding.convexBodyLT`: The set of points `x` such that `‖x w‖ < f w` for all
infinite places `w` with `f : InfinitePlace K → ℝ≥0`.

* `NumberField.mixedEmbedding.convexBodySum`: The set of points `x` such that
`∑ w real, ‖x w‖ + 2 * ∑ w complex, ‖x w‖ ≤ B`

* `NumberField.mixedEmbedding.exists_ne_zero_mem_ideal_lt`: Let `I` be a fractional ideal of `K`.
Assume that `f` is such that `minkowskiBound K I < volume (convexBodyLT K f)`, then there exists a
nonzero algebraic number `a` in `I` such that `w a < f w` for all infinite places `w`.

* `NumberField.mixedEmbedding.exists_ne_zero_mem_ideal_of_norm_le`: Let `I` be a fractional ideal
of `K`. Assume that `B` is such that `minkowskiBound K I < volume (convexBodySum K B)` (see
`convexBodySum_volume` for the computation of this volume), then there exists a nonzero algebraic
number `a` in `I` such that `|Norm a| < (B / d) ^ d` where `d` is the degree of `K`.

## Tags

number field, infinite places
-/

variable (K : Type*) [Field K]

namespace NumberField.mixedEmbedding

open NumberField NumberField.InfinitePlace FiniteDimensional

/-- The space `ℝ^r₁ × ℂ^r₂` with `(r₁, r₂)` the signature of `K`. -/
local notation "E" K =>
  ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℂ)

section convexBodyLT

open Metric NNReal

variable (f : InfinitePlace K → ℝ≥0)

/-- The convex body defined by `f`: the set of points `x : E` such that `‖x w‖ < f w` for all
infinite places `w`. -/
abbrev convexBodyLT : Set (E K) :=
  (Set.univ.pi (fun w : { w : InfinitePlace K // IsReal w } => ball 0 (f w))) ×ˢ
  (Set.univ.pi (fun w : { w : InfinitePlace K // IsComplex w } => ball 0 (f w)))

theorem convexBodyLT_mem {x : K} :
    mixedEmbedding K x ∈ (convexBodyLT K f) ↔ ∀ w : InfinitePlace K, w x < f w := by
  simp_rw [mixedEmbedding, RingHom.prod_apply, Set.mem_prod, Set.mem_pi, Set.mem_univ,
    forall_true_left, mem_ball_zero_iff, Pi.ringHom_apply, ← Complex.norm_real,
    embedding_of_isReal_apply, Subtype.forall, ← forall₂_or_left, ← not_isReal_iff_isComplex, em,
    forall_true_left, norm_embedding_eq]

theorem convexBodyLT_neg_mem (x : E K) (hx : x ∈ (convexBodyLT K f)) :
    -x ∈ (convexBodyLT K f) := by
  simp only [Set.mem_prod, Prod.fst_neg, Set.mem_pi, Set.mem_univ, Pi.neg_apply,
    mem_ball_zero_iff, norm_neg, Real.norm_eq_abs, forall_true_left, Subtype.forall,
    Prod.snd_neg, Complex.norm_eq_abs] at hx ⊢
  exact hx

theorem convexBodyLT_convex : Convex ℝ (convexBodyLT K f) :=
  Convex.prod (convex_pi (fun _ _ => convex_ball _ _)) (convex_pi (fun _ _ => convex_ball _ _))

open Fintype MeasureTheory MeasureTheory.Measure ENNReal

open scoped Classical

variable [NumberField K]

instance : IsAddHaarMeasure (volume : Measure (E K)) := prod.instIsAddHaarMeasure volume volume

instance : NoAtoms (volume : Measure (E K)) := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  by_cases hw : IsReal w
  · exact @prod.instNoAtoms_fst _ _ _ _ volume volume _ (pi_noAtoms ⟨w, hw⟩)
  · exact @prod.instNoAtoms_snd _ _ _ _ volume volume _
      (pi_noAtoms ⟨w, not_isReal_iff_isComplex.mp hw⟩)

/-- The fudge factor that appears in the formula for the volume of `convexBodyLT`. -/
noncomputable abbrev convexBodyLTFactor : ℝ≥0 :=
  (2 : ℝ≥0) ^ NrRealPlaces K * NNReal.pi ^ NrComplexPlaces K

theorem convexBodyLTFactor_ne_zero : convexBodyLTFactor K ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ two_ne_zero) (pow_ne_zero _ pi_ne_zero)

theorem one_le_convexBodyLTFactor : 1 ≤ convexBodyLTFactor K :=
  one_le_mul₀ (one_le_pow_of_one_le one_le_two _)
    (one_le_pow_of_one_le (le_trans one_le_two Real.two_le_pi) _)

/-- The volume of `(ConvexBodyLt K f)` where `convexBodyLT K f` is the set of points `x`
such that `‖x w‖ < f w` for all infinite places `w`. -/
theorem convexBodyLT_volume :
    volume (convexBodyLT K f) = (convexBodyLTFactor K) * ∏ w, (f w) ^ (mult w) := by
  calc
    _ = (∏ x : {w // InfinitePlace.IsReal w}, ENNReal.ofReal (2 * (f x.val))) *
          ∏ x : {w // InfinitePlace.IsComplex w}, ENNReal.ofReal (f x.val) ^ 2 * NNReal.pi := by
      simp_rw [volume_eq_prod, prod_prod, volume_pi, pi_pi, Real.volume_ball, Complex.volume_ball]
    _ = ((2:ℝ≥0) ^ NrRealPlaces K * (∏ x : {w // InfinitePlace.IsReal w}, ENNReal.ofReal (f x.val)))
          * ((∏ x : {w // IsComplex w}, ENNReal.ofReal (f x.val) ^ 2) *
            NNReal.pi ^ NrComplexPlaces K) := by
      simp_rw [ofReal_mul (by norm_num : 0 ≤ (2 : ℝ)), Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ, ofReal_ofNat, ofReal_coe_nnreal, coe_ofNat]
    _ = (convexBodyLTFactor K) * ((∏ x : {w // InfinitePlace.IsReal w}, .ofReal (f x.val)) *
        (∏ x : {w // IsComplex w}, ENNReal.ofReal (f x.val) ^ 2)) := by
      simp_rw [convexBodyLTFactor, coe_mul, ENNReal.coe_pow]
      ring
    _ = (convexBodyLTFactor K) * ∏ w, (f w) ^ (mult w) := by
      simp_rw [mult, pow_ite, pow_one, Finset.prod_ite, ofReal_coe_nnreal, not_isReal_iff_isComplex,
        coe_mul, coe_finset_prod, ENNReal.coe_pow]
      congr 2
      · refine (Finset.prod_subtype (Finset.univ.filter _) ?_ (fun w => (f w : ℝ≥0∞))).symm
        exact fun _ => by simp only [Finset.mem_univ, forall_true_left, Finset.mem_filter, true_and]
      · refine (Finset.prod_subtype (Finset.univ.filter _) ?_ (fun w => (f w : ℝ≥0∞) ^ 2)).symm
        exact fun _ => by simp only [Finset.mem_univ, forall_true_left, Finset.mem_filter, true_and]

variable {f}

/-- This is a technical result: quite often, we want to impose conditions at all infinite places
but one and choose the value at the remaining place so that we can apply
`exists_ne_zero_mem_ringOfIntegers_lt`. -/
theorem adjust_f {w₁ : InfinitePlace K} (B : ℝ≥0) (hf : ∀ w, w ≠ w₁ → f w ≠ 0) :
    ∃ g : InfinitePlace K → ℝ≥0, (∀ w, w ≠ w₁ → g w = f w) ∧ ∏ w, (g w) ^ mult w = B := by
  let S := ∏ w ∈ Finset.univ.erase w₁, (f w) ^ mult w
  refine ⟨Function.update f w₁ ((B * S⁻¹) ^ (mult w₁ : ℝ)⁻¹), ?_, ?_⟩
  · exact fun w hw => Function.update_noteq hw _ f
  · rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w₁), Function.update_same,
      Finset.prod_congr rfl fun w hw => by rw [Function.update_noteq (Finset.ne_of_mem_erase hw)],
      ← NNReal.rpow_natCast, ← NNReal.rpow_mul, inv_mul_cancel, NNReal.rpow_one, mul_assoc,
      inv_mul_cancel, mul_one]
    · rw [Finset.prod_ne_zero_iff]
      exact fun w hw => pow_ne_zero _ (hf w (Finset.ne_of_mem_erase hw))
    · rw [mult]; split_ifs <;> norm_num

end convexBodyLT

section convexBodyLT'

open  Metric ENNReal NNReal

open scoped Classical

variable (f : InfinitePlace K → ℝ≥0) (w₀ : {w : InfinitePlace K // IsComplex w})

/-- A version of `convexBodyLT` with an additional condition at a fixed complex place. This is
needed to ensure the element constructed is not real, see for example
`exists_primitive_element_lt_of_isComplex`.
-/
abbrev convexBodyLT' : Set (E K) :=
  (Set.univ.pi (fun w : { w : InfinitePlace K // IsReal w } ↦ ball 0 (f w))) ×ˢ
  (Set.univ.pi (fun w : { w : InfinitePlace K // IsComplex w } ↦
    if w = w₀ then {x | |x.re| < 1 ∧ |x.im| < (f w : ℝ) ^ 2} else ball 0 (f w)))

theorem convexBodyLT'_mem {x : K} :
    mixedEmbedding K x ∈ convexBodyLT' K f w₀ ↔
      (∀ w : InfinitePlace K, w ≠ w₀ → w x < f w) ∧
      |(w₀.val.embedding x).re| < 1 ∧ |(w₀.val.embedding x).im| < (f w₀: ℝ) ^ 2 := by
  simp_rw [mixedEmbedding, RingHom.prod_apply, Set.mem_prod, Set.mem_pi, Set.mem_univ,
    forall_true_left, Pi.ringHom_apply, apply_ite, mem_ball_zero_iff, ← Complex.norm_real,
    embedding_of_isReal_apply, norm_embedding_eq, Subtype.forall, Set.mem_setOf_eq]
  refine ⟨fun ⟨h₁, h₂⟩ ↦ ⟨fun w h_ne ↦ ?_, ?_⟩, fun ⟨h₁, h₂⟩ ↦ ⟨fun w hw ↦ ?_, fun w hw ↦ ?_⟩⟩
  · by_cases hw : IsReal w
    · exact norm_embedding_eq w _ ▸ h₁ w hw
    · specialize h₂ w (not_isReal_iff_isComplex.mp hw)
      rwa [if_neg (by exact Subtype.coe_ne_coe.1 h_ne)] at h₂
  · simpa [if_true] using h₂ w₀.val w₀.prop
  · exact h₁ w (ne_of_isReal_isComplex hw w₀.prop)
  · by_cases h_ne : w = w₀
    · simpa [h_ne]
    · rw [if_neg (by exact Subtype.coe_ne_coe.1 h_ne)]
      exact h₁ w h_ne

theorem convexBodyLT'_neg_mem (x : E K) (hx : x ∈ convexBodyLT' K f w₀) :
    -x ∈ convexBodyLT' K f w₀ := by
  simp [Set.mem_prod, Prod.fst_neg, Set.mem_pi, Set.mem_univ, Pi.neg_apply,
    mem_ball_zero_iff, norm_neg, Real.norm_eq_abs, forall_true_left, Subtype.forall,
    Prod.snd_neg, Complex.norm_eq_abs] at hx ⊢
  convert hx using 3
  split_ifs <;> simp

theorem convexBodyLT'_convex : Convex ℝ (convexBodyLT' K f w₀) := by
  refine Convex.prod (convex_pi (fun _ _ => convex_ball _ _)) (convex_pi (fun _ _ => ?_))
  split_ifs
  · simp_rw [abs_lt]
    refine Convex.inter ((convex_halfspace_re_gt _).inter  (convex_halfspace_re_lt _))
      ((convex_halfspace_im_gt _).inter  (convex_halfspace_im_lt _))
  · exact convex_ball _ _

open MeasureTheory MeasureTheory.Measure

open scoped Classical

variable [NumberField K]

/-- The fudge factor that appears in the formula for the volume of `convexBodyLT'`. -/
noncomputable abbrev convexBodyLT'Factor : ℝ≥0 :=
  (2 : ℝ≥0) ^ (NrRealPlaces K + 2) * NNReal.pi ^ (NrComplexPlaces K - 1)

theorem convexBodyLT'Factor_ne_zero : convexBodyLT'Factor K ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ two_ne_zero) (pow_ne_zero _ pi_ne_zero)

theorem one_le_convexBodyLT'Factor : 1 ≤ convexBodyLT'Factor K :=
  one_le_mul₀ (one_le_pow_of_one_le one_le_two _)
    (one_le_pow_of_one_le (le_trans one_le_two Real.two_le_pi) _)

theorem convexBodyLT'_volume :
    volume (convexBodyLT' K f w₀) = convexBodyLT'Factor K * ∏ w, (f w) ^ (mult w) := by
  have vol_box : ∀ B : ℝ≥0, volume {x : ℂ | |x.re| < 1 ∧ |x.im| < B^2} = 4*B^2 := by
    intro B
    rw [← (Complex.volume_preserving_equiv_real_prod.symm).measure_preimage]
    · simp_rw [Set.preimage_setOf_eq, Complex.measurableEquivRealProd_symm_apply]
      rw [show {a : ℝ × ℝ | |a.1| < 1 ∧ |a.2| < B ^ 2} =
        Set.Ioo (-1:ℝ) (1:ℝ) ×ˢ Set.Ioo (- (B:ℝ) ^ 2) ((B:ℝ) ^ 2) by
          ext; simp_rw [Set.mem_setOf_eq, Set.mem_prod, Set.mem_Ioo, abs_lt]]
      simp_rw [volume_eq_prod, prod_prod, Real.volume_Ioo, sub_neg_eq_add, one_add_one_eq_two,
        ← two_mul, ofReal_mul zero_le_two, ofReal_pow (coe_nonneg B), ofReal_ofNat,
        ofReal_coe_nnreal, ← mul_assoc, show (2:ℝ≥0∞) * 2 = 4 by norm_num]
    · refine MeasurableSet.inter ?_ ?_
      · exact measurableSet_lt (measurable_norm.comp Complex.measurable_re) measurable_const
      · exact measurableSet_lt (measurable_norm.comp Complex.measurable_im) measurable_const
  calc
    _ = (∏ x : {w // InfinitePlace.IsReal w}, ENNReal.ofReal (2 * (f x.val))) *
          ((∏ x ∈ Finset.univ.erase  w₀, ENNReal.ofReal (f x.val) ^ 2 * pi) *
          (4 * (f w₀) ^ 2)) := by
      simp_rw [volume_eq_prod, prod_prod, volume_pi, pi_pi, Real.volume_ball]
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ w₀)]
      congr 2
      · refine Finset.prod_congr rfl (fun w' hw' ↦ ?_)
        rw [if_neg (Finset.ne_of_mem_erase hw'), Complex.volume_ball]
      · simpa only [ite_true] using vol_box (f w₀)
    _ = ((2 : ℝ≥0) ^ NrRealPlaces K *
          (∏ x : {w // InfinitePlace.IsReal w}, ENNReal.ofReal (f x.val))) *
            ((∏ x ∈ Finset.univ.erase  w₀, ENNReal.ofReal (f x.val) ^ 2) *
              ↑pi ^ (NrComplexPlaces K - 1) * (4 * (f w₀) ^ 2)) := by
      simp_rw [ofReal_mul (by norm_num : 0 ≤ (2 : ℝ)), Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ofReal_ofNat,
        ofReal_coe_nnreal, coe_ofNat]
    _ = convexBodyLT'Factor K * (∏ x : {w // InfinitePlace.IsReal w}, ENNReal.ofReal (f x.val))
        * (∏ x : {w // IsComplex w}, ENNReal.ofReal (f x.val) ^ 2) := by
      rw [show (4 : ℝ≥0∞) = (2 : ℝ≥0) ^ 2 by norm_num, convexBodyLT'Factor, pow_add,
        ← Finset.prod_erase_mul _ _ (Finset.mem_univ w₀), ofReal_coe_nnreal]
      simp_rw [coe_mul, ENNReal.coe_pow]
      ring
    _ = convexBodyLT'Factor K * ∏ w, (f w) ^ (mult w) := by
      simp_rw [mult, pow_ite, pow_one, Finset.prod_ite, ofReal_coe_nnreal, not_isReal_iff_isComplex,
        coe_mul, coe_finset_prod, ENNReal.coe_pow, mul_assoc]
      congr 3
      · refine (Finset.prod_subtype (Finset.univ.filter _) ?_ (fun w => (f w : ℝ≥0∞))).symm
        exact fun _ => by simp only [Finset.mem_univ, forall_true_left, Finset.mem_filter, true_and]
      · refine (Finset.prod_subtype (Finset.univ.filter _) ?_ (fun w => (f w : ℝ≥0∞) ^ 2)).symm
        exact fun _ => by simp only [Finset.mem_univ, forall_true_left, Finset.mem_filter, true_and]

end convexBodyLT'

section convexBodySum

open ENNReal MeasureTheory Fintype

open scoped Real Classical NNReal

variable [NumberField K] (B : ℝ)
variable {K}

/-- The function that sends `x : ({w // IsReal w} → ℝ) × ({w // IsComplex w} → ℂ)` to
  `∑ w, ‖x.1 w‖ + 2 * ∑ w, ‖x.2 w‖`. It defines a norm and it used to define `convexBodySum`. -/
noncomputable abbrev convexBodySumFun (x : E K) : ℝ := ∑ w, mult w * normAtPlace w x

theorem convexBodySumFun_apply (x : E K) :
    convexBodySumFun x = ∑ w,  mult w * normAtPlace w x := rfl

theorem convexBodySumFun_apply' (x : E K) :
    convexBodySumFun x = ∑ w, ‖x.1 w‖ + 2 * ∑ w, ‖x.2 w‖ := by
  simp_rw [convexBodySumFun_apply, ← Finset.sum_add_sum_compl {w | IsReal w}.toFinset,
    Set.toFinset_setOf, Finset.compl_filter, not_isReal_iff_isComplex, ← Finset.subtype_univ,
    ← Finset.univ.sum_subtype_eq_sum_filter, Finset.mul_sum]
  congr
  · ext w
    rw [mult, if_pos w.prop, normAtPlace_apply_isReal, Nat.cast_one, one_mul]
  · ext w
    rw [mult, if_neg (not_isReal_iff_isComplex.mpr w.prop), normAtPlace_apply_isComplex,
      Nat.cast_ofNat]

theorem convexBodySumFun_nonneg (x : E K) :
    0 ≤ convexBodySumFun x :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (Nat.cast_pos.mpr mult_pos).le (normAtPlace_nonneg _ _))

theorem convexBodySumFun_neg (x : E K) :
    convexBodySumFun (- x) = convexBodySumFun x := by
  simp_rw [convexBodySumFun, normAtPlace_neg]

theorem convexBodySumFun_add_le (x y : E K) :
    convexBodySumFun (x + y) ≤ convexBodySumFun x + convexBodySumFun y := by
  simp_rw [convexBodySumFun, ← Finset.sum_add_distrib, ← mul_add]
  exact Finset.sum_le_sum
    fun _ _ ↦ mul_le_mul_of_nonneg_left (normAtPlace_add_le _ x y) (Nat.cast_pos.mpr mult_pos).le

theorem convexBodySumFun_smul (c : ℝ) (x : E K) :
    convexBodySumFun (c • x) = |c| * convexBodySumFun x := by
  simp_rw [convexBodySumFun, normAtPlace_smul, ← mul_assoc, mul_comm, Finset.mul_sum, mul_assoc]

theorem convexBodySumFun_eq_zero_iff (x : E K) :
    convexBodySumFun x = 0 ↔ x = 0 := by
  rw [← normAtPlace_eq_zero, convexBodySumFun, Finset.sum_eq_zero_iff_of_nonneg fun _ _ =>
    mul_nonneg (Nat.cast_pos.mpr mult_pos).le (normAtPlace_nonneg _ _)]
  conv =>
    enter [1, w, hw]
    rw [mul_left_mem_nonZeroDivisors_eq_zero_iff
      (mem_nonZeroDivisors_iff_ne_zero.mpr <| Nat.cast_ne_zero.mpr mult_ne_zero)]
  simp_rw [Finset.mem_univ, true_implies]

theorem norm_le_convexBodySumFun (x : E K) : ‖x‖ ≤ convexBodySumFun x := by
  rw [norm_eq_sup'_normAtPlace]
  refine (Finset.sup'_le_iff _ _).mpr fun w _ ↦ ?_
  rw [convexBodySumFun_apply, ← Finset.univ.add_sum_erase _ (Finset.mem_univ w)]
  refine le_add_of_le_of_nonneg  ?_ ?_
  · exact le_mul_of_one_le_left (normAtPlace_nonneg w x) one_le_mult
  · exact Finset.sum_nonneg (fun _ _ => mul_nonneg (Nat.cast_pos.mpr mult_pos).le
      (normAtPlace_nonneg _ _))

variable (K)

theorem convexBodySumFun_continuous :
    Continuous (convexBodySumFun : (E K) → ℝ) := by
  refine continuous_finset_sum Finset.univ fun w ↦ ?_
  obtain hw | hw := isReal_or_isComplex w
  all_goals
  · simp only [normAtPlace_apply_isReal, normAtPlace_apply_isComplex, hw]
    fun_prop

/-- The convex body equal to the set of points `x : E` such that
  `∑ w real, ‖x w‖ + 2 * ∑ w complex, ‖x w‖ ≤ B`. -/
abbrev convexBodySum : Set (E K)  := { x | convexBodySumFun x ≤ B }

theorem convexBodySum_volume_eq_zero_of_le_zero {B} (hB : B ≤ 0) :
    volume (convexBodySum K B) = 0 := by
  obtain hB | hB := lt_or_eq_of_le hB
  · suffices convexBodySum K B = ∅ by rw [this, measure_empty]
    ext x
    refine ⟨fun hx => ?_, fun h => h.elim⟩
    rw [Set.mem_setOf] at hx
    linarith [convexBodySumFun_nonneg x]
  · suffices convexBodySum K B = { 0 } by rw [this, measure_singleton]
    ext
    rw [convexBodySum, Set.mem_setOf_eq, Set.mem_singleton_iff, hB, ← convexBodySumFun_eq_zero_iff]
    exact (convexBodySumFun_nonneg _).le_iff_eq

theorem convexBodySum_mem {x : K} :
    mixedEmbedding K x ∈ (convexBodySum K B) ↔
      ∑ w : InfinitePlace K, (mult w) * w.val x ≤ B := by
  simp_rw [Set.mem_setOf_eq, convexBodySumFun, normAtPlace_apply]
  rfl

theorem convexBodySum_neg_mem {x : E K} (hx : x ∈ (convexBodySum K B)) :
    -x ∈ (convexBodySum K B) := by
  rw [Set.mem_setOf, convexBodySumFun_neg]
  exact hx

theorem convexBodySum_convex : Convex ℝ (convexBodySum K B) := by
  refine Convex_subadditive_le (fun _ _ => convexBodySumFun_add_le _ _) (fun c x h => ?_) B
  convert le_of_eq (convexBodySumFun_smul c x)
  exact (abs_eq_self.mpr h).symm

theorem convexBodySum_isBounded : Bornology.IsBounded (convexBodySum K B) := by
  refine Metric.isBounded_iff.mpr ⟨B + B, fun x hx y hy => ?_⟩
  refine le_trans (norm_sub_le x y) (add_le_add ?_ ?_)
  · exact le_trans (norm_le_convexBodySumFun x) hx
  · exact le_trans (norm_le_convexBodySumFun y) hy

theorem convexBodySum_compact : IsCompact (convexBodySum K B) := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  refine ⟨?_, convexBodySum_isBounded K B⟩
  convert IsClosed.preimage (convexBodySumFun_continuous K) (isClosed_Icc : IsClosed (Set.Icc 0 B))
  ext
  simp [convexBodySumFun_nonneg]

/-- The fudge factor that appears in the formula for the volume of `convexBodyLt`. -/
noncomputable abbrev convexBodySumFactor : ℝ≥0 :=
  (2 : ℝ≥0) ^ NrRealPlaces K * (NNReal.pi / 2) ^ NrComplexPlaces K / (finrank ℚ K).factorial

theorem convexBodySumFactor_ne_zero : convexBodySumFactor K ≠ 0 := by
  refine div_ne_zero ?_ <| Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  exact mul_ne_zero (pow_ne_zero _ two_ne_zero)
    (pow_ne_zero _ (div_ne_zero NNReal.pi_ne_zero two_ne_zero))

open MeasureTheory MeasureTheory.Measure Real in
theorem convexBodySum_volume :
    volume (convexBodySum K B) = (convexBodySumFactor K) * (.ofReal B) ^ (finrank ℚ K) := by
  obtain hB | hB := le_or_lt B 0
  · rw [convexBodySum_volume_eq_zero_of_le_zero K hB, ofReal_eq_zero.mpr hB, zero_pow, mul_zero]
    exact finrank_pos.ne'
  · suffices volume (convexBodySum K 1) = (convexBodySumFactor K) by
      rw [mul_comm]
      convert addHaar_smul volume B (convexBodySum K 1)
      · simp_rw [← Set.preimage_smul_inv₀ (ne_of_gt hB), Set.preimage_setOf_eq, convexBodySumFun,
        normAtPlace_smul, abs_inv, abs_eq_self.mpr (le_of_lt hB), ← mul_assoc, mul_comm, mul_assoc,
        ← Finset.mul_sum, inv_mul_le_iff hB, mul_one]
      · rw [abs_pow, ofReal_pow (abs_nonneg _), abs_eq_self.mpr (le_of_lt hB),
          mixedEmbedding.finrank]
      · exact this.symm
    rw [MeasureTheory.measure_le_eq_lt _ ((convexBodySumFun_eq_zero_iff 0).mpr rfl)
      convexBodySumFun_neg convexBodySumFun_add_le
      (fun hx => (convexBodySumFun_eq_zero_iff _).mp hx)
      (fun r x => le_of_eq (convexBodySumFun_smul r x))]
    rw [measure_lt_one_eq_integral_div_gamma (g := fun x : (E K) => convexBodySumFun x)
      volume ((convexBodySumFun_eq_zero_iff 0).mpr rfl) convexBodySumFun_neg convexBodySumFun_add_le
      (fun hx => (convexBodySumFun_eq_zero_iff _).mp hx)
      (fun r x => le_of_eq (convexBodySumFun_smul r x)) zero_lt_one]
    simp_rw [mixedEmbedding.finrank, div_one, Gamma_nat_eq_factorial, ofReal_div_of_pos
      (Nat.cast_pos.mpr (Nat.factorial_pos _)), Real.rpow_one, ofReal_natCast]
    suffices ∫ x : E K, exp (-convexBodySumFun x) =
        (2:ℝ) ^ NrRealPlaces K * (π / 2) ^ NrComplexPlaces K by
      rw [this, convexBodySumFactor, ofReal_mul (by positivity), ofReal_pow zero_le_two,
        ofReal_pow (by positivity), ofReal_div_of_pos zero_lt_two, ofReal_ofNat,
        ← NNReal.coe_real_pi, ofReal_coe_nnreal, coe_div (Nat.cast_ne_zero.mpr
        (Nat.factorial_ne_zero _)), coe_mul, coe_pow, coe_pow, coe_ofNat, coe_div two_ne_zero,
        coe_ofNat, coe_natCast]
    calc
      _ = (∫ x : {w : InfinitePlace K // IsReal w} → ℝ, ∏ w, exp (- ‖x w‖)) *
              (∫ x : {w : InfinitePlace K // IsComplex w} → ℂ, ∏ w, exp (- 2 * ‖x w‖)) := by
        simp_rw [convexBodySumFun_apply', neg_add, ← neg_mul, Finset.mul_sum,
          ← Finset.sum_neg_distrib, exp_add, exp_sum, ← integral_prod_mul, volume_eq_prod]
      _ = (∫ x : ℝ, exp (-|x|)) ^ NrRealPlaces K *
              (∫ x : ℂ, Real.exp (-2 * ‖x‖)) ^ NrComplexPlaces K := by
        rw [integral_fintype_prod_eq_pow _ (fun x => exp (- ‖x‖)), integral_fintype_prod_eq_pow _
          (fun x => exp (- 2 * ‖x‖))]
        simp_rw [norm_eq_abs]
      _ =  (2 * Gamma (1 / 1 + 1)) ^ NrRealPlaces K *
              (π * (2:ℝ) ^ (-(2:ℝ) / 1) * Gamma (2 / 1 + 1)) ^ NrComplexPlaces K := by
        rw [integral_comp_abs (f := fun x => exp (- x)), ← integral_exp_neg_rpow zero_lt_one,
          ← Complex.integral_exp_neg_mul_rpow le_rfl zero_lt_two]
        simp_rw [Real.rpow_one]
      _ = (2:ℝ) ^ NrRealPlaces K * (π / 2) ^ NrComplexPlaces K := by
        simp_rw [div_one, one_add_one_eq_two, Gamma_add_one two_ne_zero, Gamma_two, mul_one,
          mul_assoc, ← Real.rpow_add_one two_ne_zero, show (-2:ℝ) + 1 = -1 by norm_num,
          Real.rpow_neg_one]
        rfl

end convexBodySum

section minkowski

open scoped Classical
open MeasureTheory MeasureTheory.Measure FiniteDimensional Zspan Real Submodule

open scoped ENNReal NNReal nonZeroDivisors IntermediateField

variable [NumberField K] (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

/-- The bound that appears in **Minkowski Convex Body theorem**, see
`MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`. See
`NumberField.mixedEmbedding.volume_fundamentalDomain_idealLatticeBasis_eq` and
`NumberField.mixedEmbedding.volume_fundamentalDomain_latticeBasis` for the computation of
`volume (fundamentalDomain (idealLatticeBasis K))`. -/
noncomputable def minkowskiBound : ℝ≥0∞ :=
  volume (fundamentalDomain (fractionalIdealLatticeBasis K I)) * (2 : ℝ≥0∞) ^ (finrank ℝ (E K))

theorem volume_fundamentalDomain_fractionalIdealLatticeBasis :
    volume (fundamentalDomain (fractionalIdealLatticeBasis K I)) =
      .ofReal (FractionalIdeal.absNorm I.1) *  volume (fundamentalDomain (latticeBasis K)) := by
  let e : (Module.Free.ChooseBasisIndex ℤ I) ≃ (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) := by
    refine Fintype.equivOfCardEq ?_
    rw [← finrank_eq_card_chooseBasisIndex, ← finrank_eq_card_chooseBasisIndex,
      fractionalIdeal_rank]
  rw [← fundamentalDomain_reindex (fractionalIdealLatticeBasis K I) e,
    measure_fundamentalDomain ((fractionalIdealLatticeBasis K I).reindex e)]
  · rw [show (fractionalIdealLatticeBasis K I).reindex e = (mixedEmbedding K) ∘
        (basisOfFractionalIdeal K I) ∘ e.symm by
      ext1; simp only [Basis.coe_reindex, Function.comp_apply, fractionalIdealLatticeBasis_apply]]
    rw [mixedEmbedding.det_basisOfFractionalIdeal_eq_norm]

theorem minkowskiBound_lt_top : minkowskiBound K I < ⊤ := by
  refine ENNReal.mul_lt_top ?_ ?_
  · exact ne_of_lt (fundamentalDomain_isBounded _).measure_lt_top
  · exact ne_of_lt (ENNReal.pow_lt_top (lt_top_iff_ne_top.mpr ENNReal.two_ne_top) _)

theorem minkowskiBound_pos : 0 < minkowskiBound K I := by
  refine zero_lt_iff.mpr (mul_ne_zero ?_ ?_)
  · exact Zspan.measure_fundamentalDomain_ne_zero _
  · exact ENNReal.pow_ne_zero two_ne_zero _

variable {f : InfinitePlace K → ℝ≥0} (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

/-- Let `I` be a fractional ideal of `K`. Assume that `f : InfinitePlace K → ℝ≥0` is such that
`minkowskiBound K I < volume (convexBodyLT K f)` where `convexBodyLT K f` is the set of
points `x` such that `‖x w‖ < f w` for all infinite places `w` (see `convexBodyLT_volume` for
the computation of this volume), then there exists a nonzero algebraic number `a` in `I` such
that `w a < f w` for all infinite places `w`. -/
theorem exists_ne_zero_mem_ideal_lt (h : minkowskiBound K I < volume (convexBodyLT K f)) :
    ∃ a ∈ (I : FractionalIdeal (𝓞 K)⁰ K), a ≠ 0 ∧ ∀ w : InfinitePlace K, w a < f w := by
  have h_fund := Zspan.isAddFundamentalDomain (fractionalIdealLatticeBasis K I) volume
  have : Countable (span ℤ (Set.range (fractionalIdealLatticeBasis K I))).toAddSubgroup := by
    change Countable (span ℤ (Set.range (fractionalIdealLatticeBasis K I)) : Set (E K))
    infer_instance
  obtain ⟨⟨x, hx⟩, h_nz, h_mem⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    h_fund (convexBodyLT_neg_mem K f) (convexBodyLT_convex K f) h
  rw [mem_toAddSubgroup, mem_span_fractionalIdealLatticeBasis] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨a, ha, by simpa using h_nz, (convexBodyLT_mem K f).mp h_mem⟩

/-- A version of `exists_ne_zero_mem_ideal_lt` where the absolute value of the real part of `a` is
smaller than `1` at some fixed complex place. This is useful to ensure that `a` is not real. -/
theorem exists_ne_zero_mem_ideal_lt' (w₀ : {w : InfinitePlace K // IsComplex w})
    (h : minkowskiBound K I < volume (convexBodyLT' K f w₀)) :
    ∃ a ∈ (I : FractionalIdeal (𝓞 K)⁰ K), a ≠ 0 ∧ (∀ w : InfinitePlace K, w ≠ w₀ → w a < f w) ∧
      |(w₀.val.embedding a).re| < 1 ∧ |(w₀.val.embedding a).im| < (f w₀ : ℝ) ^ 2:= by
  have h_fund := Zspan.isAddFundamentalDomain (fractionalIdealLatticeBasis K I) volume
  have : Countable (span ℤ (Set.range (fractionalIdealLatticeBasis K I))).toAddSubgroup := by
    change Countable (span ℤ (Set.range (fractionalIdealLatticeBasis K I)) : Set (E K))
    infer_instance
  obtain ⟨⟨x, hx⟩, h_nz, h_mem⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    h_fund (convexBodyLT'_neg_mem K f w₀) (convexBodyLT'_convex K f w₀) h
  rw [mem_toAddSubgroup, mem_span_fractionalIdealLatticeBasis] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨a, ha, by simpa using h_nz, (convexBodyLT'_mem K f w₀).mp h_mem⟩

/-- A version of `exists_ne_zero_mem_ideal_lt` for the ring of integers of `K`. -/
theorem exists_ne_zero_mem_ringOfIntegers_lt (h : minkowskiBound K ↑1 < volume (convexBodyLT K f)) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ ∀ w : InfinitePlace K, w a < f w := by
  obtain ⟨_, h_mem, h_nz, h_bd⟩ := exists_ne_zero_mem_ideal_lt K ↑1 h
  obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp h_mem
  exact ⟨a, RingOfIntegers.coe_ne_zero_iff.mp h_nz, h_bd⟩

/-- A version of `exists_ne_zero_mem_ideal_lt'` for the ring of integers of `K`. -/
theorem exists_ne_zero_mem_ringOfIntegers_lt' (w₀ : {w : InfinitePlace K // IsComplex w})
    (h : minkowskiBound K ↑1 < volume (convexBodyLT' K f w₀)) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ (∀ w : InfinitePlace K, w ≠ w₀ → w a < f w) ∧
      |(w₀.val.embedding a).re| < 1 ∧ |(w₀.val.embedding a).im| < (f w₀ : ℝ) ^ 2 := by
  obtain ⟨_, h_mem, h_nz, h_bd⟩ := exists_ne_zero_mem_ideal_lt' K ↑1 w₀ h
  obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp h_mem
  exact ⟨a, RingOfIntegers.coe_ne_zero_iff.mp h_nz, h_bd⟩

theorem exists_primitive_element_lt_of_isReal {w₀ : InfinitePlace K} (hw₀ : IsReal w₀) {B : ℝ≥0}
    (hB : minkowskiBound K ↑1 < convexBodyLTFactor K * B) :
    ∃ a : 𝓞 K, ℚ⟮(a : K)⟯ = ⊤ ∧
      ∀ w : InfinitePlace K, w a < max B 1 := by
  have : minkowskiBound K ↑1 < volume (convexBodyLT K (fun w ↦ if w = w₀ then B else 1)) := by
    rw [convexBodyLT_volume, ← Finset.prod_erase_mul _ _ (Finset.mem_univ w₀)]
    simp_rw [ite_pow, one_pow]
    rw [Finset.prod_ite_eq']
    simp_rw [Finset.not_mem_erase, ite_false, mult, hw₀, ite_true, one_mul, pow_one]
    exact hB
  obtain ⟨a, h_nz, h_le⟩ := exists_ne_zero_mem_ringOfIntegers_lt K this
  refine ⟨a, ?_, fun w ↦ lt_of_lt_of_le (h_le w) ?_⟩
  · exact is_primitive_element_of_infinitePlace_lt h_nz
      (fun w h_ne ↦ by convert (if_neg h_ne) ▸ h_le w) (Or.inl hw₀)
  · split_ifs <;> simp

theorem exists_primitive_element_lt_of_isComplex {w₀ : InfinitePlace K} (hw₀ : IsComplex w₀)
    {B : ℝ≥0} (hB : minkowskiBound K ↑1 < convexBodyLT'Factor K * B) :
    ∃ a : 𝓞 K, ℚ⟮(a : K)⟯ = ⊤ ∧
      ∀ w : InfinitePlace K, w a < Real.sqrt (1 + B ^ 2) := by
  have : minkowskiBound K ↑1 <
      volume (convexBodyLT' K (fun w ↦ if w = w₀ then NNReal.sqrt B else 1) ⟨w₀, hw₀⟩) := by
    rw [convexBodyLT'_volume, ← Finset.prod_erase_mul _ _ (Finset.mem_univ w₀)]
    simp_rw [ite_pow, one_pow]
    rw [Finset.prod_ite_eq']
    simp_rw [Finset.not_mem_erase, ite_false, mult, not_isReal_iff_isComplex.mpr hw₀,
      ite_true, ite_false, one_mul, NNReal.sq_sqrt]
    exact hB
  obtain ⟨a, h_nz, h_le, h_le₀⟩ := exists_ne_zero_mem_ringOfIntegers_lt' K ⟨w₀, hw₀⟩ this
  refine ⟨a, ?_, fun w ↦ ?_⟩
  · exact is_primitive_element_of_infinitePlace_lt h_nz
      (fun w h_ne ↦ by convert if_neg h_ne ▸ h_le w h_ne) (Or.inr h_le₀.1)
  · by_cases h_eq : w = w₀
    · rw [if_pos rfl] at h_le₀
      dsimp only at h_le₀
      rw [h_eq, ← norm_embedding_eq, Real.lt_sqrt (norm_nonneg _), ← Complex.re_add_im
        (embedding w₀ _), Complex.norm_eq_abs, Complex.abs_add_mul_I, Real.sq_sqrt (by positivity)]
      refine add_lt_add ?_ ?_
      · rw [← sq_abs, sq_lt_one_iff (abs_nonneg _)]
        exact h_le₀.1
      · rw [sq_lt_sq, NNReal.abs_eq, ← NNReal.sq_sqrt B]
        exact h_le₀.2
    · refine lt_of_lt_of_le (if_neg h_eq ▸ h_le w h_eq) ?_
      rw [NNReal.coe_one, Real.le_sqrt' zero_lt_one, one_pow]
      set_option tactic.skipAssignedInstances false in norm_num

/-- Let `I` be a fractional ideal of `K`. Assume that `B : ℝ` is such that
`minkowskiBound K I < volume (convexBodySum K B)` where `convexBodySum K B` is the set of points
`x` such that `∑ w real, ‖x w‖ + 2 * ∑ w complex, ‖x w‖ ≤ B` (see `convexBodySum_volume` for
the computation of this volume), then there exists a nonzero algebraic number `a` in `I` such
that `|Norm a| < (B / d) ^ d` where `d` is the degree of `K`. -/
theorem exists_ne_zero_mem_ideal_of_norm_le {B : ℝ}
    (h : (minkowskiBound K I) ≤ volume (convexBodySum K B)) :
    ∃ a ∈ (I : FractionalIdeal (𝓞 K)⁰ K), a ≠ 0 ∧
      |Algebra.norm ℚ (a:K)| ≤ (B / finrank ℚ K) ^ finrank ℚ K := by
  have hB : 0 ≤ B := by
    contrapose! h
    rw [convexBodySum_volume_eq_zero_of_le_zero K (le_of_lt h)]
    exact minkowskiBound_pos K I
  -- Some inequalities that will be useful later on
  have h1 : 0 < (finrank ℚ K : ℝ)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr finrank_pos)
  have h2 : 0 ≤ B / (finrank ℚ K) := div_nonneg hB (Nat.cast_nonneg _)
  have h_fund := Zspan.isAddFundamentalDomain (fractionalIdealLatticeBasis K I) volume
  have : Countable (span ℤ (Set.range (fractionalIdealLatticeBasis K I))).toAddSubgroup := by
    change Countable (span ℤ (Set.range (fractionalIdealLatticeBasis K I)): Set (E K))
    infer_instance
  obtain ⟨⟨x, hx⟩, h_nz, h_mem⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
      h_fund (fun _ ↦ convexBodySum_neg_mem K B) (convexBodySum_convex K B)
      (convexBodySum_compact K B) h
  rw [mem_toAddSubgroup, mem_span_fractionalIdealLatticeBasis] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  refine ⟨a, ha, by simpa using h_nz, ?_⟩
  rw [← rpow_natCast, ← rpow_le_rpow_iff (by simp only [Rat.cast_abs, abs_nonneg])
      (rpow_nonneg h2 _) h1, ← rpow_mul h2,  mul_inv_cancel (Nat.cast_ne_zero.mpr
      (ne_of_gt finrank_pos)), rpow_one, le_div_iff' (Nat.cast_pos.mpr finrank_pos)]
  refine le_trans ?_ ((convexBodySum_mem K B).mp h_mem)
  rw [← le_div_iff' (Nat.cast_pos.mpr finrank_pos), ← sum_mult_eq, Nat.cast_sum]
  refine le_trans ?_ (geom_mean_le_arith_mean Finset.univ _ _ (fun _ _ => Nat.cast_nonneg _)
    ?_ (fun _ _ => AbsoluteValue.nonneg _ _))
  · simp_rw [← prod_eq_abs_norm, rpow_natCast]
    exact le_of_eq rfl
  · rw [← Nat.cast_sum, sum_mult_eq, Nat.cast_pos]
    exact finrank_pos

theorem exists_ne_zero_mem_ringOfIntegers_of_norm_le {B : ℝ}
    (h : (minkowskiBound K ↑1) ≤ volume (convexBodySum K B)) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ |Algebra.norm ℚ (a : K)| ≤ (B / finrank ℚ K) ^ finrank ℚ K := by
  obtain ⟨_, h_mem, h_nz, h_bd⟩ := exists_ne_zero_mem_ideal_of_norm_le K ↑1 h
  obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp h_mem
  exact ⟨a, RingOfIntegers.coe_ne_zero_iff.mp h_nz, h_bd⟩

end minkowski

end NumberField.mixedEmbedding
