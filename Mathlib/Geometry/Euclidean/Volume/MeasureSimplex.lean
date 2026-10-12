/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Geometry.Euclidean.Volume.Def
public import Mathlib.Geometry.Euclidean.Volume.Measure

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Connect the algebraic definition and measure theory for the volume of a simplex

This file proves that `Affine.Simplex.volume` agrees with the volume measure of its closed
interior.

## Main statements
* `EuclideanGeometry.euclideanHausdorffMeasure_cone`: the volume of a cone over an arbitrary
  measurable base is `h * b / n`, where `h` is the height and `b` is the volume of the base.
* `Affine.Simplex.euclideanHausdorffMeasure_real_closedInterior`: the volume measure of the closed
  interior of a simplex satisfies the recurrence relation with base and height.
* `Affine.Simplex.volume_eq_euclideanHausdorffMeasure_real_closedInterior`: `Affine.Simplex.volume`
  is equal to the volume measure of the closed interior.
-/

open MeasureTheory Measure Module Submodule AffineSubspace
open scoped ENNReal NNReal

public section

section Cone

open Set
open scoped RealInnerProductSpace

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P] [MeasurableSpace P] [BorelSpace P]

namespace EuclideanGeometry

/-- **Volume of a cone**: in a Euclidean affine subspace `T` of dimension `d + 1`, the cone with
apex `a` over a measurable base `B` contained in an affine subspace `S ≤ T` not containing `a` has
volume `h * b / (d + 1)`, where `h` is the distance from `a` to `S` and `b` is the `d`-volume of
`B`. -/
theorem euclideanHausdorffMeasure_cone {T S : AffineSubspace ℝ P} [FiniteDimensional ℝ T.direction]
    [Nonempty S] [S.direction.HasOrthogonalProjection] (hST : S ≤ T) {d : ℕ}
    (hT : finrank ℝ T.direction = d + 1) {a : P} (haT : a ∈ T) (ha : a ∉ S) {B : Set P}
    (hBS : B ⊆ S) (hB : MeasurableSet B) :
    μHE[d + 1] (⋃ t ∈ Icc (0 : ℝ) 1, AffineMap.homothety a t '' B) =
      ((d + 1 : ℕ) : ℝ≥0∞)⁻¹ * .ofReal (dist a (orthogonalProjection S a)) * μHE[d] B := by
  borelize V
  set K := ⋃ t ∈ Icc (0 : ℝ) 1, AffineMap.homothety a t '' B
  set f : P := (orthogonalProjection S a : P)
  set w : V := f -ᵥ a
  have hw : w ≠ 0 := vsub_ne_zero.2 fun h ↦ ha (h ▸ orthogonalProjection_mem a)
  have hw2 : 0 < ‖w‖ ^ 2 := by positivity
  -- every point of `S` lies at level `1` along `w`
  have hlevel (b : P) (hb : b ∈ S) : ⟪w, b -ᵥ a⟫ = ‖w‖ ^ 2 := by
    rw [← vsub_add_vsub_cancel b f a, inner_add_right,
      S.direction.inner_left_of_mem_orthogonal (vsub_mem_direction hb (orthogonalProjection_mem a))
        (orthogonalProjection_vsub_mem_direction_orthogonal S a), zero_add,
      real_inner_self_eq_norm_sq]
  have hhom (t : ℝ) (b : P) : AffineMap.homothety a t b -ᵥ a = t • (b -ᵥ a) := by
    simp [AffineMap.homothety_apply]
  -- the slice of the cone at level `x ∈ (0, 1]` is the image of `B` by a homothety
  have hslice (x : ℝ) (hx : x ≠ 0) :
      K ∩ mk' (x • w +ᵥ a) (ℝ ∙ w)ᗮ = if x ∈ Ioc 0 1 then AffineMap.homothety a x '' B else ∅ := by
    have hmem (y : P) : y ∈ mk' (x • w +ᵥ a) (ℝ ∙ w)ᗮ ↔ ⟪w, y -ᵥ a⟫ = x * ‖w‖ ^ 2 := by
      rw [mem_mk', Submodule.mem_orthogonal_singleton_iff_inner_right,
        vsub_vadd_eq_vsub_sub, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq,
        sub_eq_zero]
    have hlev (t : ℝ) (b : P) (hb : b ∈ B) :
        ⟪w, AffineMap.homothety a t b -ᵥ a⟫ = t * ‖w‖ ^ 2 := by
      rw [hhom, inner_smul_right, hlevel b (hBS hb)]
    ext y
    simp only [K, mem_inter_iff, mem_iUnion, mem_image, SetLike.mem_coe, hmem, exists_prop]
    split_ifs with hx'
    · constructor
      · rintro ⟨⟨t, -, b, hb, rfl⟩, hy⟩
        rw [hlev t b hb] at hy
        exact ⟨b, hb, by rw [mul_right_cancel₀ hw2.ne' hy]⟩
      · rintro ⟨b, hb, rfl⟩
        exact ⟨⟨x, Ioc_subset_Icc_self hx', b, hb, rfl⟩, hlev x b hb⟩
    · simp only [mem_empty_iff_false, iff_false, not_and]
      rintro ⟨t, ht, b, hb, rfl⟩ hy
      rw [hlev t b hb] at hy
      obtain rfl := mul_right_cancel₀ hw2.ne' hy
      exact hx' ⟨lt_of_le_of_ne ht.1 (Ne.symm hx), ht.2⟩
  -- the cone is measurable: away from the apex, it is a preimage of `B`
  have hK : MeasurableSet K := by
    set lev : P → ℝ := fun y ↦ ⟪w, y -ᵥ a⟫ / ‖w‖ ^ 2
    have hK' : K = ({y | lev y ∈ Ioc 0 1} ∩
        (fun y ↦ AffineMap.homothety a (lev y)⁻¹ y) ⁻¹' B) ∪ (K ∩ {a}) := by
      ext y
      constructor
      · intro hy
        by_cases hya : y = a
        · exact Or.inr ⟨hy, hya⟩
        left
        obtain ⟨t, ht, b, hb, rfl⟩ : ∃ t ∈ Icc (0 : ℝ) 1, ∃ b ∈ B,
            AffineMap.homothety a t b = y := by simpa [K] using hy
        have ht0 : t ≠ 0 := by rintro rfl; simp at hya
        have hlt : lev (AffineMap.homothety a t b) = t := by
          simp only [lev, hhom, inner_smul_right, hlevel b (hBS hb)]
          field_simp
        refine ⟨by simpa [hlt] using ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2⟩, ?_⟩
        simpa [hlt, ← AffineMap.homothety_mul_apply, inv_mul_cancel₀ ht0] using hb
      · rintro (⟨hlev, hb⟩ | ⟨hy, -⟩)
        · refine mem_iUnion₂.2 ⟨lev y, Ioc_subset_Icc_self hlev, _, hb, ?_⟩
          rw [← AffineMap.homothety_mul_apply, mul_inv_cancel₀ hlev.1.ne', AffineMap.homothety_one,
            AffineMap.id_apply]
        · exact hy
    have hlevm : Measurable lev :=
      ((continuous_const.inner (continuous_id.vsub continuous_const)).div_const _).measurable
    rw [hK']
    refine MeasurableSet.union (MeasurableSet.inter ?_ (hB.preimage ?_))
      ((subsingleton_singleton.anti inter_subset_right).measurableSet)
    · exact measurableSet_Ioc.preimage hlevm
    · simp only [AffineMap.homothety_apply]
      have hψ : Continuous fun q : ℝ × P ↦ q.1 • (q.2 -ᵥ a) +ᵥ a :=
        (continuous_fst.smul (continuous_snd.vsub continuous_const)).vadd continuous_const
      exact hψ.measurable.comp (hlevm.inv.prodMk measurable_id)
  -- integrate the volume of the slices along `w`
  have hae : (fun x : ℝ ↦ μHE[d] (K ∩ mk' (x • w +ᵥ a) (ℝ ∙ w)ᗮ)) =ᵐ[volume]
      (Ioc 0 1).indicator fun x ↦ ((‖x‖₊ ^ d : ℝ≥0) : ℝ≥0∞) * μHE[d] B := by
    filter_upwards [(ae_iff (p := fun x : ℝ ↦ x ≠ 0)).2 (by simp)] with x hx
    rw [hslice x hx]
    split_ifs with hx'
    · rw [indicator_of_mem hx', euclideanHausdorffMeasure_homothety_image _ _ hx, ENNReal.smul_def,
        smul_eq_mul]
    · rw [indicator_of_notMem hx', measure_empty]
  have hint : ∫⁻ x in Ioc (0 : ℝ) 1, ((‖x‖₊ ^ d : ℝ≥0) : ℝ≥0∞) = ((d + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
    calc
      _ = ENNReal.ofReal (∫ x in Ioc (0 : ℝ) 1, ((‖x‖₊ ^ d : ℝ≥0) : ℝ)) :=
        lintegral_coe_eq_integral _ (Continuous.integrableOn_Ioc (by fun_prop))
      _ = ENNReal.ofReal (∫ x in Ioc (0 : ℝ) 1, x ^ d) :=
        congrArg _ (setIntegral_congr_fun measurableSet_Ioc fun x hx ↦ by
          simp [abs_of_nonneg hx.1.le])
      _ = ((d + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
        rw [← intervalIntegral.integral_of_le zero_le_one, integral_pow,
          ← ENNReal.ofReal_natCast (d + 1), ← ENNReal.ofReal_inv_of_pos (by positivity)]
        norm_num
  have hwT : w ∈ T.direction := vsub_mem_direction (hST (orthogonalProjection_mem a)) haT
  have hKT : K ⊆ T := iUnion₂_subset fun t _ ↦ image_subset_iff.2 fun b hb ↦
    AffineMap.homothety_mem haT t (hST (hBS hb))
  conv_lhs => rw [← hT]
  rw [euclideanHausdorffMeasure_eq_lintegral_of_subset a hw hK hwT hKT, hT, Nat.add_sub_cancel,
    lintegral_congr_ae hae, lintegral_indicator measurableSet_Ioc,
    lintegral_mul_const _ (by fun_prop), hint,
    ← ofReal_norm, ← dist_eq_norm_vsub']
  ring

end EuclideanGeometry

end Cone

namespace Affine.Simplex
variable {V P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [MetricSpace P] [NormedAddTorsor V P] [MeasurableSpace P] [BorelSpace P]
variable {n : ℕ}

theorem measurableSet_closedInterior (s : Simplex ℝ P n) : MeasurableSet s.closedInterior :=
  s.isClosed_closedInterior.measurableSet

/-- The volume of the cross section of a simplex is scaled from the base. This is an intermediate
result for volume calculation and is expressed as a.e.-equal to take care of the exception at zero.

TODO: if the cross section object also shows up elsewhere, we should turn it to a proper definition.
-/
theorem euclideanHausdorffMeasure_closedInterior_inter_shift_aeEq (s : Simplex ℝ P (n + 1))
    (i : Fin (n + 2)) :
    (μHE[n] <| s.closedInterior ∩ (affineSpan ℝ (s.points '' {i}ᶜ)).shift (s.points i) ·)
      =ᵐ[MeasureSpace.volume.restrict (Set.Icc 0 1)]
        (‖·‖₊ ^ n • μHE[n] (s.faceOpposite i).closedInterior) := by
  rw [← restrict_Ioc_eq_restrict_Icc]
  refine ae_restrict_of_forall_mem (by simp) fun x hx ↦ ?_
  simp [s.closedInterior_inter_shift_eq_homothety i (Set.Ioc_subset_Icc_self hx),
    euclideanHausdorffMeasure_homothety_image _ _ hx.1.ne.symm]

/-- The cross section of a simplex vanishes outside of the simplex in terms of its volume. -/
theorem support_euclideanHausdorffMeasure_closedInterior_inter_shift_subset
    (s : Simplex ℝ P (n + 1)) (i : Fin (n + 2)) :
    Function.support (μHE[n] <| s.closedInterior ∩
      (affineSpan ℝ (s.points '' {i}ᶜ)).shift (s.points i) ·) ⊆ Set.Icc 0 1 := by
  refine Function.support_subset_iff'.mpr fun x hx ↦ ?_
  rw [(s.disjoint_closedInterior_shift i (by grind)).inter_eq, measure_empty]

/-- The $n$-volume of the closed interior of a $n$-simplex is equal to $h * b / n$, where $h$ is the
height and $b$ is the $(n - 1)$-volume of the base. This version is expressed in `ENNReal`. -/
theorem euclideanHausdorffMeasure_closedInterior (s : Simplex ℝ P (n + 1)) (i : Fin (n + 2)) :
    μHE[n + 1] s.closedInterior =
      ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ * .ofReal (s.height i) * μHE[n] (s.faceOpposite i).closedInterior := by
  have hn : finrank ℝ (affineSpan ℝ (Set.range s.points)).direction = n + 1 := by
    rw [direction_affineSpan]
    exact s.independent.finrank_vectorSpan (by simp)
  rw [s.closedInterior_eq_iUnion_homothety i]
  exact EuclideanGeometry.euclideanHausdorffMeasure_cone
    (affineSpan_mono _ (by rw [range_faceOpposite_points]; exact Set.image_subset_range _ _))
    hn (mem_affineSpan _ (Set.mem_range_self i)) (s.points_notMem_affineSpan_faceOpposite i)
    (s.faceOpposite i).closedInterior_subset_affineSpan
    (s.faceOpposite i).measurableSet_closedInterior

/-- The $n$-volume of the closed interior of a $n$-simplex is equal to $h * b / n$, where $h$ is the
height and $b$ is the $(n - 1)$-volume of the base. This version is expressed in `Real`. -/
theorem euclideanHausdorffMeasure_real_closedInterior (s : Simplex ℝ P (n + 1)) (i : Fin (n + 2)) :
    μHE[n + 1].real s.closedInterior =
      (↑(n + 1))⁻¹ * s.height i * μHE[n].real (s.faceOpposite i).closedInterior := by
  simp_rw [measureReal_def]
  rw [s.euclideanHausdorffMeasure_closedInterior i, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (s.height_pos i).le, ENNReal.toReal_inv, ENNReal.toReal_natCast]

theorem euclideanHausdorffMeasure_closedInterior_eq_one (s : Simplex ℝ P 0) :
    μHE[0] s.closedInterior = 1 := by
  simp

theorem euclideanHausdorffMeasure_closedInterior_real_eq_one (s : Simplex ℝ P 0) :
    μHE[0].real s.closedInterior = 1 := by
  simp [real_def]

/-- `Affine.Simplex.volume` is equal to the Euclidean Hausdorff measure of the closed interior. -/
theorem volume_eq_euclideanHausdorffMeasure_real_closedInterior (s : Simplex ℝ P n) :
    s.volume = μHE[n].real s.closedInterior := by
  induction n with
  | zero => rw [euclideanHausdorffMeasure_closedInterior_real_eq_one, volume]
  | succ n ih => simp [volume, s.euclideanHausdorffMeasure_real_closedInterior 0, ih]

/-- `Affine.Simplex.volume` is equal to the Lebesgue measure of the closed interior. -/
theorem volume_eq_volume_real_closedInterior [MeasurableSpace V] [BorelSpace V]
    [FiniteDimensional ℝ V] (hn : finrank ℝ V = n) (s : Simplex ℝ V n) :
    s.volume = MeasureTheory.MeasureSpace.volume.real s.closedInterior := by
  simp_rw [volume_eq_euclideanHausdorffMeasure_real_closedInterior, ← hn,
    InnerProductSpace.euclideanHausdorffMeasure_eq_volume]

end Affine.Simplex
