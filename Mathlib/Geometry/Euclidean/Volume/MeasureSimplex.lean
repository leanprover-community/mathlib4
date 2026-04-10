/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.Geometry.Euclidean.Volume.Def
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Shift

/-!
# Connects the algebraic definition and measure theory for the volume of a simplex
-/


open MeasureTheory Measure Module Submodule

public section
variable {k V P : Type*}
variable [Field k] [AddCommGroup V] [AddTorsor V P] [Module k V]

-- Move this
theorem Affine.Simplex.closedInterior_inter_mapHomothety_eq_empty [LinearOrder k]
    [IsStrictOrderedRing k]
    {n : ℕ} [NeZero n] (s : Simplex k P n) (i : Fin (n + 1)) {x : k} (hx : x ∉ Set.Icc 0 1) :
    s.closedInterior ∩ (affineSpan k (Set.range (s.faceOpposite i).points)).shift (s.points i) x =
    ∅ := by
  have hx0 : x ≠ 0 := by
    contrapose! hx
    simp [hx]
  by_contra! h
  obtain ⟨z, hzi, hzs⟩ := h
  rw [AffineSubspace.shift_eq_map_homothety _ _ (IsUnit.mk0 _ hx0)] at hzs
  obtain hz := Set.mem_of_mem_of_subset hzi s.closedInterior_subset_affineSpan
  obtain ⟨w, hw1, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hz
  rw [s.affineCombination_mem_closedInterior_iff hw1] at hzi
  have hxi : 1 - x⁻¹ + x⁻¹ * w i ≠ 0 := by
    contrapose! hx
    have : w i = 1 - x := by grind
    specialize hzi i
    rw [this] at hzi
    grind
  obtain hzs := AffineSubspace.mem_map_of_mem (AffineMap.homothety (s.points i) x⁻¹) hzs
  obtain p := Classical.arbitrary (affineSpan k (Set.range (s.faceOpposite i).points))
  rw [AffineSubspace.map_map, ← AffineMap.homothety_mul, inv_mul_cancel₀ hx0,
    AffineMap.homothety_one, AffineSubspace.map_id,
    Finset.homothety_affineCombination _ _ _ (by simp),
    ← AffineSubspace.vsub_right_mem_direction_iff_mem p.prop,
    ← Finset.sum_smul_vsub_const_eq_affineCombination_vsub _ _ _ _ (by
      simp [AffineMap.lineMap_apply_module, Finset.sum_add_distrib, ← Finset.mul_sum, hw1]),
    ← Finset.sum_erase_add _ _ (show i ∈ Finset.univ by simp),
    Submodule.add_mem_iff_right _ (Submodule.sum_mem _ fun j hj ↦ by
      apply smul_mem
      refine AffineSubspace.vsub_mem_direction (mem_affineSpan _ ?_) p.prop
      suffices ∃ k, k ≠ i ∧ s.points k = s.points j by simpa
      exact ⟨j, by simpa using hj⟩), AffineMap.lineMap_apply_module, Pi.add_apply, Pi.smul_apply,
    Pi.smul_apply, Finset.affineCombinationSingleWeights_apply_self, smul_eq_mul, smul_eq_mul,
    mul_one, smul_mem_iff _ hxi, AffineSubspace.vsub_right_mem_direction_iff_mem p.prop] at hzs
  exact s.points_notMem_affineSpan_faceOpposite i hzs


namespace Affine.Simplex

variable {V P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [MetricSpace P] [MeasurableSpace P] [BorelSpace P] [NormedAddTorsor V P]

theorem measurableSet_closedInterior {n : ℕ} (s : Simplex ℝ P n) :
    MeasurableSet s.closedInterior := by
  apply (s.isClosed_closedInterior  (n := n)).measurableSet

/-- For public version, use `Affine.Simplex.euclideanHausdorffMeasure_closedInterior`. -/
private theorem euclideanHausdorffMeasure_closedInterior' [FiniteDimensional ℝ V]
    {n : ℕ} (hn : finrank ℝ V = n + 1) (s : Simplex ℝ P (n + 1)) (i : Fin (n + 2)) :
    μHE[n + 1] s.closedInterior = (ENNReal.ofReal (n + 1 : ℕ))⁻¹ * ENNReal.ofReal (s.height i) *
    μHE[n] (s.faceOpposite i).closedInterior := by
  borelize V
  have htop : vectorSpan ℝ (Set.range s.points) = ⊤ :=
    s.independent.vectorSpan_eq_top_of_card_eq_finrank_add_one (by simp [hn])
  have haltitudeFoot : s.altitudeFoot i -ᵥ s.points i ≠ 0 := by
    rw [← norm_eq_zero.ne, ← dist_eq_norm_vsub', ← height]
    exact (s.height_pos i).ne.symm
  have hrank_orth : finrank ℝ ↥(ℝ ∙ (s.altitudeFoot i -ᵥ s.points i))ᗮ = n :=
    have : Fact (finrank ℝ V = n + 1) := ⟨hn⟩
    finrank_orthogonal_span_singleton haltitudeFoot
  have hinter (x : ℝ) : AffineSubspace.mk' (x • (s.altitudeFoot i -ᵥ s.points i) +ᵥ s.points i)
      (ℝ ∙ (s.altitudeFoot i -ᵥ s.points i))ᗮ =
      (affineSpan ℝ (Set.range (s.faceOpposite i).points)).shift (s.points i) x := by
    convert AffineSubspace.mk'_eq ?_
    · rw [AffineSubspace.direction_shift]
      trans (affineSpan ℝ (Set.range (s.faceOpposite i).points)).direction
        ⊔ (vectorSpan ℝ (Set.range s.points))ᗮ
      · rw [← orthogonalComplement_eq_orthogonalComplement, ← inf_orthogonal,
          orthogonal_orthogonal, orthogonal_orthogonal,
          range_faceOpposite_points, direction_affineSpan, ← direction_altitude,
          ← affineSpan_pair_altitudeFoot_eq_altitude, direction_affineSpan, vectorSpan_pair]
      · simp [htop]
    rw [AffineSubspace.shift_eq _ ⟨s.altitudeFoot i, altitudeFoot_mem_affineSpan_faceOpposite s i⟩]
    suffices ∃ y ∈ (affineSpan ℝ (Set.range (s.faceOpposite i).points)),
        (1 - x) • (s.points i -ᵥ s.altitudeFoot i) +ᵥ y =
        x • (s.altitudeFoot i -ᵥ s.points i) +ᵥ s.points i by
      simpa
    simp only [vadd_eq_iff_eq_neg_vadd, ↓existsAndEq, and_true]
    rw [← smul_neg, neg_vsub_eq_vsub_rev, vadd_vadd, ← add_smul, sub_add_cancel, one_smul,
      vsub_vadd]
    exact altitudeFoot_mem_affineSpan_faceOpposite s i
  conv in μHE[n + 1] => rw [← hn]
  rw [EuclideanGeometry.euclideanHausdorffMeasure_eq_lintegral (s.points i) haltitudeFoot
    s.measurableSet_closedInterior, enorm_eq_nnnorm, ← norm_toNNReal, ← dist_eq_norm_vsub',
    ← Simplex.height, hrank_orth]
  simp_rw [hinter]
  have hcongr : (fun x ↦ μHE[n] (s.closedInterior ∩
        (affineSpan ℝ (Set.range (s.faceOpposite i).points)).shift (s.points i) x))
      =ᶠ[ae (MeasureSpace.volume.restrict (Set.Icc 0 1))]
      fun x ↦ ‖x‖₊ ^ n • μHE[n] (s.faceOpposite i).closedInterior := by
    rw [← restrict_Ioc_eq_restrict_Icc]
    refine ae_restrict_of_forall_mem (by simp) fun x hx ↦ ?_
    simp only
    rw [s.closedInterior_inter_shift i (Set.mem_of_mem_of_subset hx (by grind))]
    rw [euclideanHausdorffMeasure_homothety_image _ _ hx.1.ne.symm]
  have hsupport : Function.support (fun x ↦ μHE[n] (s.closedInterior ∩
      (affineSpan ℝ (Set.range (s.faceOpposite i).points)).shift (s.points i) x)) ⊆
      Set.Icc 0 1 := by
    intro x
    contrapose
    intro hx
    rw [Function.mem_support, not_not, s.closedInterior_inter_mapHomothety_eq_empty i hx,
      measure_empty]
  rw [← setLIntegral_eq_of_support_subset hsupport, lintegral_congr_ae hcongr]
  simp_rw [nnreal_smul_coe_apply]
  rw [lintegral_mul_const _ (by fun_prop), ← mul_assoc]
  congrm ?_ * _
  suffices ∫⁻ (x : ℝ) in Set.Icc 0 1, ↑(‖x‖₊ ^ n) = (ENNReal.ofReal ↑(n + 1))⁻¹ by
    rw [this, mul_comm]
    norm_cast
  suffices (∫⁻ (x : ℝ) in Set.Icc 0 1, ↑(‖x‖₊ ^ n)).toReal = (ENNReal.ofReal ↑(n + 1))⁻¹.toReal by
    rw [ENNReal.toReal_eq_toReal_iff] at this
    apply this.resolve_right
    push_neg +distrib
    exact ⟨Or.inr (by simp; grind), Or.inr (by simp)⟩
  calc
  (∫⁻ (x : ℝ) in Set.Icc 0 1, ↑(‖x‖₊ ^ n)).toReal = ∫ (x : ℝ) in Set.Icc 0 1, ‖x‖ ^ n := by
    rw [integral_eq_lintegral_of_nonneg_ae (.of_forall (fun x ↦ by positivity)) (by fun_prop)]
    rw [setLIntegral_congr_fun (by simp) ?_]
    intro x hx
    simp only
    push_cast
    rw [ENNReal.ofReal_pow (by simp)]
    congrm ($norm_toNNReal.symm) ^ _
  _ = ∫ x in Set.Icc 0 1, x ^ n := by
    apply setIntegral_congr_fun (by simp)
    intro x hx
    simpa [Real.norm_eq_abs, ← abs_pow] using abs_of_nonneg <| pow_nonneg hx.1 n
  _ = ∫ x in 0..1, x ^ n := by
    simp [intervalIntegral.intervalIntegral_eq_integral_uIoc, integral_Icc_eq_integral_Ioc]
  _ = _ := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal (by positivity)]
    simp

set_option backward.isDefEq.respectTransparency false in
theorem euclideanHausdorffMeasure_closedInterior
    {n : ℕ} (s : Simplex ℝ P (n + 1)) (i : Fin (n + 2)) :
    μHE[n + 1] s.closedInterior = (.ofReal (n + 1 : ℕ))⁻¹ * .ofReal (s.height i) *
    μHE[n] (s.faceOpposite i).closedInterior := by
  have hn : finrank ℝ ↥(affineSpan ℝ (Set.range s.points)).direction = n + 1 := by
    rw [← add_left_inj 1, direction_affineSpan, s.independent.finrank_vectorSpan_add_one]
    simp
  convert ← (s.restrict _ le_rfl).euclideanHausdorffMeasure_closedInterior' hn i using 0
  congrm (?_ = _ * ENNReal.ofReal ?_ * ?_)
  · rw [closedInterior_restrict, Isometry.euclideanHausdorffMeasure_preimage
      (by exact (AffineSubspace.subtypeₐᵢ _).isometry)]
    congr
    rw [Set.inter_eq_left]
    simpa using closedInterior_subset_affineSpan
  · exact (s.height_restrict _ le_rfl i)
  · rw [faceOpposite_restrict, closedInterior_restrict, Isometry.euclideanHausdorffMeasure_preimage
      (by exact (AffineSubspace.subtypeₐᵢ _).isometry)]
    congrm μHE[n] ?_
    rw [Set.inter_eq_left]
    apply closedInterior_subset_affineSpan.trans
    suffices affineSpan ℝ (s.points '' {i}ᶜ) ≤ affineSpan ℝ (Set.range s.points) by simpa
    exact affineSpan_mono _ (by simp)

theorem euclideanHausdorffMeasure_real_closedInterior
    {n : ℕ} (s : Simplex ℝ P (n + 1)) (i : Fin (n + 2)) :
    μHE[n + 1].real s.closedInterior =
    (↑(n + 1))⁻¹ * s.height i * μHE[n].real (s.faceOpposite i).closedInterior := by
  simp_rw [measureReal_def]
  rw [s.euclideanHausdorffMeasure_closedInterior i, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (s.height_pos i).le,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (by positivity)]

theorem euclideanHausdorffMeasure_closedInterior_eq_one (s : Simplex ℝ P 0) :
    μHE[0] s.closedInterior = 1 := by
  simp

theorem euclideanHausdorffMeasure_closedInterior_real_eq_one (s : Simplex ℝ P 0) :
    μHE[0].real s.closedInterior = 1 := by
  simp [MeasureTheory.Measure.real_def]

theorem euclideanHausdorffMeasure_closedInterior_ne_top {n : ℕ} (s : Simplex ℝ P n) :
    μHE[n] s.closedInterior ≠ ⊤ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [s.euclideanHausdorffMeasure_closedInterior 0]
    exact ENNReal.mul_ne_top (by finiteness) (ih _)

theorem euclideanHausdorffMeasure_interior {n : ℕ} (hn : n ≠ 0) (s : Simplex ℝ P n) :
    μHE[n] s.interior = μHE[n] s.closedInterior := by
  apply le_antisymm
  · gcongr
    exact s.interior_subset_closedInterior
  have : NeZero n := ⟨hn⟩
  grw [closedInterior_eq_interior_union, measure_union_le, measure_iUnion_le, tsum_fintype]
  suffices ∑ b, μHE[n] (s.faceOpposite b).closedInterior = 0 by simp [this]
  refine Finset.sum_eq_zero (fun i _ ↦ ?_)
  apply (euclideanHausdorffMeasure_zero_or_top (Nat.sub_one_lt hn) _).resolve_right
  apply euclideanHausdorffMeasure_closedInterior_ne_top

theorem euclideanHausdorffMeasure_interior_eq_zero (s : Simplex ℝ P 0) (d : ℕ) :
    μHE[d] s.interior = 0 := by
  simp

set_option backward.isDefEq.respectTransparency false in
theorem volume_eq_euclideanHausdorffMeasure_real_closedInterior
    {n : ℕ} (s : Simplex ℝ P n) :
    s.volume = μHE[n].real s.closedInterior := by
  induction n with
  | zero => rw [euclideanHausdorffMeasure_closedInterior_real_eq_one, volume]
  | succ n ih => rw [volume, s.euclideanHausdorffMeasure_real_closedInterior 0, ih]

theorem volume_eq_volume_real_closedInterior [MeasurableSpace V] [BorelSpace V]
    [FiniteDimensional ℝ V] {n : ℕ} (hn : finrank ℝ V = n) (s : Simplex ℝ V n) :
    s.volume = MeasureTheory.MeasureSpace.volume.real s.closedInterior := by
  rw [volume_eq_euclideanHausdorffMeasure_real_closedInterior]
  simp_rw [← hn]
  rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume]

end Affine.Simplex
