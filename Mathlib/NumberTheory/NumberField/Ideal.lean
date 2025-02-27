/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne
import Mathlib.NumberTheory.NumberField.ClassNumber

/-!
# Docstring

-/

variable (K : Type*) [Field K] [NumberField K]

namespace NumberField

open Filter Ideal Submodule Topology NumberField NumberField.InfinitePlace
  NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.mixedEmbedding.euclidean NumberField.Units

open scoped nonZeroDivisors Real

open Classical in
private noncomputable def ideal.tendsto_mk_eq_norm_le_div_atop_aux₁ (J : (Ideal (𝓞 K))⁰) (s : ℝ) :
    ↑({x | x ∈ (toMixed K) ⁻¹' fundamentalCone K ∧ mixedEmbedding.norm ((toMixed K) x) ≤ s} ∩
      (ZLattice.comap ℝ (idealLattice K ((FractionalIdeal.mk0 K) J)) (toMixed K).toLinearMap))
        ≃ {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) ≤ s} := by
  rw [ZLattice.coe_comap]
  refine (((toMixed K).toEquiv.image _).trans (Equiv.setCongr ?_)).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter _ (mixedEmbedding.norm · ≤ s)).symm
  ext
  simp_rw [mem_idealSet, Set.mem_image, Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe,
    mem_idealLattice, FractionalIdeal.coe_mk0]
  constructor
  · rintro ⟨_, ⟨⟨hx₁, hx₂⟩, _, ⟨x, hx₃, rfl⟩, rfl⟩, rfl⟩
    exact ⟨⟨hx₁, x, hx₃, rfl⟩, hx₂⟩
  · rintro ⟨⟨hx₁, ⟨x, hx₂, rfl⟩⟩, hx₃⟩
    exact ⟨(toMixed K).symm (mixedEmbedding K x), ⟨⟨hx₁, hx₃⟩, ⟨(x : K), by simp [hx₂], rfl⟩⟩, rfl⟩

private theorem ideal.tendsto_mk_eq_norm_le_div_atop_aux₂ (C : ClassGroup (𝓞 K))
    (J : (Ideal (𝓞 K))⁰) (hJ : ClassGroup.mk0 J = C⁻¹) (s : ℝ) :
    Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) ≤ s ∧ ClassGroup.mk0 I = C}
      = Nat.card {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ I ∧ IsPrincipal (I : Ideal (𝓞 K)) ∧
        absNorm (I : Ideal (𝓞 K)) ≤ s * absNorm (J : Ideal (𝓞 K))} := by
  let e : (Ideal (𝓞 K))⁰ ≃ {I : (Ideal (𝓞 K))⁰ // J ∣ I} := by
    refine Equiv.ofBijective (fun I ↦ ⟨J * I, dvd_mul_right J I⟩) ⟨?_, ?_⟩
    · intro _ _ h
      simp_rw [Subtype.ext_iff, Submonoid.coe_mul, mul_eq_mul_left_iff] at h
      exact Subtype.ext_iff_val.mpr (h.resolve_right (nonZeroDivisors.coe_ne_zero J))
    · rintro ⟨_, ⟨I, hI⟩⟩
      exact ⟨I, Subtype.mk_eq_mk.mpr hI.symm⟩
  refine Nat.card_congr ?_
  let g := Equiv.subtypeSubtypeEquivSubtypeInter (fun I : (Ideal (𝓞 K))⁰ ↦ J ∣ I)
  simp_rw [← nonZeroDivisors_dvd_iff_dvd_coe]
  refine Equiv.trans ?_ (g _)
  refine Equiv.subtypeEquiv e ?_
  intro I
  simp_rw [← ClassGroup.mk0_eq_one_iff (SetLike.coe_mem (e I).1), e, Equiv.ofBijective_apply,
    Submonoid.coe_mul, ← Submonoid.mul_def, _root_.map_mul,  Nat.cast_mul, hJ, and_comm,
    ← inv_eq_iff_mul_eq_one, inv_inv, eq_comm, mul_comm s _, _root_.mul_le_mul_left
    (Nat.cast_pos.mpr (Nat.zero_lt_of_ne_zero (absNorm_ne_zero_of_nonZeroDivisors J)))]

theorem ideal.tendsto_mk_eq_norm_le_div_atop (C : ClassGroup (𝓞 K)) :
    Tendsto (fun s : ℝ ↦
      (Nat.card {I : (Ideal (𝓞 K))⁰ //
        absNorm (I : Ideal (𝓞 K)) ≤ s ∧ ClassGroup.mk0 I = C} : ℝ) / s) atTop
          (𝓝 ((2 ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * regulator K) /
            (torsionOrder K *  Real.sqrt |discr K|))) := by
  classical
  have h : ∀ s : ℝ,
    {x | x ∈ toMixed K ⁻¹' fundamentalCone K ∧ mixedEmbedding.norm (toMixed K x) ≤ s} =
      toMixed K ⁻¹' {x | x ∈ fundamentalCone K ∧ mixedEmbedding.norm x ≤ s} := fun _ ↦ rfl
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective C⁻¹
  convert ((ZLattice.covolume.tendsto_card_le_div'
      (ZLattice.comap ℝ (mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J))
        (toMixed K).toLinearMap)
      (F := fun x ↦ mixedEmbedding.norm (toMixed K x))
      (X := (toMixed K)⁻¹' (fundamentalCone K)) (fun _ _ _ h ↦ ?_) (fun _ _ h ↦ ?_)
      (isBounded_normLeOne K) ?_ ?_).mul (tendsto_const_nhds
        (x := (absNorm (J : Ideal (𝓞 K)) : ℝ) * (torsionOrder K : ℝ)⁻¹))).comp
      (tendsto_id.atTop_mul_const' <| Nat.cast_pos.mpr (absNorm_pos_of_nonZeroDivisors J))
    using 2 with s
  · simp_rw [ideal.tendsto_mk_eq_norm_le_div_atop_aux₂ K C J hJ, Function.comp_def, id_eq,
      Nat.card_congr (ideal.tendsto_mk_eq_norm_le_div_atop_aux₁ K J (s * (absNorm J.1))),
      ← card_isPrincipal_dvd_norm_le, Nat.cast_mul, div_eq_mul_inv, mul_inv, ← mul_assoc]
    rw [inv_mul_cancel_right₀ (Nat.cast_ne_zero.mpr (absNorm_ne_zero_of_nonZeroDivisors J)),
      mul_right_comm, mul_inv_cancel_right₀ (Nat.cast_ne_zero.mpr (torsionOrder K).ne_zero)]
  · simp_rw [h, (volumePreserving_toMixed K).measure_preimage
      (measurableSet_normLeOne K).nullMeasurableSet, volume_normLeOne,
      ZLattice.covolume_comap _ _ _ (volumePreserving_toMixed K), covolume_idealLattice,
      ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.coe_toReal,
      NNReal.coe_real_pi, ENNReal.toReal_ofReal (regulator_pos K).le, FractionalIdeal.coe_mk0,
      FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast, inv_pow, div_eq_mul_inv, mul_inv,
      inv_inv, mul_assoc, mul_comm (absNorm J.1 : ℝ), mul_comm (absNorm J.1 : ℝ)⁻¹, mul_assoc]
    rw [mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (absNorm_ne_zero_of_nonZeroDivisors J)), mul_one]
    ring
  · rwa [Set.mem_preimage, map_smul, smul_mem_iff_mem h.ne']
  · simp_rw [map_smul, mixedEmbedding.norm_smul, euclidean.finrank, abs_of_nonneg h]
  · exact (toMixed K).continuous.measurable (measurableSet_normLeOne K)
  · rw [h, ← ContinuousLinearEquiv.coe_toHomeomorph, ← Homeomorph.preimage_frontier,
      ContinuousLinearEquiv.coe_toHomeomorph, (volumePreserving_toMixed K).measure_preimage
      measurableSet_frontier.nullMeasurableSet, volume_frontier_normLeOne]

theorem ideal.tendsto_norm_le_div_atop₀ :
    Tendsto (fun s : ℝ ↦
      (Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) ≤ s} : ℝ) / s) atTop
          (𝓝 ((2 ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * regulator K * classNumber K) /
            (torsionOrder K *  Real.sqrt |discr K|))) := by
  classical
  convert Filter.Tendsto.congr' ?_
    (tendsto_finset_sum Finset.univ (fun C _  ↦ ideal.tendsto_mk_eq_norm_le_div_atop K C))
  · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, classNumber]
    ring
  · filter_upwards [eventually_ge_atTop 0] with s hs
    have : Fintype {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) ≤ s} := by
      simp_rw [← Nat.le_floor_iff hs]
      refine @Fintype.ofFinite _ ?_
      refine (finite_setOf_absNorm_le (S := 𝓞 K) ⌊s⌋₊).of_injective (fun ⟨I, h⟩ ↦ ⟨I.1, h⟩) ?_
      intro _ _ h
      rwa [Subtype.mk.injEq, SetLike.coe_eq_coe, SetCoe.ext_iff] at h
    let e := fun C : ClassGroup (𝓞 K) ↦ Equiv.subtypeSubtypeEquivSubtypeInter
      (fun I : (Ideal (𝓞 K))⁰ ↦ absNorm I.1 ≤ s) (fun I ↦ ClassGroup.mk0 I = C)
    simp_rw [← Nat.card_congr (e _), Nat.card_eq_fintype_card, Fintype.subtype_card]
    rw [Fintype.card, Finset.card_eq_sum_card_fiberwise (f := fun I ↦ ClassGroup.mk0 I.1)
      (t := Finset.univ) (fun _ _ ↦ Finset.mem_univ _), Nat.cast_sum, Finset.sum_div]

theorem ideal.tendsto_norm_le_div_atop :
    Tendsto (fun s : ℝ ↦ (Nat.card {I : Ideal (𝓞 K) // absNorm I ≤ s} : ℝ) / s) atTop
          (𝓝 ((2 ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * regulator K * classNumber K) /
            (torsionOrder K *  Real.sqrt |discr K|))) := by
  have := (ideal.tendsto_norm_le_div_atop₀ K).add tendsto_inv_atTop_zero
  rw [add_zero] at this
  refine Tendsto.congr' ?_ this
  filter_upwards [eventually_ge_atTop 0] with s hs
  simp_rw [← Nat.le_floor_iff hs]
  rw [Ideal.card_norm_le_eq_card_norm_le_add_one, Nat.cast_add, Nat.cast_one, add_div, one_div]

end NumberField
