/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne
import Mathlib.NumberTheory.NumberField.ClassNumber

/-!
# Asymptotics on integral ideals of a number field

We prove several asymptotics involving integral ideals of a number field.

## Main results

* `NumberField.ideal.tendsto_norm_le_and_mk_eq_div_atTop`: asymptotics for the number of (nonzero)
  integral ideals of bounded norm in a fixed class of the class group.
* `NumberField.ideal.tendsto_norm_le_div_atTop`: asymptotics for the number of integral ideals
  of bounded norm.

-/

noncomputable section

open Ideal

variable (K : Type*) [Field K] [NumberField K]

namespace NumberField.Ideal

open scoped nonZeroDivisors Real

open Filter InfinitePlace mixedEmbedding euclidean fundamentalCone Submodule Topology Units

variable {C : ClassGroup (𝓞 K)} {J : (Ideal (𝓞 K))⁰} {s : ℝ}

private theorem tendsto_norm_le_and_mk_eq_div_atTop_aux₁ (hJ : ClassGroup.mk0 J = C⁻¹) :
    Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) ≤ s ∧ ClassGroup.mk0 I = C}
      = Nat.card {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ I ∧ IsPrincipal (I : Ideal (𝓞 K)) ∧
        absNorm (I : Ideal (𝓞 K)) ≤ s * absNorm (J : Ideal (𝓞 K))} := by
  simp_rw [← nonZeroDivisors_dvd_iff_dvd_coe]
  refine Nat.card_congr ?_
  refine ((Equiv.dvd J).subtypeEquiv fun I ↦ ?_).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter (fun I : (Ideal (𝓞 K))⁰ ↦ J ∣ I) _)
  rw [← ClassGroup.mk0_eq_one_iff (SetLike.coe_mem _)]
  simp_rw [Equiv.dvd_apply, Submonoid.coe_mul, ← Submonoid.mul_def, _root_.map_mul, hJ,
    inv_mul_eq_one, Nat.cast_mul, mul_comm s, eq_comm, and_comm, and_congr_left_iff]
  exact fun _ ↦
    (mul_le_mul_iff_of_pos_left (Nat.cast_pos.mpr (absNorm_pos_of_nonZeroDivisors J))).symm

open Classical in
private def tendsto_norm_le_and_mk_eq_div_atTop_aux₂ :
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

variable (C) in
/--
The limit of the number of nonzero integral ideals of norm `≤ s` in a fixed class `C` of the
class group divided by `s` when `s → +∞`.
-/
theorem tendsto_norm_le_and_mk_eq_div_atTop :
    Tendsto (fun s : ℝ ↦
      (Nat.card {I : (Ideal (𝓞 K))⁰ //
        absNorm (I : Ideal (𝓞 K)) ≤ s ∧ ClassGroup.mk0 I = C} : ℝ) / s) atTop
          (𝓝 ((2 ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * regulator K) /
            (torsionOrder K * Real.sqrt |discr K|))) := by
  classical
  have h₁ : ∀ s : ℝ,
    {x | x ∈ toMixed K ⁻¹' fundamentalCone K ∧ mixedEmbedding.norm (toMixed K x) ≤ s} =
      toMixed K ⁻¹' {x | x ∈ fundamentalCone K ∧ mixedEmbedding.norm x ≤ s} := fun _ ↦ rfl
  have h₂ : {x | x ∈ fundamentalCone K ∧ mixedEmbedding.norm x ≤ 1} = normLeOne K := by ext; simp
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective C⁻¹
  have h₃ : (absNorm J.1 : ℝ) ≠ 0 := (Nat.cast_ne_zero.mpr (absNorm_ne_zero_of_nonZeroDivisors J))
  convert ((ZLattice.covolume.tendsto_card_le_div'
    (ZLattice.comap ℝ (mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J))
      (toMixed K).toLinearMap)
    (F := fun x ↦ mixedEmbedding.norm (toMixed K x))
    (X := (toMixed K) ⁻¹' (fundamentalCone K)) (fun _ _ _ h ↦ ?_) (fun _ _ h ↦ ?_)
    (isBounded_normLeOne K) ?_ ?_).mul (tendsto_const_nhds
      (x := (absNorm (J : Ideal (𝓞 K)) : ℝ) * (torsionOrder K : ℝ)⁻¹))).comp
    (tendsto_id.atTop_mul_const' <| Nat.cast_pos.mpr (absNorm_pos_of_nonZeroDivisors J))
    using 2 with s
  · simp_rw [Ideal.tendsto_norm_le_and_mk_eq_div_atTop_aux₁ K hJ, id_eq,
      Nat.card_congr (Ideal.tendsto_norm_le_and_mk_eq_div_atTop_aux₂ K),
      ← card_isPrincipal_dvd_norm_le, Function.comp_def, Nat.cast_mul, div_eq_mul_inv, mul_inv,
      ← mul_assoc, mul_comm _ (torsionOrder K : ℝ)⁻¹, mul_comm _ (torsionOrder K : ℝ), mul_assoc]
    rw [inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr (torsionOrder_ne_zero K)), inv_mul_cancel₀ h₃,
      mul_one]
  · rw [h₁, h₂, MeasureTheory.measureReal_def, (volumePreserving_toMixed K).measure_preimage
      (measurableSet_normLeOne K).nullMeasurableSet, volume_normLeOne, ZLattice.covolume_comap
      _ _ _ (volumePreserving_toMixed K), covolume_idealLattice, ENNReal.toReal_mul,
      ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
      ENNReal.coe_toReal, NNReal.coe_real_pi, ENNReal.toReal_ofReal (regulator_pos K).le,
      FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast, div_eq_mul_inv,
      div_eq_mul_inv, mul_inv, mul_inv, mul_inv, inv_pow, inv_inv]
    ring_nf
    rw [mul_inv_cancel_right₀ h₃]
  · rwa [Set.mem_preimage, map_smul, smul_mem_iff_mem h.ne']
  · dsimp only
    rw [map_smul, mixedEmbedding.norm_smul, euclidean.finrank, abs_of_nonneg h]
  · exact (toMixed K).continuous.measurable (measurableSet_normLeOne K)
  · rw [h₁, ← (toMixed K).coe_toHomeomorph, ← Homeomorph.preimage_frontier,
      (toMixed K).coe_toHomeomorph, (volumePreserving_toMixed K).measure_preimage
      measurableSet_frontier.nullMeasurableSet, h₂, volume_frontier_normLeOne]

/--
The limit of the number of nonzero integral ideals of norm `≤ s` divided by `s` when `s → +∞`.
-/
theorem tendsto_norm_le_div_atTop₀ :
    Tendsto (fun s : ℝ ↦
      (Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) ≤ s} : ℝ) / s) atTop
          (𝓝 ((2 ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * regulator K * classNumber K) /
            (torsionOrder K * Real.sqrt |discr K|))) := by
  classical
  convert Filter.Tendsto.congr' ?_
    (tendsto_finset_sum Finset.univ (fun C _ ↦ tendsto_norm_le_and_mk_eq_div_atTop K C))
  · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, classNumber]
    ring
  · filter_upwards [eventually_ge_atTop 0] with s hs
    have : Fintype {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) ≤ s} := by
      simp_rw [← Nat.le_floor_iff hs]
      refine @Fintype.ofFinite _ (finite_setOf_absNorm_le₀ ⌊s⌋₊)
    let e := fun C : ClassGroup (𝓞 K) ↦ Equiv.subtypeSubtypeEquivSubtypeInter
      (fun I : (Ideal (𝓞 K))⁰ ↦ absNorm I.1 ≤ s) (fun I ↦ ClassGroup.mk0 I = C)
    simp_rw [← Nat.card_congr (e _), Nat.card_eq_fintype_card, Fintype.subtype_card]
    rw [Fintype.card, Finset.card_eq_sum_card_fiberwise (f := fun I ↦ ClassGroup.mk0 I.1)
      (t := Finset.univ) (fun _ _ ↦ Finset.mem_univ _), Nat.cast_sum, Finset.sum_div]

/--
The limit of the number of integral ideals of norm `≤ s` divided by `s` when `s → +∞`.
-/
theorem tendsto_norm_le_div_atTop :
    Tendsto (fun s : ℝ ↦ (Nat.card {I : Ideal (𝓞 K) // absNorm I ≤ s} : ℝ) / s) atTop
      (𝓝 ((2 ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * regulator K * classNumber K) /
        (torsionOrder K * Real.sqrt |discr K|))) := by
  have := (tendsto_norm_le_div_atTop₀ K).add tendsto_inv_atTop_zero
  rw [add_zero] at this
  apply this.congr'
  filter_upwards [eventually_ge_atTop 0] with s hs
  simp_rw [← Nat.le_floor_iff hs]
  rw [Ideal.card_norm_le_eq_card_norm_le_add_one, Nat.cast_add, Nat.cast_one, add_div, one_div]

end NumberField.Ideal
