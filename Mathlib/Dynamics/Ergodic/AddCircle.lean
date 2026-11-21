/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Group.AddCircle

import Mathlib.Dynamics.FixedPoints.Prufer
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Ergodic maps of the additive circle

This file contains proofs of ergodicity for maps of the additive circle.

## Main definitions:

* `AddCircle.ergodic_zsmul`: given `n : ℤ` such that `1 < |n|`, the self map `y ↦ n • y` on
  the additive circle is ergodic (w.r.t. the Haar measure).
* `AddCircle.ergodic_nsmul`: given `n : ℕ` such that `1 < n`, the self map `y ↦ n • y` on
  the additive circle is ergodic (w.r.t. the Haar measure).
* `AddCircle.ergodic_zsmul_add`: given `n : ℤ` such that `1 < |n|` and `x : AddCircle T`, the
  self map `y ↦ n • y + x` on the additive circle is ergodic (w.r.t. the Haar measure).
* `AddCircle.ergodic_nsmul_add`: given `n : ℕ` such that `1 < n` and `x : AddCircle T`, the
  self map `y ↦ n • y + x` on the additive circle is ergodic (w.r.t. the Haar measure).
-/

public section


open Set Function MeasureTheory MeasureTheory.Measure Filter Metric

open scoped MeasureTheory NNReal ENNReal Topology Pointwise symmDiff

namespace AddCircle

variable {T : ℝ} [hT : Fact (0 < T)]

theorem ae_empty_or_univ_of_tendsto_addOrderOf_sq_volume_symmDiff_zero {s : Set <| AddCircle T}
    (hs : NullMeasurableSet s volume) {ι : Type*} {l : Filter ι} [l.NeBot] {u : ι → AddCircle T}
    (hu₁ : Tendsto (fun i ↦ addOrderOf (u i) ^ 2 • volume ((u i +ᵥ s) ∆ s)) l (𝓝 0))
    (hu₂ : Tendsto (addOrderOf ∘ u) l atTop) :
    s =ᵐ[volume] (∅ : Set <| AddCircle T) ∨ s =ᵐ[volume] univ := by
  /- Sketch of proof:
    Assume `T = 1` for simplicity and let `μ` be the Haar measure. We may assume `s` has positive
    measure since otherwise there is nothing to prove. In this case, by Lebesgue's density theorem,
    there exists a point `d` of positive density. Let `Iⱼ` be the sequence of closed balls about `d`
    of diameter `1 / nⱼ` where `nⱼ` is the additive order of `uⱼ`. Since `d` has positive density we
    must have `μ (s ∩ Iⱼ) / μ Iⱼ → 1` along `l`. Let `εⱼ = μ ((uⱼ +ᵥ s) ∆ s)`. By the triangle
    inequality, `μ ((k • uⱼ +ᵥ s) ∆ s) ≤ k * εⱼ`. Since `Iⱼ` is a fundamental domain for the action
    of `uⱼ`, summing over its `nⱼ` translates we obtain `nⱼ * μ (s ∩ Iⱼ) ≤ μ s + nⱼ ^ 2 * εⱼ` and
    thus, since `nⱼ * μ Iⱼ = 1`, `μ (s ∩ Iⱼ) / μ Iⱼ ≤ μ s + nⱼ ^ 2 * εⱼ`. The left side tends to `1`
    and the right side tends to `μ s` so `1 ≤ μ s` and thus `μ s = 1`. -/
  set μ := (volume : Measure <| AddCircle T)
  set n : ι → ℕ := addOrderOf ∘ u
  have hT₀ : 0 < T := hT.out
  have hT₁ : ENNReal.ofReal T ≠ 0 := by simpa
  rw [ae_eq_empty, ae_eq_univ_iff_measure_eq hs, AddCircle.measure_univ]
  refine (eq_or_ne (μ s) 0).imp_right fun h ↦ ?_
  obtain ⟨d, -, hd⟩ := exists_mem_of_measure_ne_zero_of_ae h
    (IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div μ s 1)
  let I : ι → Set (AddCircle T) := fun j => closedBall d (T / (2 * ↑(n j)))
  replace hd : Tendsto (fun j => μ (s ∩ I j) / μ (I j)) l (𝓝 1) := by
    let δ : ι → ℝ := fun j => T / (2 * ↑(n j))
    have hδ₀ : ∀ᶠ j in l, 0 < δ j := (hu₂.eventually_gt_atTop 0).mono fun j hj => by positivity
    refine hd _ δ (tendsto_nhdsWithin_iff.mpr ⟨?_, hδ₀⟩)
      (.of_forall fun j ↦ mem_closedBall_self (by positivity))
    exact tendsto_const_nhds.div_atTop ((tendsto_natCast_atTop_iff.mpr hu₂).const_mul_atTop two_pos)
  set ε : ι → ℝ≥0∞ := fun j ↦ μ ((u j +ᵥ s) ∆ s)
  have hε (j : ι) (k : ℕ) : μ ((k • u j +ᵥ s) ∆ s) ≤ k • ε j := by
    simpa only [vadd_iterate, preimage_vadd, smul_neg, neg_neg, symmDiff_comm s] using
      (measurePreserving_vadd (-u j) μ).measure_symmDiff_preimage_iterate_le hs k
  let T' := ENNReal.ofReal T
  suffices ∀ᶠ j in l, μ (s ∩ I j) / μ (I j) ≤ (μ s + n j ^ 2 • ε j) / T' by
    have hlim : Tendsto (fun j ↦ (μ s + n j ^ 2 • ε j) / T') l (𝓝 (μ s / T')) := by
      have := ENNReal.Tendsto.div_const (hu₁.const_add (μ s)) (Or.inr hT₁)
      rwa [add_zero] at this
    have h₁ := le_of_tendsto_of_tendsto hd hlim this
    rw [ENNReal.le_div_iff_mul_le (Or.inl hT₁) (Or.inl ENNReal.ofReal_ne_top), one_mul] at h₁
    exact le_antisymm (AddCircle.measure_univ (T := T) ▸ measure_mono (subset_univ s)) h₁
  refine (hu₂.eventually_gt_atTop 0).mono fun j hj => ?_
  have huj : IsOfFinAddOrder (u j) := addOrderOf_pos_iff.mp hj
  have hI : μ (I j) * ↑(n j) = T' := by
    rw [volume_closedBall, mul_div, mul_div_mul_left T _ two_ne_zero,
      min_eq_right (div_le_self hT₀.le (by norm_cast)), ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity), div_mul_cancel₀ _ (by positivity)]
  have hF := isAddFundamentalDomain_of_ae_ball (I j) (u j) d huj closedBall_ae_eq_ball
  have h₀ (k : ℕ) (hk : k ≤ n j) : μ (s ∩ I j) ≤ μ ((k • u j +ᵥ s) ∩ I j) + n j • ε j := by
    calc μ (s ∩ I j)
        ≤ μ ((k • u j +ᵥ s) ∩ I j) + μ ((s ∩ I j) ∆ ((k • u j +ᵥ s) ∩ I j)) :=
          tsub_le_iff_left.mp le_measure_symmDiff
      _ ≤ μ ((k • u j +ᵥ s) ∩ I j) + n j • ε j := by
          gcongr
          rw [← Set.inter_symmDiff_distrib_right, symmDiff_comm]
          exact (measure_mono inter_subset_left).trans <| (hε j k).trans <| by gcongr
  have h₁ : μ s = ∑ k ∈ Finset.range (n j), μ ((k • u j +ᵥ s) ∩ I j) := by
    rw [hF.measure_eq_tsum s, ← (finEquivZMultiples huj).tsum_eq, tsum_fintype, Finset.sum_range]
    congr
  have h₂ : n j • μ (s ∩ I j) ≤ μ s + n j ^ 2 • ε j := by
    calc n j • μ (s ∩ I j)
        = ∑ k ∈ Finset.range (n j), μ (s ∩ I j) := by simp
      _ ≤ ∑ k ∈ Finset.range (n j), (μ ((k • u j +ᵥ s) ∩ I j) + n j • ε j) :=
          Finset.sum_le_sum fun k hk ↦ h₀ k (Finset.mem_range.mp hk).le
      _ = μ s + n j ^ 2 • ε j := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, sq, mul_nsmul, h₁]
  calc μ (s ∩ I j) / μ (I j)
      = n j • μ (s ∩ I j) / T' := by
        rw [← hI, nsmul_eq_mul, mul_comm, ENNReal.mul_div_mul_right _ _ (by aesop) (by simp)]
      _ ≤ (μ s + n j ^ 2 • ε j) / T' := by gcongr

/-- If a null-measurable subset of the circle is almost invariant under rotation by a family of
rational angles with denominators tending to infinity, then it must be almost empty or almost full.
-/
theorem ae_empty_or_univ_of_forall_vadd_ae_eq_self {s : Set <| AddCircle T}
    (hs : NullMeasurableSet s volume) {ι : Type*} {l : Filter ι} [l.NeBot] {u : ι → AddCircle T}
    (hu₁ : ∀ i, u i +ᵥ s =ᵐ[volume] s) (hu₂ : Tendsto (addOrderOf ∘ u) l atTop) :
    s =ᵐ[volume] (∅ : Set <| AddCircle T) ∨ s =ᵐ[volume] univ :=
  ae_empty_or_univ_of_tendsto_addOrderOf_sq_volume_symmDiff_zero hs
    (by simp [measure_symmDiff_eq_zero_iff.mpr (hu₁ _)]) hu₂

theorem ergodic_zsmul {n : ℤ} (hn : 1 < |n|) : Ergodic fun y : AddCircle T => n • y :=
  Ergodic.of_preimage_eq (measurePreserving_zsmul volume (abs_pos.mp <| lt_trans zero_lt_one hn))
    fun s hs hs' => by
      let u : ℕ → AddCircle T := fun j => ↑((↑1 : ℝ) / ↑(n.natAbs ^ j) * T)
      replace hn : 1 < n.natAbs := by rwa [Int.abs_eq_natAbs, Nat.one_lt_cast] at hn
      have hu₀ : ∀ j, addOrderOf (u j) = n.natAbs ^ j := fun j => by
        convert
          addOrderOf_div_of_gcd_eq_one (p := T) (m := 1) (pow_pos (pos_of_gt hn) j) (gcd_one_left _)
        norm_cast
      have hnu : ∀ j, n ^ j • u j = 0 := fun j => by
        rw [← addOrderOf_dvd_iff_zsmul_eq_zero, hu₀, Int.natCast_pow, Int.natCast_natAbs, ← abs_pow,
          abs_dvd]
      have hu₁ : ∀ j, (u j +ᵥ s : Set _) =ᵐ[volume] s := fun j =>
        .of_eq <| vadd_eq_self_of_preimage_zsmul_eq_self hs' (hnu j)
      have hu₂ : Tendsto (fun j => addOrderOf <| u j) atTop atTop := by
        simp_rw [hu₀]; exact tendsto_pow_atTop_atTop_of_one_lt hn
      rw [eventuallyEmptyOrUniv_iff']
      exact ae_empty_or_univ_of_forall_vadd_ae_eq_self hs.nullMeasurableSet hu₁ hu₂

theorem ergodic_nsmul {n : ℕ} (hn : 1 < n) : Ergodic fun y : AddCircle T => n • y :=
  ergodic_zsmul (by simp [hn] : 1 < |(n : ℤ)|)

theorem ergodic_zsmul_add (x : AddCircle T) {n : ℤ} (h : 1 < |n|) : Ergodic fun y => n • y + x := by
  set f : AddCircle T → AddCircle T := fun y => n • y + x
  let e : AddCircle T ≃ᵐ AddCircle T := MeasurableEquiv.addLeft (DivisibleBy.div x <| n - 1)
  have he : MeasurePreserving e volume volume :=
    measurePreserving_add_left volume (DivisibleBy.div x <| n - 1)
  suffices e ∘ f ∘ e.symm = fun y => n • y by
    rw [← he.ergodic_conjugate_iff, this]; exact ergodic_zsmul h
  replace h : n - 1 ≠ 0 := by
    rw [← abs_one] at h; rw [sub_ne_zero]; exact ne_of_apply_ne _ (ne_of_gt h)
  have hnx : n • DivisibleBy.div x (n - 1) = x + DivisibleBy.div x (n - 1) := by
    conv_rhs => enter [1]; rw [← DivisibleBy.div_cancel x h]
    rw [sub_smul, one_smul, sub_add_cancel]
  ext y
  simp only [f, e, hnx, MeasurableEquiv.coe_addLeft, MeasurableEquiv.symm_addLeft, comp_apply,
    smul_add, zsmul_neg', neg_smul, neg_add_rev]
  abel

theorem ergodic_nsmul_add (x : AddCircle T) {n : ℕ} (h : 1 < n) : Ergodic fun y => n • y + x :=
  ergodic_zsmul_add x (by simp [h] : 1 < |(n : ℤ)|)

end AddCircle
