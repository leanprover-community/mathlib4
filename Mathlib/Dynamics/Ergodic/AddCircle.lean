/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Dynamics.FixedPoints.Prufer
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Covering.DensityTheorem
public import Mathlib.MeasureTheory.Group.AddCircle
public import Mathlib.MeasureTheory.Measure.Haar.Unique

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
set_option backward.defeqAttrib.useBackward true

public section


open Set Function MeasureTheory MeasureTheory.Measure Filter Metric

open scoped MeasureTheory NNReal ENNReal Topology Pointwise

namespace AddCircle

variable {T : ℝ} [hT : Fact (0 < T)]

/-- If a null-measurable subset of the circle is almost invariant under rotation by a family of
rational angles with denominators tending to infinity, then it must be almost empty or almost full.
-/
theorem ae_empty_or_univ_of_forall_vadd_ae_eq_self {s : Set <| AddCircle T}
    (hs : NullMeasurableSet s volume) {ι : Type*} {l : Filter ι} [l.NeBot] {u : ι → AddCircle T}
    (hu₁ : ∀ i, (u i +ᵥ s : Set _) =ᵐ[volume] s) (hu₂ : Tendsto (addOrderOf ∘ u) l atTop) :
    s =ᵐ[volume] (∅ : Set <| AddCircle T) ∨ s =ᵐ[volume] univ := by
  /- Sketch of proof:
    Assume `T = 1` for simplicity and let `μ` be the Haar measure. We may assume `s` has positive
    measure since otherwise there is nothing to prove. In this case, by Lebesgue's density theorem,
    there exists a point `d` of positive density. Let `Iⱼ` be the sequence of closed balls about `d`
    of diameter `1 / nⱼ` where `nⱼ` is the additive order of `uⱼ`. Since `d` has positive density we
    must have `μ (s ∩ Iⱼ) / μ Iⱼ → 1` along `l`. However since `s` is invariant under the action of
    `uⱼ` and since `Iⱼ` is a fundamental domain for this action, we must have
    `μ (s ∩ Iⱼ) = nⱼ * μ s = (μ Iⱼ) * μ s`. We thus have `μ s → 1` and thus `μ s = 1`. -/
  set μ := (volume : Measure <| AddCircle T)
  set n : ι → ℕ := addOrderOf ∘ u
  have hT₀ : 0 < T := hT.out
  have hT₁ : ENNReal.ofReal T ≠ 0 := by simpa
  rw [ae_eq_empty, ae_eq_univ_iff_measure_eq hs, AddCircle.measure_univ]
  rcases eq_or_ne (μ s) 0 with h | h; · exact Or.inl h
  right
  obtain ⟨d, -, hd⟩ : ∃ d, d ∈ s ∧ ∀ {ι'} {l : Filter ι'} (w : ι' → AddCircle T) (δ : ι' → ℝ),
    Tendsto δ l (𝓝[>] 0) → (∀ᶠ j in l, d ∈ closedBall (w j) (1 * δ j)) →
      Tendsto (fun j => μ (s ∩ closedBall (w j) (δ j)) / μ (closedBall (w j) (δ j))) l (𝓝 1) :=
    exists_mem_of_measure_ne_zero_of_ae h
      (IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div μ s 1)
  let I : ι → Set (AddCircle T) := fun j => closedBall d (T / (2 * ↑(n j)))
  replace hd : Tendsto (fun j => μ (s ∩ I j) / μ (I j)) l (𝓝 1) := by
    let δ : ι → ℝ := fun j => T / (2 * ↑(n j))
    have hδ₀ : ∀ᶠ j in l, 0 < δ j :=
      (hu₂.eventually_gt_atTop 0).mono fun j hj => div_pos hT₀ <| by positivity
    have hδ₁ : Tendsto δ l (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, hδ₀⟩
      replace hu₂ : Tendsto (fun j => T⁻¹ * 2 * n j) l atTop :=
        (tendsto_natCast_atTop_iff.mpr hu₂).const_mul_atTop (by positivity : 0 < T⁻¹ * 2)
      convert hu₂.inv_tendsto_atTop
      ext j
      simp only [δ, Pi.inv_apply, mul_inv_rev, inv_inv, div_eq_inv_mul, ← mul_assoc]
    have hw : ∀ᶠ j in l, d ∈ closedBall d (1 * δ j) := hδ₀.mono fun j hj => by
      simp only [one_mul, mem_closedBall, dist_self]
      apply hj.le
    exact hd _ δ hδ₁ hw
  suffices ∀ᶠ j in l, μ (s ∩ I j) / μ (I j) = μ s / ENNReal.ofReal T by
    replace hd := hd.congr' this
    rwa [tendsto_const_nhds_iff, ENNReal.div_eq_one_iff hT₁ ENNReal.ofReal_ne_top] at hd
  refine (hu₂.eventually_gt_atTop 0).mono fun j hj => ?_
  have : addOrderOf (u j) = n j := rfl
  have huj : IsOfFinAddOrder (u j) := addOrderOf_pos_iff.mp hj
  have huj' : 1 ≤ (↑(n j) : ℝ) := by norm_cast
  have hI₀ : μ (I j) ≠ 0 := (measure_closedBall_pos _ d <| by positivity).ne.symm
  have hI₁ : μ (I j) ≠ ⊤ := measure_ne_top _ _
  have hI₂ : μ (I j) * ↑(n j) = ENNReal.ofReal T := by
    rw [volume_closedBall, mul_div, mul_div_mul_left T _ two_ne_zero,
      min_eq_right (div_le_self hT₀.le huj'), mul_comm, ← nsmul_eq_mul, ← ENNReal.ofReal_nsmul,
      nsmul_eq_mul, mul_div_cancel₀]
    exact Nat.cast_ne_zero.mpr hj.ne'
  rw [ENNReal.div_eq_div_iff hT₁ ENNReal.ofReal_ne_top hI₀ hI₁,
    volume_of_add_preimage_eq s _ (u j) d huj (hu₁ j) closedBall_ae_eq_ball, nsmul_eq_mul, ←
    mul_assoc, this, hI₂]

theorem ergodic_zsmul {n : ℤ} (hn : 1 < |n|) : Ergodic fun y : AddCircle T => n • y :=
  { measurePreserving_zsmul volume (abs_pos.mp <| lt_trans zero_lt_one hn) with
    aeconst_set := fun s hs hs' => by
      let u : ℕ → AddCircle T := fun j => ↑((↑1 : ℝ) / ↑(n.natAbs ^ j) * T)
      replace hn : 1 < n.natAbs := by rwa [Int.abs_eq_natAbs, Nat.one_lt_cast] at hn
      have hu₀ : ∀ j, addOrderOf (u j) = n.natAbs ^ j := fun j => by
        convert addOrderOf_div_of_gcd_eq_one (p := T) (m := 1)
          (pow_pos (pos_of_gt hn) j) (gcd_one_left _)
        norm_cast
      have hnu : ∀ j, n ^ j • u j = 0 := fun j => by
        rw [← addOrderOf_dvd_iff_zsmul_eq_zero, hu₀, Int.natCast_pow, Int.natCast_natAbs, ← abs_pow,
          abs_dvd]
      have hu₁ : ∀ j, (u j +ᵥ s : Set _) =ᵐ[volume] s := fun j => by
        rw [vadd_eq_self_of_preimage_zsmul_eq_self hs' (hnu j)]
      have hu₂ : Tendsto (fun j => addOrderOf <| u j) atTop atTop := by
        simp_rw [hu₀]; exact tendsto_pow_atTop_atTop_of_one_lt hn
      rw [eventuallyConst_set']
      exact ae_empty_or_univ_of_forall_vadd_ae_eq_self hs.nullMeasurableSet hu₁ hu₂ }

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
    conv_rhs => congr; rw [← DivisibleBy.div_cancel x h]
    rw [sub_smul, one_smul, sub_add_cancel]
  ext y
  simp only [f, e, hnx, MeasurableEquiv.coe_addLeft, MeasurableEquiv.symm_addLeft, comp_apply,
    smul_add, zsmul_neg', neg_smul, neg_add_rev]
  abel

theorem ergodic_nsmul_add (x : AddCircle T) {n : ℕ} (h : 1 < n) : Ergodic fun y => n • y + x :=
  ergodic_zsmul_add x (by simp [h] : 1 < |(n : ℤ)|)

end AddCircle
