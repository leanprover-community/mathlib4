/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.MeasureTheory.Integral.Periodic
import Mathlib.Data.ZMod.Quotient

#align_import measure_theory.group.add_circle from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Measure-theoretic results about the additive circle

The file is a place to collect measure-theoretic results about the additive circle.

## Main definitions:

 * `AddCircle.closedBall_ae_eq_ball`: open and closed balls in the additive circle are almost
   equal
 * `AddCircle.isAddFundamentalDomain_of_ae_ball`: a ball is a fundamental domain for rational
   angle rotation in the additive circle

-/


open Set Function Filter MeasureTheory MeasureTheory.Measure Metric

open scoped MeasureTheory Pointwise BigOperators Topology ENNReal

namespace AddCircle

variable {T : ℝ} [hT : Fact (0 < T)]

theorem closedBall_ae_eq_ball {x : AddCircle T} {ε : ℝ} : closedBall x ε =ᵐ[volume] ball x ε := by
  rcases le_or_lt ε 0 with hε | hε
  · rw [ball_eq_empty.mpr hε, ae_eq_empty, volume_closedBall,
      min_eq_right (by linarith [hT.out] : 2 * ε ≤ T), ENNReal.ofReal_eq_zero]
    exact mul_nonpos_of_nonneg_of_nonpos zero_le_two hε
  · suffices volume (closedBall x ε) ≤ volume (ball x ε) by
      exact (ae_eq_of_subset_of_measure_ge ball_subset_closedBall this measurableSet_ball
        (measure_ne_top _ _)).symm
    have : Tendsto (fun δ => volume (closedBall x δ)) (𝓝[<] ε) (𝓝 <| volume (closedBall x ε)) := by
      simp_rw [volume_closedBall]
      refine' ENNReal.tendsto_ofReal (Tendsto.min tendsto_const_nhds <| Tendsto.const_mul _ _)
      convert (@monotone_id ℝ _).tendsto_nhdsWithin_Iio ε
      simp
    refine' le_of_tendsto this (mem_nhdsWithin_Iio_iff_exists_Ioo_subset.mpr ⟨0, hε, fun r hr => _⟩)
    exact measure_mono (closedBall_subset_ball hr.2)
#align add_circle.closed_ball_ae_eq_ball AddCircle.closedBall_ae_eq_ball

/-- Let `G` be the subgroup of `AddCircle T` generated by a point `u` of finite order `n : ℕ`. Then
any set `I` that is almost equal to a ball of radius `T / 2n` is a fundamental domain for the action
of `G` on `AddCircle T` by left addition. -/
theorem isAddFundamentalDomain_of_ae_ball (I : Set <| AddCircle T) (u x : AddCircle T)
    (hu : IsOfFinAddOrder u) (hI : I =ᵐ[volume] ball x (T / (2 * addOrderOf u))) :
    IsAddFundamentalDomain (AddSubgroup.zmultiples u) I := by
  set G := AddSubgroup.zmultiples u
  set n := addOrderOf u
  set B := ball x (T / (2 * n))
  have hn : 1 ≤ (n : ℝ) := by norm_cast; linarith [hu.addOrderOf_pos]
  refine' IsAddFundamentalDomain.mk_of_measure_univ_le _ _ _ _
  · -- `NullMeasurableSet I volume`
    exact measurableSet_ball.nullMeasurableSet.congr hI.symm
  · -- `∀ (g : G), g ≠ 0 → AEDisjoint volume (g +ᵥ I) I`
    rintro ⟨g, hg⟩ hg'
    replace hg' : g ≠ 0; · simpa only [Ne.def, AddSubgroup.mk_eq_zero_iff] using hg'
    change AEDisjoint volume (g +ᵥ I) I
    refine' AEDisjoint.congr (Disjoint.aedisjoint _)
      ((quasiMeasurePreserving_add_left volume (-g)).vadd_ae_eq_of_ae_eq g hI) hI
    have hBg : g +ᵥ B = ball (g + x) (T / (2 * n)) := by
      rw [add_comm g x, ← singleton_add_ball _ x g, add_ball, thickening_singleton]
    rw [hBg]
    apply ball_disjoint_ball
    rw [dist_eq_norm, add_sub_cancel, div_mul_eq_div_div, ← add_div, ← add_div, add_self_div_two,
      div_le_iff' (by positivity : 0 < (n : ℝ)), ← nsmul_eq_mul]
    refine' (le_add_order_smul_norm_of_isOfFinAddOrder (hu.of_mem_zmultiples hg) hg').trans
      (nsmul_le_nsmul_left (norm_nonneg g) _)
    exact Nat.le_of_dvd (addOrderOf_pos_iff.mpr hu) (addOrderOf_dvd_of_mem_zmultiples hg)
  · -- `∀ (g : G), QuasiMeasurePreserving (VAdd.vadd g) volume volume`
    exact fun g => quasiMeasurePreserving_add_left (G := AddCircle T) volume g
  · -- `volume univ ≤ ∑' (g : G), volume (g +ᵥ I)`
    replace hI := hI.trans closedBall_ae_eq_ball.symm
    haveI : Fintype G := @Fintype.ofFinite _ hu.finite_zmultiples.to_subtype
    have hG_card : (Finset.univ : Finset G).card = n := by
      show _ = addOrderOf u
      rw [← Nat.card_zmultiples, Nat.card_eq_fintype_card]; rfl
    simp_rw [measure_vadd]
    rw [AddCircle.measure_univ, tsum_fintype, Finset.sum_const, measure_congr hI,
      volume_closedBall, ← ENNReal.ofReal_nsmul, mul_div, mul_div_mul_comm,
      div_self, one_mul, min_eq_right (div_le_self hT.out.le hn), hG_card,
      nsmul_eq_mul, mul_div_cancel' T (lt_of_lt_of_le zero_lt_one hn).ne.symm]
    exact two_ne_zero
#align add_circle.is_add_fundamental_domain_of_ae_ball AddCircle.isAddFundamentalDomain_of_ae_ball

theorem volume_of_add_preimage_eq (s I : Set <| AddCircle T) (u x : AddCircle T)
    (hu : IsOfFinAddOrder u) (hs : (u +ᵥ s : Set <| AddCircle T) =ᵐ[volume] s)
    (hI : I =ᵐ[volume] ball x (T / (2 * addOrderOf u))) :
    volume s = addOrderOf u • volume (s ∩ I) := by
  let G := AddSubgroup.zmultiples u
  haveI : Fintype G := @Fintype.ofFinite _ hu.finite_zmultiples.to_subtype
  have hsG : ∀ g : G, (g +ᵥ s : Set <| AddCircle T) =ᵐ[volume] s := by
    rintro ⟨y, hy⟩; exact (vadd_ae_eq_self_of_mem_zmultiples hs hy : _)
  rw [(isAddFundamentalDomain_of_ae_ball I u x hu hI).measure_eq_card_smul_of_vadd_ae_eq_self s hsG,
    ← Nat.card_zmultiples u, Nat.card_eq_fintype_card]
#align add_circle.volume_of_add_preimage_eq AddCircle.volume_of_add_preimage_eq

end AddCircle
