/-
Copyright (c) 2026 Benoît Jubin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benoît Jubin
-/
module

public import Mathlib.Algebra.Order.Group.Indicator
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.LinearAlgebra.AffineSpace.Slope
public import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Mean-value-type results with countable exceptional sets

In this file we prove that a real function which is continuous on a real interval and whose lower
right Dini derivative is nonnegative outside a countable set is monotone on that interval
(`monotoneOn_of_liminf_slope_right_nonneg`, with the whole-line version
`monotone_of_liminf_slope_right_nonneg`).

Compare with the results in `Mathlib/Analysis/Calculus/MeanValue.lean`, where the derivative
bound must hold at every point of the interior of the interval.
-/

public section

open Set Filter
open scoped Topology

/-- If a real function is continuous on a real interval and its lower right Dini derivative is
nonnegative on the interior of that interval outside a countable set, then it is monotone on that
interval.

The hypothesis `hf'` expresses that the lower right Dini derivative of `f` at `x`, that is,
the `liminf` of `slope f x y` as `y` tends to `x` from the right, is nonnegative.

This is Proposition 2 of [N. Bourbaki, *Functions of a Real Variable*][bourbaki2004], Ch. I, §2.2,
adapted to the `MonotoneOn` predicate, to general intervals, and to the lower right Dini
derivative instead of the right-derivative. -/
theorem monotoneOn_of_liminf_slope_right_nonneg {f : ℝ → ℝ} {D s : Set ℝ} (hD : OrdConnected D)
    (hs : s.Countable) (hf : ContinuousOn f D)
    (hf' : ∀ x ∈ interior D, x ∉ s → ∀ r > 0, ∀ᶠ y in 𝓝[>] x, -r < slope f x y) :
    MonotoneOn f D := by
  rw [monotoneOn_iff_forall_lt]
  intro a ha b hb hab
  have habD : Icc a b ⊆ D := hD.out ha hb
  apply le_of_forall_pos_le_add
  intro ε εpos
  have εpos2 : 0 < ε / 2 := half_pos εpos
  -- Choose positive weights `w` on `insert a s` of total sum at most `ε / 2`.
  let S : Type := {x : ℝ // x ∈ insert a s}
  have : Encodable S := (hs.insert a).toEncodable
  obtain ⟨w, wpos, sumw, hsumw, hsumw_le⟩ := posSumOfEncodable εpos2 S
  -- `W y` is the sum of the weights of the exceptional points strictly below `y`.
  let below := fun y : ℝ ↦ {u : S | u < y}
  have below_mono : Monotone below := fun _ _ hxy _ hu ↦ hu.trans_le hxy
  let W := fun y ↦ ∑' u : S, (below y).indicator w u
  have W_mono : Monotone W := fun x y hxy ↦
    Summable.tsum_le_tsum
      (indicator_le_indicator_of_subset (below_mono hxy) fun u ↦ (wpos u).le)
      (hsumw.summable.indicator (below x)) (hsumw.summable.indicator (below y))
  -- On `[a, b]`, the quantity `f y - f a` will be bounded below by the antitone `lowerBound`.
  let lowerBound := fun y ↦ -(ε / 2) * ((y - a) / (b - a)) - W y
  have affine_anti : Antitone fun x ↦ -(ε / 2) * ((x - a) / (b - a)) := by
    intro _ _ hxy
    dsimp only
    exact mul_le_mul_of_nonpos_left
      (div_le_div_of_nonneg_right (sub_le_sub_right hxy a) (sub_pos.mpr hab).le)
      (neg_nonpos_of_nonneg εpos2.le)
  have lb_anti : Antitone lowerBound := by
    intro _ _ hxy
    dsimp only [lowerBound]
    linarith [W_mono hxy, affine_anti hxy]
  -- `J` is the set of points of `[a, b]` up to which the lower bound holds.
  -- The continuous-induction principles of `Mathlib/Topology/Order/IntermediateValue.lean`
  -- do not apply here, since `lowerBound` is not continuous, so `J` cannot be proved closed
  -- a priori.
  let J := {x | x ∈ Icc a b ∧ ∀ y ∈ Icc a x, lowerBound y ≤ f y - f a}
  have haJ : a ∈ J := by
    refine ⟨⟨le_rfl, hab.le⟩, fun y hy ↦ ?_⟩
    obtain rfl : a = y := le_antisymm hy.1 hy.2
    have hW : 0 ≤ W a := tsum_nonneg fun u ↦ indicator_apply_nonneg fun _ ↦ (wpos u).le
    have hlba : lowerBound a = -W a := by simp [lowerBound]
    rw [hlba, sub_self]
    exact neg_nonpos_of_nonneg hW
  have hJ_downward : ∀ ⦃m x⦄, m ∈ J → x ∈ Icc a m → x ∈ J := fun _ _ hm hx ↦
    ⟨⟨hx.1, hx.2.trans hm.1.2⟩, fun y hy ↦ hm.2 y (Icc_subset_Icc_right hx.2 hy)⟩
  have hJ_nonempty : J.Nonempty := ⟨a, haJ⟩
  have hJ_bddAbove : BddAbove J := ⟨b, fun _ hx ↦ hx.1.2⟩
  let c : ℝ := sSup J
  have hac : a ≤ c := le_csSup hJ_bddAbove haJ
  have hcb : c ≤ b := csSup_le hJ_nonempty fun _ hx ↦ hx.1.2
  have hcD : c ∈ D := habD ⟨hac, hcb⟩
  have hcont : ContinuousWithinAt f D c := hf c hcD
  -- The point `c = sSup J` belongs to `J`, by continuity of `f` on the left of `c`.
  have hcJ : c ∈ J := by
    by_cases hca : c = a
    · exact hca ▸ haJ
    · have hac' : a < c := lt_of_le_of_ne hac (Ne.symm hca)
      have hIco : Ico a c ⊆ J := by
        intro _ hx
        obtain ⟨m, hmJ, hxm⟩ := exists_lt_of_lt_csSup hJ_nonempty hx.2
        exact hJ_downward hmJ ⟨hx.1, hxm.le⟩
      refine ⟨⟨hac, hcb⟩, ?_⟩
      intro y hy
      obtain hyc | hyc := lt_or_ge y c
      · exact (hIco ⟨hy.1, hyc⟩).2 y ⟨hy.1, le_rfl⟩
      · obtain rfl : y = c := le_antisymm hy.2 hyc
        have hleft : ∀ z ∈ Ico a c, lowerBound c ≤ f z - f a := by
          intro z hz
          calc
            lowerBound c ≤ lowerBound z := lb_anti hz.2.le
            _ ≤ f z - f a := (hIco hz).2 z ⟨hz.1, le_rfl⟩
        have hsub : ContinuousWithinAt (fun z ↦ f z - f a) (Ico a c) c :=
          ((hcont.mono ((Icc_subset_Icc_right hcb).trans habD)).sub
            continuousWithinAt_const).mono Ico_subset_Icc_self
        change f c - f a ∈ Ici (lowerBound c)
        have ht : Tendsto (fun z ↦ f z - f a) (𝓝[<] c) (𝓝 (f c - f a)) := by
          rw [← nhdsWithin_Ico_eq_nhdsLT hac']
          exact hsub.tendsto
        apply IsClosed.mem_of_tendsto isClosed_Ici ht
        filter_upwards [Ico_mem_nhdsLT hac'] with z hz
        exact hleft z hz
  -- Moreover `c = b`, since otherwise `J` would contain points greater than `c = sSup J`.
  have hc_eq_b : c = b := by
    by_contra hne
    have hcb' : c < b := lt_of_le_of_ne hcJ.1.2 hne
    obtain ⟨t, hct, htJ⟩ : ∃ t > c, t ∈ J := by
      -- It suffices to bound `f y - f a` for `y` slightly to the right of `c`.
      have key : ∀ δ > 0, δ ≤ b - c →
          (∀ y ∈ Ioc c (c + δ / 2), lowerBound y ≤ f y - f a) → ∃ t > c, t ∈ J := by
        intro δ δpos δle hbound
        refine ⟨c + δ / 2, by linarith, ⟨by linarith, by linarith⟩, fun y hy ↦ ?_⟩
        obtain hyc | hcy := le_or_gt y c
        · exact hcJ.2 y ⟨hy.1, hyc⟩
        · exact hbound y ⟨hcy, hy.2⟩
      have hfc : lowerBound c ≤ f c - f a := hcJ.2 c ⟨hac, le_rfl⟩
      by_cases hcs : c ∈ insert a s
      · let uc : S := ⟨c, hcs⟩
        have hwc : 0 < w uc := wpos uc
        obtain ⟨δ, δpos, hδ⟩ := Metric.continuousWithinAt_iff.mp hcont (w uc / 2) (half_pos hwc)
        have hmin : 0 < min δ (b - c) := lt_min δpos (sub_pos.mpr hcb')
        refine key (min δ (b - c)) hmin (min_le_right _ _) fun y hy ↦ ?_
        obtain ⟨hcy, hyδ⟩ := hy
        have hyD : y ∈ D := hD.out hcD hb
          ⟨hcy.le, by linarith [min_le_right δ (b - c)]⟩
        have hdist : dist y c < δ := by
          rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hcy.le)]
          linarith [min_le_left δ (b - c)]
        have hfy : -(w uc / 2) < f y - f c := (abs_lt.mp (hδ hyD hdist)).1
        have hWy : W c + w uc ≤ W y := by
          have hsingle : Summable fun u : S ↦ if u = uc then w uc else 0 :=
            (hasSum_ite_eq uc (w uc)).summable
          dsimp only [W]
          calc
            ∑' u : S, (below c).indicator w u + w uc
              = ∑' u : S, ((below c).indicator w u + if u = uc then w uc else 0) := by
              rw [Summable.tsum_add (hsumw.summable.indicator (below c)) hsingle,
                tsum_ite_eq uc fun _ ↦ w uc]
            _ ≤ ∑' u : S, (below y).indicator w u := by
              refine Summable.tsum_le_tsum (fun u ↦ ?_)
                ((hsumw.summable.indicator (below c)).add hsingle)
                (hsumw.summable.indicator (below y))
              obtain rfl | hu := eq_or_ne u uc
              · have h1 : uc ∉ below c := lt_irrefl c
                have h2 : uc ∈ below y := hcy
                simp [indicator_of_notMem h1, indicator_of_mem h2]
              · rw [if_neg hu, add_zero]
                exact indicator_le_indicator_apply_of_subset (below_mono hcy.le) (wpos u).le
        calc
          lowerBound y ≤ w uc / 2 + lowerBound y := le_add_of_nonneg_left (half_pos hwc).le
          _ = -(w uc / 2) - (ε / 2) * ((y - a) / (b - a)) - (W y - w uc) := by
            simp only [lowerBound]
            ring
          _ ≤ -(w uc / 2) - (ε / 2) * ((y - a) / (b - a)) - W c := by linarith [hWy]
          _ ≤ -(w uc / 2) - (ε / 2) * ((c - a) / (b - a)) - W c := by linarith [affine_anti hcy.le]
          _ = -(w uc / 2) + lowerBound c := by simp only [lowerBound]; ring
          _ ≤ (f y - f c) + (f c - f a) := add_le_add hfy.le hfc
          _ = f y - f a := by ring
      · rw [mem_insert_iff, not_or] at hcs
        have hac' : a < c := lt_of_le_of_ne hac (Ne.symm hcs.1)
        have hcint : c ∈ interior D := interior_mono habD (interior_Icc.symm.subset ⟨hac', hcb'⟩)
        obtain ⟨δ, δpos, hδ⟩ : ∃ δ > 0, ∀ ⦃y⦄, y ∈ Ioc c (c + δ) →
            -(ε / 2 / (b - a)) < slope f c y := by
          have hDini : {y : ℝ | -(ε / 2 / (b - a)) < slope f c y} ∈ 𝓝[>] c := by
            simpa only [Filter.Eventually] using
              hf' c hcint hcs.2 _ (div_pos εpos2 (sub_pos.mpr hab))
          rw [mem_nhdsGT_iff_exists_Ioc_subset] at hDini
          obtain ⟨u, hu, hIoc⟩ := hDini
          exact ⟨u - c, sub_pos.mpr hu,
            fun _ hy ↦ hIoc ⟨hy.1, hy.2.trans_eq (add_sub_cancel c u)⟩⟩
        have hmin : 0 < min δ (b - c) := lt_min δpos (sub_pos.mpr hcb')
        refine key (min δ (b - c)) hmin (min_le_right _ _) fun y hy ↦ ?_
        obtain ⟨hcy, hyδ⟩ := hy
        have hslope : -(ε / 2 / (b - a)) < slope f c y :=
          hδ ⟨hcy, by linarith [min_le_left δ (b - c)]⟩
        calc
          lowerBound y ≤ -(ε / 2 / (b - a)) * (y - c) + lowerBound c := by
            have hid : -(ε / 2) * ((y - a) / (b - a)) =
                -(ε / 2) * ((c - a) / (b - a)) + -(ε / 2 / (b - a)) * (y - c) := by
              field_simp [sub_ne_zero.mpr hab.ne']
              ring
            simp only [lowerBound, hid]
            linarith [W_mono hcy.le]
          _ ≤ slope f c y * (y - c) + (f c - f a) :=
            add_le_add (mul_le_mul_of_nonneg_right hslope.le (sub_nonneg.mpr hcy.le)) hfc
          _ = (f y - f c) + (f c - f a) := by
            rw [slope_def_field]
            field_simp [sub_ne_zero.mpr hcy.ne']
          _ = f y - f a := by ring
    exact not_lt_of_ge (le_csSup hJ_bddAbove htJ) hct
  -- Conclude by taking `y = b` in the bound defining `J`.
  have hbJ : b ∈ J := hc_eq_b ▸ hcJ
  have hfb : lowerBound b ≤ f b - f a := hbJ.2 b ⟨hab.le, le_rfl⟩
  have hlbb : lowerBound b = -(ε / 2) - W b := by
    simp [lowerBound, div_self (sub_ne_zero_of_ne hab.ne')]
  have hWb : W b ≤ sumw :=
    (Summable.tsum_le_tsum (fun u ↦ indicator_le_self' (fun v _ ↦ (wpos v).le) u)
      (hsumw.summable.indicator (below b)) hsumw.summable).trans_eq hsumw.tsum_eq
  rw [hlbb] at hfb
  linarith [hsumw_le, hWb]

/-- If a real function is continuous and its lower right Dini derivative is nonnegative on the real
line outside a countable set, then it is monotone.

See `monotoneOn_of_liminf_slope_right_nonneg` for a version on an interval. -/
theorem monotone_of_liminf_slope_right_nonneg {f : ℝ → ℝ} {s : Set ℝ} (hs : s.Countable)
    (hf : Continuous f) (hf' : ∀ x ∉ s, ∀ r > 0, ∀ᶠ y in 𝓝[>] x, -r < slope f x y) :
    Monotone f :=
  monotoneOn_univ.mp <| monotoneOn_of_liminf_slope_right_nonneg ordConnected_univ hs
    hf.continuousOn fun x _ hx ↦ hf' x hx
