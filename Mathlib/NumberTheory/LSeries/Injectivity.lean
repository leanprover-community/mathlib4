/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.LSeries.Linearity

/-!
# A converging L-series determines its coefficients

We show that two functions `f` and `g : ℕ → ℂ` whose L-series agree and both converge somewhere
must agree on all nonzero arguments. See `LSeries_eq_iff_of_abscissaOfAbsConv_lt_top`
and `LSeries_injOn`.
-/

open LSeries Complex

-- The following two lemmas need both `LSeries.Linearity` and `LSeries.Convergence`,
-- so cannot live in either of these files.

/-- The abscissa of absolute convergence of `f + g` is at most the maximum of those
of `f` and `g`. -/
lemma LSeries.abscissaOfAbsConv_add_le (f g : ℕ → ℂ) :
    abscissaOfAbsConv (f + g) ≤ max (abscissaOfAbsConv f) (abscissaOfAbsConv g) :=
  abscissaOfAbsConv_binop_le LSeriesSummable.add f g

/-- The abscissa of absolute convergence of `f - g` is at most the maximum of those
of `f` and `g`. -/
lemma LSeries.abscissaOfAbsConv_sub_le (f g : ℕ → ℂ) :
    abscissaOfAbsConv (f - g) ≤ max (abscissaOfAbsConv f) (abscissaOfAbsConv g) :=
  abscissaOfAbsConv_binop_le LSeriesSummable.sub f g

private
lemma cpow_mul_div_cpow_eq_div_div_cpow (m n : ℕ) (z : ℂ) (x : ℝ) :
    (n + 1) ^ (x : ℂ) * (z / m ^ (x : ℂ)) = z / (m / (n + 1)) ^ (x : ℂ) := by
  have Hn : (0 : ℝ) ≤ (n + 1 : ℝ)⁻¹ := by positivity
  rw [← mul_div_assoc, mul_comm, div_eq_mul_inv z, mul_div_assoc]
  congr
  simp_rw [div_eq_mul_inv]
  rw [show (n + 1 : ℂ)⁻¹ = (n + 1 : ℝ)⁻¹ by simp,
    show (n + 1 : ℂ) = (n + 1 : ℝ) by norm_cast, show (m : ℂ) = (m : ℝ) by norm_cast,
    mul_cpow_ofReal_nonneg m.cast_nonneg Hn, mul_inv, mul_comm]
  congr
  rw [← cpow_neg, show (-x : ℂ) = (-1 : ℝ) * x by simp, cpow_mul_ofReal_nonneg Hn,
    Real.rpow_neg_one, inv_inv]

open Filter Real in
/-- If the coefficients `f m` of an L-series are zero for `m ≤ n` and the L-series converges
at some point, then `f (n+1)` is the limit of `(n+1)^x * LSeries f x` as `x → ∞`. -/
lemma LSeries.tendsto_cpow_mul_atTop {f : ℕ → ℂ} {n : ℕ} (h : ∀ m ≤ n, f m = 0)
    (ha : abscissaOfAbsConv f < ⊤) :
    Tendsto (fun x : ℝ ↦ (n + 1) ^ (x : ℂ) * LSeries f x) atTop (nhds (f (n + 1))) := by
  obtain ⟨y, hay, hyt⟩ := exists_between ha
  lift y to ℝ using ⟨hyt.ne, ((OrderBot.bot_le _).trans_lt hay).ne'⟩
  -- `F x m` is the `m`th term of `(n+1)^x * LSeries f x`, except that `F x (n+1) = 0`
  let F := fun (x : ℝ) ↦ {m | n + 1 < m}.indicator (fun m ↦ f m / (m / (n + 1) : ℂ) ^ (x : ℂ))
  have hF₀ (x : ℝ) {m : ℕ} (hm : m ≤ n + 1) : F x m = 0 := by simp [F, not_lt_of_ge hm]
  have hF (x : ℝ) {m : ℕ} (hm : m ≠ n + 1) : F x m = ((n + 1) ^ (x : ℂ)) * term f x m := by
    rcases lt_trichotomy m (n + 1) with H | rfl | H
    · simp [Nat.not_lt_of_gt H, term, h m <| Nat.lt_succ_iff.mp H, F]
    · exact (hm rfl).elim
    · simp [H, term, (n.zero_lt_succ.trans H).ne', F, cpow_mul_div_cpow_eq_div_div_cpow]
  have hs {x : ℝ} (hx : x ≥ y) : Summable fun m ↦ (n + 1) ^ (x : ℂ) * term f x m := by
    refine (summable_mul_left_iff <| natCast_add_one_cpow_ne_zero n _).mpr <|
       LSeriesSummable_of_abscissaOfAbsConv_lt_re ?_
    simpa only [ofReal_re] using hay.trans_le <| EReal.coe_le_coe_iff.mpr hx
  -- we can write `(n+1)^x * LSeries f x` as `f (n+1)` plus the series over `F x`
  have key : ∀ x ≥ y, (n + 1) ^ (x : ℂ) * LSeries f x = f (n + 1) + ∑' m : ℕ, F x m := by
    intro x hx
    rw [LSeries, ← tsum_mul_left, (hs hx).tsum_eq_add_tsum_ite (n + 1), pow_mul_term_eq f x n]
    congr
    ext1 m
    rcases eq_or_ne m (n + 1) with rfl | hm
    · simp [hF₀ x le_rfl]
    · simp [hm, hF]
  -- reduce to showing that `∑' m, F x m → 0` as `x → ∞`
  conv => enter [3, 1]; rw [← add_zero (f _)]
  refine Tendsto.congr'
    (eventuallyEq_of_mem (s := {x | y ≤ x}) (mem_atTop y) key).symm <| tendsto_const_nhds.add ?_
  -- get the prerequisites for applying dominated convergence
  have hys : Summable (F y) := by
    refine ((hs le_rfl).indicator {m | n + 1 < m}).congr fun m ↦ ?_
    by_cases hm : n + 1 < m
    · simp [hF, hm, hm.ne']
    · simp [hm, hF₀ _ (le_of_not_gt hm)]
  have hc (k : ℕ) : Tendsto (F · k) atTop (nhds 0) := by
    rcases lt_or_ge (n + 1) k with H | H
    · have H₀ : (0 : ℝ) ≤ k / (n + 1) := by positivity
      have H₀' : (0 : ℝ) ≤ (n + 1) / k := by positivity
      have H₁ : (k / (n + 1) : ℂ) = (k / (n + 1) : ℝ) := by push_cast; rfl
      have H₂ : (n + 1) / k < (1 : ℝ) :=
        (div_lt_one <| mod_cast n.succ_pos.trans H).mpr <| mod_cast H
      simp only [Set.mem_setOf_eq, H, Set.indicator_of_mem, F]
      conv =>
        enter [1, x]
        rw [div_eq_mul_inv, H₁, ← ofReal_cpow H₀, ← ofReal_inv, ← Real.inv_rpow H₀, inv_div]
      conv => enter [3, 1]; rw [← mul_zero (f k)]
      exact
        (tendsto_rpow_atTop_of_base_lt_one _ (neg_one_lt_zero.trans_le H₀') H₂).ofReal.const_mul _
    · simp [hF₀ _ H]
  rw [show (0 : ℂ) = tsum (fun _ : ℕ ↦ 0) from tsum_zero.symm]
  refine tendsto_tsum_of_dominated_convergence hys.norm hc <| eventually_iff.mpr ?_
  filter_upwards [mem_atTop y] with y' hy' k
  -- it remains to show that `‖F y' k‖ ≤ ‖F y k‖` (for `y' ≥ y`)
  rcases lt_or_ge (n + 1) k with H | H
  · simp only [Set.mem_setOf_eq, H, Set.indicator_of_mem, norm_div, norm_cpow_real,
      Complex.norm_natCast, F]
    rw [← Nat.cast_one, ← Nat.cast_add, Complex.norm_natCast]
    have hkn : 1 ≤ (k / (n + 1 :) : ℝ) :=
      (one_le_div (by positivity)).mpr <| mod_cast Nat.le_of_succ_le H
    gcongr
    assumption
  · simp [hF₀ _ H]

open Filter in
/-- If the L-series of `f` converges at some point, then `f 1` is the limit of `LSeries f x`
as `x → ∞`. -/
lemma LSeries.tendsto_atTop {f : ℕ → ℂ} (ha : abscissaOfAbsConv f < ⊤) :
    Tendsto (fun x : ℝ ↦ LSeries f x) atTop (nhds (f 1)) := by
  let F (n : ℕ) : ℂ := if n = 0 then 0 else f n
  have hF₀ : F 0 = 0 := rfl
  have hF {n : ℕ} (hn : n ≠ 0) : F n = f n := if_neg hn
  have ha' : abscissaOfAbsConv F < ⊤ := (abscissaOfAbsConv_congr hF).symm ▸ ha
  simp_rw [← LSeries_congr _ hF]
  convert LSeries.tendsto_cpow_mul_atTop (n := 0) (fun _ hm ↦ Nat.le_zero.mp hm ▸ hF₀) ha' using 1
  simp

lemma LSeries_eq_zero_of_abscissaOfAbsConv_eq_top {f : ℕ → ℂ} (h : abscissaOfAbsConv f = ⊤) :
    LSeries f = 0 := by
  ext1 s
  exact LSeries.eq_zero_of_not_LSeriesSummable f s <| mt LSeriesSummable.abscissaOfAbsConv_le <|
    h ▸ fun H ↦ (H.trans_lt <| EReal.coe_lt_top _).false

open Filter Nat in
/-- The `LSeries` of `f` is zero for large real arguments if and only if either `f n = 0`
for all `n ≠ 0` or the L-series converges nowhere. -/
lemma LSeries_eventually_eq_zero_iff' {f : ℕ → ℂ} :
    (fun x : ℝ ↦ LSeries f x) =ᶠ[atTop] 0 ↔ (∀ n ≠ 0, f n = 0) ∨ abscissaOfAbsConv f = ⊤ := by
  by_cases h : abscissaOfAbsConv f = ⊤
  · simpa [h] using
      Eventually.of_forall <| by simp [LSeries_eq_zero_of_abscissaOfAbsConv_eq_top h]
  · simp only [ne_eq, h, or_false]
    refine ⟨fun H ↦ ?_, fun H ↦ Eventually.of_forall fun x ↦ ?_⟩
    · let F (n : ℕ) : ℂ := if n = 0 then 0 else f n
      have hF₀ : F 0 = 0 := rfl
      have hF {n : ℕ} (hn : n ≠ 0) : F n = f n := if_neg hn
      suffices ∀ n, F n = 0 from fun n hn ↦ (hF hn).symm.trans (this n)
      have ha : ¬ abscissaOfAbsConv F = ⊤ := abscissaOfAbsConv_congr hF ▸ h
      have h' (x : ℝ) : LSeries F x = LSeries f x := LSeries_congr x hF
      have H' (n : ℕ) : (fun x : ℝ ↦ n ^ (x : ℂ) * LSeries F x) =ᶠ[atTop] fun _ ↦ 0 := by
        simp only [h']
        rw [eventuallyEq_iff_exists_mem] at H ⊢
        obtain ⟨s, hs⟩ := H
        exact ⟨s, hs.1, fun x hx ↦ by simp [hs.2 hx]⟩
      intro n
      induction n using Nat.strongRecOn with | ind n ih =>
      -- it suffices to show that `n ^ x * LSeries F x` tends to `F n` as `x` tends to `∞`
      suffices Tendsto (fun x : ℝ ↦ n ^ (x : ℂ) * LSeries F x) atTop (nhds (F n)) by
        replace this := this.congr' <| H' n
        simp only [tendsto_const_nhds_iff] at this
        exact this.symm
      cases n with
      | zero => exact Tendsto.congr' (H' 0).symm <| by simp [hF₀]
      | succ n =>
          simpa using LSeries.tendsto_cpow_mul_atTop (fun m hm ↦ ih m <| lt_succ_of_le hm) <|
            Ne.lt_top ha
    · simp [LSeries_congr x fun {n} ↦ H n, show (fun _ : ℕ ↦ (0 : ℂ)) = 0 from rfl]

open Nat in
/-- Assuming `f 0 = 0`, the `LSeries` of `f` is zero if and only if either `f = 0` or the
L-series converges nowhere. -/
lemma LSeries_eq_zero_iff {f : ℕ → ℂ} (hf : f 0 = 0) :
    LSeries f = 0 ↔ f = 0 ∨ abscissaOfAbsConv f = ⊤ := by
  by_cases h : abscissaOfAbsConv f = ⊤
  · simpa [h] using LSeries_eq_zero_of_abscissaOfAbsConv_eq_top h
  · simp only [h, or_false]
    refine ⟨fun H ↦ ?_, fun H ↦ H ▸ LSeries_zero⟩
    convert (LSeries_eventually_eq_zero_iff'.mp ?_).resolve_right h
    · refine ⟨fun H' _ _ ↦ by rw [H', Pi.zero_apply], fun H' ↦ ?_⟩
      ext (- | m)
      · simp [hf]
      · simp [H']
    · simpa only [H] using Filter.EventuallyEq.rfl

open Filter in
/-- If the `LSeries` of `f` and of `g` converge somewhere and agree on large real arguments,
then the L-series of `f - g` is zero for large real arguments. -/
lemma LSeries_sub_eventuallyEq_zero_of_LSeries_eventually_eq {f g : ℕ → ℂ}
    (hf : abscissaOfAbsConv f < ⊤) (hg : abscissaOfAbsConv g < ⊤)
    (h : (fun x : ℝ ↦ LSeries f x) =ᶠ[atTop] fun x ↦ LSeries g x) :
    (fun x : ℝ ↦ LSeries (f - g) x) =ᶠ[atTop] (0 : ℝ → ℂ) := by
  rw [EventuallyEq, eventually_atTop] at h ⊢
  obtain ⟨x₀, hx₀⟩ := h
  obtain ⟨yf, hyf₁, hyf₂⟩ := exists_between hf
  obtain ⟨yg, hyg₁, hyg₂⟩ := exists_between hg
  lift yf to ℝ using ⟨hyf₂.ne, ((OrderBot.bot_le _).trans_lt hyf₁).ne'⟩
  lift yg to ℝ using ⟨hyg₂.ne, ((OrderBot.bot_le _).trans_lt hyg₁).ne'⟩
  refine ⟨max x₀ (max yf yg), fun x hx ↦ ?_⟩
  have Hf : LSeriesSummable f x := by
    refine LSeriesSummable_of_abscissaOfAbsConv_lt_re <|
      (ofReal_re x).symm ▸ hyf₁.trans_le (EReal.coe_le_coe_iff.mpr ?_)
    exact (le_max_left _ yg).trans <| (le_max_right x₀ _).trans hx
  have Hg : LSeriesSummable g x := by
    refine LSeriesSummable_of_abscissaOfAbsConv_lt_re <|
      (ofReal_re x).symm ▸ hyg₁.trans_le (EReal.coe_le_coe_iff.mpr ?_)
    exact (le_max_right yf _).trans <| (le_max_right x₀ _).trans hx
  rw [LSeries_sub Hf Hg, hx₀ x <| (le_max_left ..).trans hx, sub_self, Pi.zero_apply]

open Filter in
/-- If the `LSeries` of `f` and of `g` converge somewhere and agree on large real arguments,
then `f n = g n` whenever `n ≠ 0`. -/
lemma LSeries.eq_of_LSeries_eventually_eq {f g : ℕ → ℂ} (hf : abscissaOfAbsConv f < ⊤)
    (hg : abscissaOfAbsConv g < ⊤) (h : (fun x : ℝ ↦ LSeries f x) =ᶠ[atTop] fun x ↦ LSeries g x)
    {n : ℕ} (hn : n ≠ 0) :
    f n = g n := by
  have hsub : (fun x : ℝ ↦ LSeries (f - g) x) =ᶠ[atTop] (0 : ℝ → ℂ) :=
    LSeries_sub_eventuallyEq_zero_of_LSeries_eventually_eq hf hg h
  have ha : abscissaOfAbsConv (f - g) ≠ ⊤ :=
    lt_top_iff_ne_top.mp <| (abscissaOfAbsConv_sub_le f g).trans_lt <| max_lt hf hg
  simpa only [Pi.sub_apply, sub_eq_zero]
    using (LSeries_eventually_eq_zero_iff'.mp hsub).resolve_right ha n hn

/-- If the `LSeries` of `f` and of `g` both converge somewhere, then they are equal if and only
if `f n = g n` whenever `n ≠ 0`. -/
lemma LSeries_eq_iff_of_abscissaOfAbsConv_lt_top {f g : ℕ → ℂ} (hf : abscissaOfAbsConv f < ⊤)
    (hg : abscissaOfAbsConv g < ⊤) :
    LSeries f = LSeries g ↔ ∀ n ≠ 0, f n = g n := by
  refine ⟨fun H n hn ↦ ?_, fun H ↦ funext (LSeries_congr · fun {n} ↦ H n)⟩
  refine eq_of_LSeries_eventually_eq hf hg ?_ hn
  exact Filter.Eventually.of_forall fun x ↦ congr_fun H x

/-- The map `f ↦ LSeries f` is injective on functions `f` such that `f 0 = 0` and the L-series
of `f` converges somewhere. -/
lemma LSeries_injOn : Set.InjOn LSeries {f | f 0 = 0 ∧ abscissaOfAbsConv f < ⊤} := by
  intro f hf g hg h
  simp only [Set.mem_setOf] at hf hg
  replace h := (LSeries_eq_iff_of_abscissaOfAbsConv_lt_top hf.2 hg.2).mp h
  ext1 n
  cases n with
  | zero => exact hf.1.trans hg.1.symm
  | succ n => exact h _ n.zero_ne_add_one.symm
