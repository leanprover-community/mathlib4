/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.FundThmCalculus

#align_import analysis.special_functions.non_integrable from "leanprover-community/mathlib"@"55ec6e9af7d3e0043f57e394cb06a72f6275273e"

/-!
# Non integrable functions

In this file we prove that the derivative of a function that tends to infinity is not interval
integrable, see `not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_filter` and
`not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_punctured`. Then we apply the
latter lemma to prove that the function `fun x => x⁻¹` is integrable on `a..b` if and only if
`a = b` or `0 ∉ [a, b]`.

## Main results

* `not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_punctured`: if `f` tends to infinity
  along `𝓝[≠] c` and `f' = O(g)` along the same filter, then `g` is not interval integrable on any
  nontrivial integral `a..b`, `c ∈ [a, b]`.

* `not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_filter`: a version of
  `not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_punctured` that works for one-sided
  neighborhoods;

* `not_intervalIntegrable_of_sub_inv_isBigO_punctured`: if `1 / (x - c) = O(f)` as `x → c`, `x ≠ c`,
  then `f` is not interval integrable on any nontrivial interval `a..b`, `c ∈ [a, b]`;

* `intervalIntegrable_sub_inv_iff`, `intervalIntegrable_inv_iff`: integrability conditions for
  `(x - c)⁻¹` and `x⁻¹`.

## Tags

integrable function
-/


open scoped MeasureTheory Topology Interval NNReal ENNReal

open MeasureTheory TopologicalSpace Set Filter Asymptotics intervalIntegral

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]

/-- If `f` is eventually differentiable along a nontrivial filter `l : Filter ℝ` that is generated
by convex sets, the norm of `f` tends to infinity along `l`, and `f' = O(g)` along `l`, where `f'`
is the derivative of `f`, then `g` is not integrable on any set `k` belonging to `l`.
Auxiliary version assuming that `E` is complete. -/
theorem not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter_aux
    [CompleteSpace E] {f : ℝ → E} {g : ℝ → F}
    {k : Set ℝ} (l : Filter ℝ) [NeBot l] [TendstoIxxClass Icc l l]
    (hl : k ∈ l) (hd : ∀ᶠ x in l, DifferentiableAt ℝ f x) (hf : Tendsto (fun x => ‖f x‖) l atTop)
    (hfg : deriv f =O[l] g) : ¬IntegrableOn g k := by
  intro hgi
  obtain ⟨C, hC₀, s, hsl, hsub, hfd, hg⟩ :
    ∃ (C : ℝ) (_ : 0 ≤ C), ∃ s ∈ l, (∀ x ∈ s, ∀ y ∈ s, [[x, y]] ⊆ k) ∧
      (∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ [[x, y]], DifferentiableAt ℝ f z) ∧
        ∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ [[x, y]], ‖deriv f z‖ ≤ C * ‖g z‖ := by
    rcases hfg.exists_nonneg with ⟨C, C₀, hC⟩
    have h : ∀ᶠ x : ℝ × ℝ in l.prod l,
        ∀ y ∈ [[x.1, x.2]], (DifferentiableAt ℝ f y ∧ ‖deriv f y‖ ≤ C * ‖g y‖) ∧ y ∈ k :=
      (tendsto_fst.uIcc tendsto_snd).eventually ((hd.and hC.bound).and hl).smallSets
    rcases mem_prod_self_iff.1 h with ⟨s, hsl, hs⟩
    simp only [prod_subset_iff, mem_setOf_eq] at hs
    exact ⟨C, C₀, s, hsl, fun x hx y hy z hz => (hs x hx y hy z hz).2, fun x hx y hy z hz =>
      (hs x hx y hy z hz).1.1, fun x hx y hy z hz => (hs x hx y hy z hz).1.2⟩
  replace hgi : IntegrableOn (fun x ↦ C * ‖g x‖) k := by exact hgi.norm.smul C
  obtain ⟨c, hc, d, hd, hlt⟩ : ∃ c ∈ s, ∃ d ∈ s, (‖f c‖ + ∫ y in k, C * ‖g y‖) < ‖f d‖ := by
    rcases Filter.nonempty_of_mem hsl with ⟨c, hc⟩
    have : ∀ᶠ x in l, (‖f c‖ + ∫ y in k, C * ‖g y‖) < ‖f x‖ :=
      hf.eventually (eventually_gt_atTop _)
    exact ⟨c, hc, (this.and hsl).exists.imp fun d hd => ⟨hd.2, hd.1⟩⟩
  specialize hsub c hc d hd; specialize hfd c hc d hd
  replace hg : ∀ x ∈ Ι c d, ‖deriv f x‖ ≤ C * ‖g x‖ :=
    fun z hz => hg c hc d hd z ⟨hz.1.le, hz.2⟩
  have hg_ae : ∀ᵐ x ∂volume.restrict (Ι c d), ‖deriv f x‖ ≤ C * ‖g x‖ :=
    (ae_restrict_mem measurableSet_uIoc).mono hg
  have hsub' : Ι c d ⊆ k := Subset.trans Ioc_subset_Icc_self hsub
  have hfi : IntervalIntegrable (deriv f) volume c d := by
    rw [intervalIntegrable_iff]
    have : IntegrableOn (fun x ↦ C * ‖g x‖) (Ι c d) := IntegrableOn.mono hgi hsub' le_rfl
    exact Integrable.mono' this (aestronglyMeasurable_deriv _ _) hg_ae
  refine hlt.not_le (sub_le_iff_le_add'.1 ?_)
  calc
    ‖f d‖ - ‖f c‖ ≤ ‖f d - f c‖ := norm_sub_norm_le _ _
    _ = ‖∫ x in c..d, deriv f x‖ := congr_arg _ (integral_deriv_eq_sub hfd hfi).symm
    _ = ‖∫ x in Ι c d, deriv f x‖ := norm_integral_eq_norm_integral_Ioc _
    _ ≤ ∫ x in Ι c d, ‖deriv f x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x in Ι c d, C * ‖g x‖ :=
      setIntegral_mono_on hfi.norm.def' (hgi.mono_set hsub') measurableSet_uIoc hg
    _ ≤ ∫ x in k, C * ‖g x‖ := by
      apply setIntegral_mono_set hgi
        (ae_of_all _ fun x => mul_nonneg hC₀ (norm_nonneg _)) hsub'.eventuallyLE

theorem not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter
    {f : ℝ → E} {g : ℝ → F}
    {k : Set ℝ} (l : Filter ℝ) [NeBot l] [TendstoIxxClass Icc l l]
    (hl : k ∈ l) (hd : ∀ᶠ x in l, DifferentiableAt ℝ f x) (hf : Tendsto (fun x => ‖f x‖) l atTop)
    (hfg : deriv f =O[l] g) : ¬IntegrableOn g k := by
  let a : E →ₗᵢ[ℝ] UniformSpace.Completion E := UniformSpace.Completion.toComplₗᵢ
  let f' := a ∘ f
  have h'd : ∀ᶠ x in l, DifferentiableAt ℝ f' x := by
    filter_upwards [hd] with x hx using a.toContinuousLinearMap.differentiableAt.comp x hx
  have h'f : Tendsto (fun x => ‖f' x‖) l atTop := hf.congr (fun x ↦ by simp [f'])
  have h'fg : deriv f' =O[l] g := by
    apply IsBigO.trans _ hfg
    rw [← isBigO_norm_norm]
    suffices (fun x ↦ ‖deriv f' x‖) =ᶠ[l] (fun x ↦ ‖deriv f x‖) by exact this.isBigO
    filter_upwards [hd] with x hx
    have : deriv f' x = a (deriv f x) := by
      rw [fderiv.comp_deriv x _ hx]
      · have : fderiv ℝ a (f x) = a.toContinuousLinearMap := a.toContinuousLinearMap.fderiv
        simp only [this]
        rfl
      · exact a.toContinuousLinearMap.differentiableAt
    simp only [this]
    simp
  exact not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter_aux l hl h'd h'f h'fg

/-- If `f` is eventually differentiable along a nontrivial filter `l : Filter ℝ` that is generated
by convex sets, the norm of `f` tends to infinity along `l`, and `f' = O(g)` along `l`, where `f'`
is the derivative of `f`, then `g` is not integrable on any interval `a..b` such that
`[a, b] ∈ l`. -/
theorem not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_filter {f : ℝ → E} {g : ℝ → F}
    {a b : ℝ} (l : Filter ℝ) [NeBot l] [TendstoIxxClass Icc l l] (hl : [[a, b]] ∈ l)
    (hd : ∀ᶠ x in l, DifferentiableAt ℝ f x) (hf : Tendsto (fun x => ‖f x‖) l atTop)
    (hfg : deriv f =O[l] g) : ¬IntervalIntegrable g volume a b := by
  rw [intervalIntegrable_iff']
  exact not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter _ hl hd hf hfg
set_option linter.uppercaseLean3 false in
#align not_interval_integrable_of_tendsto_norm_at_top_of_deriv_is_O_filter not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_filter

/-- If `a ≠ b`, `c ∈ [a, b]`, `f` is differentiable in the neighborhood of `c` within
`[a, b] \ {c}`, `‖f x‖ → ∞` as `x → c` within `[a, b] \ {c}`, and `f' = O(g)` along
`𝓝[[a, b] \ {c}] c`, where `f'` is the derivative of `f`, then `g` is not interval integrable on
`a..b`. -/
theorem not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_within_diff_singleton
    {f : ℝ → E} {g : ℝ → F} {a b c : ℝ} (hne : a ≠ b) (hc : c ∈ [[a, b]])
    (h_deriv : ∀ᶠ x in 𝓝[[[a, b]] \ {c}] c, DifferentiableAt ℝ f x)
    (h_infty : Tendsto (fun x => ‖f x‖) (𝓝[[[a, b]] \ {c}] c) atTop)
    (hg : deriv f =O[𝓝[[[a, b]] \ {c}] c] g) : ¬IntervalIntegrable g volume a b := by
  obtain ⟨l, hl, hl', hle, hmem⟩ :
    ∃ l : Filter ℝ, TendstoIxxClass Icc l l ∧ l.NeBot ∧ l ≤ 𝓝 c ∧ [[a, b]] \ {c} ∈ l := by
    cases' (min_lt_max.2 hne).lt_or_lt c with hlt hlt
    · refine ⟨𝓝[<] c, inferInstance, inferInstance, inf_le_left, ?_⟩
      rw [← Iic_diff_right]
      exact diff_mem_nhdsWithin_diff (Icc_mem_nhdsWithin_Iic ⟨hlt, hc.2⟩) _
    · refine ⟨𝓝[>] c, inferInstance, inferInstance, inf_le_left, ?_⟩
      rw [← Ici_diff_left]
      exact diff_mem_nhdsWithin_diff (Icc_mem_nhdsWithin_Ici ⟨hc.1, hlt⟩) _
  have : l ≤ 𝓝[[[a, b]] \ {c}] c := le_inf hle (le_principal_iff.2 hmem)
  exact not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_filter l
    (mem_of_superset hmem diff_subset) (h_deriv.filter_mono this) (h_infty.mono_left this)
    (hg.mono this)
set_option linter.uppercaseLean3 false in
#align not_interval_integrable_of_tendsto_norm_at_top_of_deriv_is_O_within_diff_singleton not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_within_diff_singleton

/-- If `f` is differentiable in a punctured neighborhood of `c`, `‖f x‖ → ∞` as `x → c` (more
formally, along the filter `𝓝[≠] c`), and `f' = O(g)` along `𝓝[≠] c`, where `f'` is the derivative
of `f`, then `g` is not interval integrable on any nontrivial interval `a..b` such that
`c ∈ [a, b]`. -/
theorem not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_punctured {f : ℝ → E}
    {g : ℝ → F} {a b c : ℝ} (h_deriv : ∀ᶠ x in 𝓝[≠] c, DifferentiableAt ℝ f x)
    (h_infty : Tendsto (fun x => ‖f x‖) (𝓝[≠] c) atTop) (hg : deriv f =O[𝓝[≠] c] g) (hne : a ≠ b)
    (hc : c ∈ [[a, b]]) : ¬IntervalIntegrable g volume a b :=
  have : 𝓝[[[a, b]] \ {c}] c ≤ 𝓝[≠] c := nhdsWithin_mono _ inter_subset_right
  not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_within_diff_singleton hne hc
    (h_deriv.filter_mono this) (h_infty.mono_left this) (hg.mono this)
set_option linter.uppercaseLean3 false in
#align not_interval_integrable_of_tendsto_norm_at_top_of_deriv_is_O_punctured not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_punctured

/-- If `f` grows in the punctured neighborhood of `c : ℝ` at least as fast as `1 / (x - c)`,
then it is not interval integrable on any nontrivial interval `a..b`, `c ∈ [a, b]`. -/
theorem not_intervalIntegrable_of_sub_inv_isBigO_punctured {f : ℝ → F} {a b c : ℝ}
    (hf : (fun x => (x - c)⁻¹) =O[𝓝[≠] c] f) (hne : a ≠ b) (hc : c ∈ [[a, b]]) :
    ¬IntervalIntegrable f volume a b := by
  have A : ∀ᶠ x in 𝓝[≠] c, HasDerivAt (fun x => Real.log (x - c)) (x - c)⁻¹ x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa using ((hasDerivAt_id x).sub_const c).log (sub_ne_zero.2 hx)
  have B : Tendsto (fun x => ‖Real.log (x - c)‖) (𝓝[≠] c) atTop := by
    refine tendsto_abs_atBot_atTop.comp (Real.tendsto_log_nhdsWithin_zero.comp ?_)
    rw [← sub_self c]
    exact ((hasDerivAt_id c).sub_const c).tendsto_punctured_nhds one_ne_zero
  exact not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_punctured
    (A.mono fun x hx => hx.differentiableAt) B
    (hf.congr' (A.mono fun x hx => hx.deriv.symm) EventuallyEq.rfl) hne hc
set_option linter.uppercaseLean3 false in
#align not_interval_integrable_of_sub_inv_is_O_punctured not_intervalIntegrable_of_sub_inv_isBigO_punctured

/-- The function `fun x => (x - c)⁻¹` is integrable on `a..b` if and only if
`a = b` or `c ∉ [a, b]`. -/
@[simp]
theorem intervalIntegrable_sub_inv_iff {a b c : ℝ} :
    IntervalIntegrable (fun x => (x - c)⁻¹) volume a b ↔ a = b ∨ c ∉ [[a, b]] := by
  constructor
  · refine fun h => or_iff_not_imp_left.2 fun hne hc => ?_
    exact not_intervalIntegrable_of_sub_inv_isBigO_punctured (isBigO_refl _ _) hne hc h
  · rintro (rfl | h₀)
    · exact IntervalIntegrable.refl
    refine ((continuous_sub_right c).continuousOn.inv₀ ?_).intervalIntegrable
    exact fun x hx => sub_ne_zero.2 <| ne_of_mem_of_not_mem hx h₀
#align interval_integrable_sub_inv_iff intervalIntegrable_sub_inv_iff

/-- The function `fun x => x⁻¹` is integrable on `a..b` if and only if
`a = b` or `0 ∉ [a, b]`. -/
@[simp]
theorem intervalIntegrable_inv_iff {a b : ℝ} :
    IntervalIntegrable (fun x => x⁻¹) volume a b ↔ a = b ∨ (0 : ℝ) ∉ [[a, b]] := by
  simp only [← intervalIntegrable_sub_inv_iff, sub_zero]
#align interval_integrable_inv_iff intervalIntegrable_inv_iff

/-- The function `fun x ↦ x⁻¹` is not integrable on any interval `[a, +∞)`. -/
theorem not_IntegrableOn_Ici_inv {a : ℝ} :
    ¬ IntegrableOn (fun x => x⁻¹) (Ici a) := by
  have A : ∀ᶠ x in atTop, HasDerivAt (fun x => Real.log x) x⁻¹ x := by
    filter_upwards [Ioi_mem_atTop 0] with x hx using Real.hasDerivAt_log (ne_of_gt hx)
  have B : Tendsto (fun x => ‖Real.log x‖) atTop atTop :=
    tendsto_norm_atTop_atTop.comp Real.tendsto_log_atTop
  exact not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter atTop (Ici_mem_atTop a)
    (A.mono (fun x hx ↦ hx.differentiableAt)) B
    (Filter.EventuallyEq.isBigO (A.mono (fun x hx ↦ hx.deriv)))

/-- The function `fun x ↦ x⁻¹` is not integrable on any interval `(a, +∞)`. -/
theorem not_IntegrableOn_Ioi_inv {a : ℝ} :
    ¬ IntegrableOn (·⁻¹) (Ioi a) := by
  simpa only [IntegrableOn, restrict_Ioi_eq_restrict_Ici] using not_IntegrableOn_Ici_inv
