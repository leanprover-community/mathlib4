/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

module

public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.EReal.Inv
public import Mathlib.RingTheory.PowerSeries.Order

/-!
# Order at infinity

We define the "order at infinity" of a function `ℍ → ℂ` as the supremum of `t` such that
`f = O(exp (-2 * π * τ.im * t))` as `Im τ → ∞`. This definition is deliberately chosen to be
independent of any holomorphy or periodicity hypotheses; but if `f` is periodic and
holomorphic on `ℍ ∪ ∞`, we show that the order of vanishing is determined by the order of
vanishing of its `q`-expansion (divided by the period).

### Main statements (general functions)

* `UpperHalfPlane.le_orderAtInfty_iff`: the order is at least `t` iff there is an exponential
  bound at every rate `s < t`.
* `UpperHalfPlane.orderAtInfty_mul`: the order of a product is at least the sum of the orders.

### Main statements (periodic holomorphic functions)

Here the functions are holomorphic on `ℍ`, bounded at infinity, and periodic with positive
period `h`. (The obvious examples are modular forms, but we keep the hypotheses un-bundled, since
only the periodicity is relevant here.)

* `UpperHalfPlane.orderAtInfty_eq_qExpansion_order`: the order at infinity equals the order of
  the `q`-expansion divided by `h`.
* `UpperHalfPlane.isTheta_orderAtInfty`: a nonzero function has exact exponential decay rate
  given by its order at infinity.
* `UpperHalfPlane.orderAtInfty_eq_top_iff_eq_zero`: the order is infinite iff the function is zero.
* `UpperHalfPlane.orderAtInfty_mul_of_holo`: the order of a product equals the sum of the orders.

-/

open Real Function

open scoped Manifold

private lemma EReal.eq_top_iff_forall_ge (t : EReal) : t = ⊤ ↔ ∀ (s : ℝ), s ≤ t :=
  WithBot.eq_top_iff_forall_ge

public section

namespace UpperHalfPlane

/-!
## Elementary theory for arbitrary functions
-/

variable {E : Type*} {f g : ℍ → E} {s t : ℝ}

section Norm
variable [Norm E]

/-- The supremum of `t` such that `f = O (exp (-2 * π * τ.im * t))` as `Im τ → ∞`. We take the
supremum as an `EReal`, so the zero function has order `+∞`, and a function with no exponential
bound has order `-∞`. See `lt_orderAtInfty_iff` and `le_orderAtInfty_iff` for characterizations. -/
noncomputable def orderAtInfty (f : ℍ → E) : EReal :=
    ⨆ t : {t : ℝ // f =O[atImInfty] fun τ ↦ Real.exp (-2 * π * τ.im * t)}, (t : EReal)

lemma le_orderAtInfty_of_isBigO (ht : f =O[atImInfty] fun τ ↦ exp (-2 * π * τ.im * t)) :
    t ≤ orderAtInfty f :=
  le_iSup_iff_forall_lt.mpr fun _ hs ↦ ⟨⟨t, ht⟩, hs⟩

private lemma exp_decay_isBigO_of_le (hst : s ≤ t) :
    (fun τ : ℍ ↦ exp (-2 * π * τ.im * t)) =O[atImInfty] fun τ ↦ exp (-2 * π * τ.im * s) := by
  refine .of_bound 1 (.of_forall fun τ ↦ ?_)
  simp only [Real.norm_eq_abs, abs_exp, one_mul, exp_le_exp]
  linear_combination 2 * π * τ.im * hst

lemma le_orderAtInfty_iff :
    t ≤ orderAtInfty f ↔ ∀ s < t, f =O[atImInfty] fun τ ↦ exp (-2 * π * τ.im * s) where
  mp ht s hst := by
    have hs : s < orderAtInfty f := (EReal.coe_lt_coe hst).trans_le ht
    rw [orderAtInfty, lt_iSup_iff] at hs
    obtain ⟨u, hsu⟩ := hs
    exact u.property.trans <| exp_decay_isBigO_of_le (EReal.coe_lt_coe_iff.mp hsu).le
  mpr ht := by
    rw [orderAtInfty, le_iSup_iff_forall_lt]
    intro u hu
    obtain ⟨s, hus, hst⟩ := EReal.lt_iff_exists_real_btwn.mp hu
    aesop

lemma lt_orderAtInfty_iff :
    t < orderAtInfty f ↔ ∃ s > t, f =O[atImInfty] fun τ ↦ exp (-2 * π * τ.im * s) := by
  rw [orderAtInfty, lt_iSup_iff]
  aesop

lemma orderAtInfty_eq_top_iff :
    orderAtInfty f = ⊤ ↔ ∀ (t : ℝ), f =O[atImInfty] fun τ ↦ exp (-2 * π * τ.im * t) := by
  simp only [EReal.eq_top_iff_forall_lt, lt_orderAtInfty_iff]
  exact ⟨fun hf s ↦ match hf s with | ⟨t, hst, hf⟩ => hf.trans (exp_decay_isBigO_of_le hst.le),
    fun hf y ↦ match exists_gt y with | ⟨s, hs⟩ => ⟨s, hs, hf s⟩⟩

lemma IsBoundedAtImInfty.orderAtInfty_nonneg (hf : IsBoundedAtImInfty f) :
    0 ≤ orderAtInfty f := by
  apply le_orderAtInfty_of_isBigO
  simpa [-Asymptotics.isBigO_one_iff, Pi.one_def, IsBoundedAtImInfty, Filter.BoundedAtFilter]
      using hf

/-- Real translations preserve the order at infinity. -/
lemma orderAtInfty_vadd (x : ℝ) :
    orderAtInfty (fun τ ↦ f (x +ᵥ τ)) = orderAtInfty f := by
  have hle (f : ℍ → E) (x : ℝ) : orderAtInfty f ≤ orderAtInfty (fun τ ↦ f (x +ᵥ τ)) := by
    refine iSup_le fun ⟨t, ht⟩ ↦ le_orderAtInfty_of_isBigO ?_
    have hx : Filter.Tendsto (fun τ : ℍ ↦ x +ᵥ τ) atImInfty atImInfty := by
      simpa [atImInfty, Filter.tendsto_comap_iff, Function.comp_def] using
        (Filter.tendsto_comap : Filter.Tendsto im atImInfty Filter.atTop)
    simpa only [Function.comp_def, vadd_im] using ht.comp_tendsto hx
  exact le_antisymm (by simpa using hle (fun τ ↦ f (x +ᵥ τ)) (-x)) (hle f x)

end Norm

section SeminormedAddCommGroup
variable [SeminormedAddCommGroup E]

/-- Matching exponential upper and lower bounds determine the order at infinity. -/
private lemma orderAtInfty_eq_of_isTheta
    (hf : f =Θ[atImInfty] fun τ ↦ exp (-2 * π * τ.im * t)) : orderAtInfty f = t := by
  refine le_antisymm (le_of_not_gt fun ht ↦ ?_) (le_orderAtInfty_of_isBigO hf.1)
  obtain ⟨s, hts, hs⟩ := lt_orderAtInfty_iff.mp ht
  have hb := Real.isBigO_exp_comp_exp_comp.mp (hf.2.trans hs)
  apply Filter.not_isBoundedUnder_of_tendsto_atTop (l := atImInfty) _ hb
  -- A faster exponential bound would make a positive multiple of `Im τ` bounded above.
  convert! (Filter.tendsto_comap : Filter.Tendsto im atImInfty Filter.atTop).const_mul_atTop
    (show 0 < 2 * π * (s - t) by positivity) using 1
  ext τ
  simp only [Pi.sub_apply]
  ring

end SeminormedAddCommGroup

section SeminormedRing
variable [SeminormedCommRing E]
-- commutativity is not needed, but it shortens the proof, and we only really need `E = ℂ` anyway

lemma orderAtInfty_mul : orderAtInfty f + orderAtInfty g ≤ orderAtInfty (f * g) := by
  wlog! hfg : orderAtInfty g ≤ orderAtInfty f
  · simpa [add_comm, mul_comm] using this hfg.le
  have aux {a b c : ℝ} {f g : ℍ → E} (hf : f =O[atImInfty] fun τ ↦ exp (-2 * π * τ.im * a))
      (hg : g =O[atImInfty] fun τ ↦ exp (-2 * π * τ.im * b)) (habc : a + b = c) :
      (f * g) =O[atImInfty] fun τ ↦ exp (-2 * π * τ.im * c) := by
    convert! hf.mul hg using 1
    ext τ
    rw [← exp_add, exp_eq_exp, ← habc]
    ring
  generalize hs : orderAtInfty f = s
  generalize ht : orderAtInfty g = t
  rw [hs, ht] at hfg
  cases s with
  | bot => simp
  | top => cases t with
    | bot => simp
    | coe t =>
      -- Exactly one of `s, t` is `⊤` and the other is finite.
      simp only [EReal.top_add_coe, top_le_iff, orderAtInfty_eq_top_iff] at hs ⊢
      intro u
      obtain ⟨v, hv⟩ := exists_lt t
      refine aux (hs (u - v)) (le_orderAtInfty_iff.mp ht.ge v hv) (by abel)
    | top =>
      -- Both of `s, t` are `⊤`.
      simp only [EReal.top_add_top, top_le_iff, orderAtInfty_eq_top_iff] at hs ht ⊢
      exact fun u ↦ aux (hs _) (ht _) (add_halves u)
  | coe s => cases t with
    | bot => simp
    | top => grind [EReal.coe_ne_top]
    | coe t =>
      -- Both `s, t` are finite.
      replace hs := hs.ge
      replace ht := ht.ge
      simp only [← EReal.coe_add, le_orderAtInfty_iff] at hs ht ⊢
      refine fun u hu ↦ aux (hs ((u + s - t) / 2) ?_) (ht ((u - s + t) / 2) ?_) ?_ <;>
      grind

/-- The order of a finite product is at least the sum of the orders of its factors. -/
lemma orderAtInfty_prod {ι : Type*} (s : Finset ι) (F : ι → ℍ → E) :
    ∑ i ∈ s, orderAtInfty (F i) ≤ orderAtInfty (∏ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using IsBoundedAtImInfty.orderAtInfty_nonneg
      (Filter.const_boundedAtFilter atImInfty (1 : E))
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact (add_le_add le_rfl ih).trans
      (orderAtInfty_mul (f := F i) (g := ∏ j ∈ s, F j))

end SeminormedRing

/-- Taking norms preserves the order at infinity. -/
lemma orderAtInfty_norm [SeminormedAddCommGroup E] (f : ℍ → E) :
    orderAtInfty (fun τ ↦ ‖f τ‖) = orderAtInfty f := by
  have hiff (t : ℝ) : t < orderAtInfty (fun τ ↦ ‖f τ‖) ↔ t < orderAtInfty f := by
    simp only [lt_orderAtInfty_iff, Asymptotics.isBigO_norm_left]
  apply le_antisymm
  · by_contra! h
    obtain ⟨t, ht, ht'⟩ := EReal.lt_iff_exists_real_btwn.mp h
    exact ht.not_gt ((hiff t).mp ht')
  · by_contra! h
    obtain ⟨t, ht, ht'⟩ := EReal.lt_iff_exists_real_btwn.mp h
    exact ht.not_gt ((hiff t).mpr ht')

/-- A change of variables which scales imaginary parts scales the order by the same factor. -/
lemma orderAtInfty_comp_equiv [Norm E] (f : ℍ → E) (e : ℍ ≃ ℍ) {a : ℝ} (ha : 0 < a)
    (he : ∀ τ, (e τ).im = a * τ.im) :
    orderAtInfty (f ∘ e) = (a : EReal) * orderAtInfty f := by
  have he' (τ : ℍ) : (e.symm τ).im = a⁻¹ * τ.im := by
    rw [← e.apply_symm_apply τ, he]
    simp [ha.ne']
  have hmap : Filter.Tendsto e atImInfty atImInfty := by
    simpa only [atImInfty, Filter.tendsto_comap_iff, Function.comp_def, he] using
      (Filter.tendsto_comap : Filter.Tendsto im atImInfty Filter.atTop).const_mul_atTop ha
  have hmap' : Filter.Tendsto e.symm atImInfty atImInfty := by
    simpa only [atImInfty, Filter.tendsto_comap_iff, Function.comp_def, he'] using
      (Filter.tendsto_comap : Filter.Tendsto im atImInfty Filter.atTop).const_mul_atTop
        (inv_pos.mpr ha)
  have hbigO (t : ℝ) : (f ∘ e) =O[atImInfty] (fun τ ↦ exp (-2 * π * τ.im * t)) ↔
      f =O[atImInfty] (fun τ ↦ exp (-2 * π * τ.im * (t / a))) := by
    constructor
    · intro h
      convert h.comp_tendsto hmap' using 1
      · ext τ; simp
      · ext τ; simp only [Function.comp_def, he']; congr 1; ring
    · intro h
      convert h.comp_tendsto hmap using 1
      ext τ
      simp only [Function.comp_def, he]
      congr 1
      field_simp
  have hiff (t : ℝ) : t < orderAtInfty (f ∘ e) ↔ t < (a : EReal) * orderAtInfty f := by
    rw [mul_comm (a : EReal), ← EReal.div_lt_iff (EReal.coe_pos.mpr ha) (EReal.coe_ne_top _),
      ← EReal.coe_div]
    simp only [lt_orderAtInfty_iff, hbigO]
    constructor
    · rintro ⟨s, hts, hs⟩
      exact ⟨s / a, (div_lt_div_iff_of_pos_right ha).mpr hts, hs⟩
    · rintro ⟨s, hts, hs⟩
      refine ⟨s * a, (div_lt_iff₀ ha).mp hts, ?_⟩
      simpa [ha.ne'] using hs
  apply le_antisymm
  · by_contra! h
    obtain ⟨t, ht, ht'⟩ := EReal.lt_iff_exists_real_btwn.mp h
    exact ht.not_gt ((hiff t).mp ht')
  · by_contra! h
    obtain ⟨t, ht, ht'⟩ := EReal.lt_iff_exists_real_btwn.mp h
    exact ht.not_gt ((hiff t).mpr ht')

/-- Scalar multiplication by a nonzero constant preserves the order. -/
lemma orderAtInfty_const_mul [NormedRing E] [NormMulClass E] (c : E) (hc : c ≠ 0)
    (f : ℍ → E) :
    orderAtInfty (fun τ ↦ c * f τ) = orderAtInfty f := by
  have hiff (t : ℝ) : t < orderAtInfty (fun τ ↦ c * f τ) ↔ t < orderAtInfty f := by
    simp only [lt_orderAtInfty_iff, Asymptotics.isBigO_const_mul_left_iff hc]
  apply le_antisymm
  · by_contra! h
    obtain ⟨t, ht, ht'⟩ := EReal.lt_iff_exists_real_btwn.mp h
    exact ht.not_gt ((hiff t).mp ht')
  · by_contra! h
    obtain ⟨t, ht, ht'⟩ := EReal.lt_iff_exists_real_btwn.mp h
    exact ht.not_gt ((hiff t).mpr ht')

open scoped MatrixGroups ModularForm in
/-- Negating the matrix in a slash operator preserves the order at infinity. -/
lemma orderAtInfty_slash_neg (f : ℍ → ℂ) (k : ℤ) (g : GL (Fin 2) ℝ) :
    orderAtInfty (f ∣[k] (-g)) = orderAtInfty (f ∣[k] g) := by
  rw [← neg_one_mul g, SlashAction.slash_mul]
  have hneg : f ∣[k] (-1 : GL (Fin 2) ℝ) = fun τ ↦ (-1 : ℂ) ^ (-k) * f τ := by
    ext τ
    simp [ModularForm.slash_apply, σ, Matrix.GeneralLinearGroup.val_det_apply,
      Matrix.det_neg, mul_comm]
  rw [hneg]
  have heq : ((fun τ ↦ (-1 : ℂ) ^ (-k) * f τ) ∣[k] g) =
      fun τ ↦ (σ g ((-1 : ℂ) ^ (-k))) * (f ∣[k] g) τ := by
    ext τ
    simp [ModularForm.slash_apply, mul_assoc, map_mul]
  rw [heq]
  apply orderAtInfty_const_mul
  simp [σ, zpow_ne_zero]

open scoped MatrixGroups ModularForm in
/-- An upper triangular slash operator scales the order by its scale factor on imaginary parts. -/
lemma orderAtInfty_slash_of_upperTriangular (f : ℍ → ℂ) (k : ℤ) (g : GL (Fin 2) ℝ)
    (hg : g 1 0 = 0) :
    orderAtInfty (f ∣[k] g) = (|g 0 0 / g 1 1| : ℝ) * orderAtInfty f := by
  have hd : g 1 1 ≠ 0 := by
    intro h
    exact g.det_ne_zero (by simp [Matrix.det_fin_two, hg, h])
  have ha : 0 < |g 0 0 / g 1 1| := by
    simpa [Matrix.det_fin_two, hg] using g.det_ne_zero
  have him (τ : ℍ) : (g • τ).im = |g 0 0 / g 1 1| * τ.im := by
    simp [im_smul, num, denom, hg, abs_div, abs_mul,
      abs_of_pos τ.im_pos, mul_div_right_comm]
  have hnorm : (fun τ ↦ ‖(f ∣[k] g) τ‖) =
      fun τ ↦ (‖g.det.val ^ (k - 1)‖ * ‖g 1 1 ^ (-k)‖) * ‖f (g • τ)‖ := by
    ext τ
    simp [ModularForm.slash_def, denom, hg, mul_assoc, mul_comm ‖f _‖]
  rw [← orderAtInfty_norm (f ∣[k] g), hnorm,
    orderAtInfty_const_mul _ (by simp [hd, g.det_ne_zero, zpow_ne_zero])]
  simpa only [Function.comp_def, MulAction.toPerm_apply, orderAtInfty_norm] using
    orderAtInfty_comp_equiv (fun τ ↦ ‖f τ‖) (MulAction.toPerm g) ha him

open scoped MatrixGroups ModularForm Pointwise in
/-- The width-weighted order is unchanged by an upper triangular change of cusp coordinate. -/
lemma width_mul_orderAtInfty_slash_of_upperTriangular
    (G : Subgroup (GL (Fin 2) ℝ)) [DiscreteTopology G] (hw : 0 < G.widthInfty)
    (f : ℍ → ℂ) (k : ℤ) (g : GL (Fin 2) ℝ) (hg : g 1 0 = 0)
    (ha : 0 < g 0 0 / g 1 1) :
    (ConjAct.toConjAct g⁻¹ • G).widthInfty * orderAtInfty (f ∣[k] g) =
      G.widthInfty * orderAtInfty f := by
  rw [Subgroup.widthInfty_conj_of_upperTriangular hw hg ha,
    orderAtInfty_slash_of_upperTriangular f k g hg, abs_of_pos ha,
    ← mul_assoc, ← EReal.coe_mul, div_mul_cancel₀ _ ha.ne']

open OnePoint in
open scoped MatrixGroups ModularForm Pointwise in
lemma width_mul_orderAtInfty_slash_eq_of_smul_infty_eq
    (G : Subgroup (GL (Fin 2) ℝ)) [DiscreteTopology G]
    (f : ℍ → ℂ) (k : ℤ) (g h : GL (Fin 2) ℝ)
    (hw : 0 < (ConjAct.toConjAct g⁻¹ • G).widthInfty)
    (hcg : g • (∞ : OnePoint ℝ) = h • ∞)
    (hdg : 0 < g.det.val) (hdh : 0 < h.det.val) :
    (ConjAct.toConjAct g⁻¹ • G).widthInfty * orderAtInfty (f ∣[k] g) =
      (ConjAct.toConjAct h⁻¹ • G).widthInfty * orderAtInfty (f ∣[k] h) := by
  let t := g⁻¹ * h
  have ht : t 1 0 = 0 := by
    apply OnePoint.smul_infty_eq_self_iff.mp
    simp only [t, mul_smul, ← hcg, inv_smul_smul]
  have hd : 0 < t.det.val := by
    simpa only [t, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val] using
      mul_pos (inv_pos.mpr hdg) hdh
  have ha : 0 < t 0 0 / t 1 1 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, ht, mul_zero,
      sub_zero] at hd
    exact div_pos_iff.mpr (mul_pos_iff.mp hd)
  have heq := width_mul_orderAtInfty_slash_of_upperTriangular
    (ConjAct.toConjAct g⁻¹ • G) hw (f ∣[k] g) k t ht ha
  simpa only [t, mul_inv_rev, inv_inv, ← ConjAct.toConjAct_mul, ← mul_smul,
    mul_inv_cancel_right, ← SlashAction.slash_mul, mul_inv_cancel_left] using heq.symm

/-!
## Theory for periodic holomorphic functions

If we assume `f` is periodic, and holomorphic on `ℍ ∪ ∞`, then its order at infinity is related
to the order of vanishing of its cusp function.
-/
section Complex

variable {h : ℝ} {f g : ℍ → ℂ}

/-- A nonzero periodic function holomorphic on `ℍ ∪ ∞` has finite order in the cusp coordinate. -/
lemma analyticOrderAt_cuspFunction_ne_top (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h)
    (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) (hfne : f ≠ 0) :
    analyticOrderAt (cuspFunction h f) 0 ≠ ⊤ := by
  refine fun htop ↦ hfne (funext fun τ ↦ ?_)
  rw [← eq_cuspFunction τ hh.ne' hfper]
  have han : AnalyticOnNhd ℂ (cuspFunction h f) (Metric.ball 0 1) :=
    (differentiableOn_cuspFunction_ball hh hfper hfhol hfbdd).analyticOnNhd Metric.isOpen_ball
  have hzero : Set.EqOn (cuspFunction h f) 0 (Metric.ball 0 1) :=
    han.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball 0 1).isPreconnected (by simp)
      (analyticOrderAt_eq_top.mp htop)
  exact hzero (mem_ball_zero_iff.mpr (Periodic.norm_qParam_lt_one hh τ.im_pos))

/-- The asymptotic behaviour of a nonzero periodic function holomorphic on `ℍ ∪ ∞` is determined
by the order of vanishing of its cusp function at zero. -/
theorem isTheta_analyticOrderAt (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h)
    (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) (hfne : f ≠ 0) :
    f =Θ[atImInfty] fun τ ↦ exp (-2 * π * τ.im *
      analyticOrderNatAt (cuspFunction h f) 0 / h) := by
  have han := analyticAt_cuspFunction_zero hh hfper hfhol hfbdd
  have hfinite := analyticOrderAt_cuspFunction_ne_top hh hfper hfhol hfbdd hfne
  obtain ⟨g, hg, hg0, hfg⟩ := han.analyticOrderAt_eq_natCast.mp
    (Nat.cast_analyticOrderNatAt hfinite).symm
  let n := analyticOrderNatAt (cuspFunction h f) 0
  have hlim : Filter.Tendsto (fun τ : ℍ ↦ f τ / Periodic.qParam h τ ^ n)
      atImInfty (nhds (g 0)) := by
    apply (hg.continuousAt.tendsto.comp (qParam_tendsto_atImInfty hh)).congr'
    filter_upwards [(qParam_tendsto_atImInfty hh).eventually hfg] with τ hτ
    rw [eq_cuspFunction τ hh.ne' hfper, sub_zero, smul_eq_mul] at hτ
    simp [hτ, n, Periodic.qParam_ne_zero]
  -- The nonvanishing analytic factor gives matching upper and lower bounds for `q ^ n`.
  convert! (Asymptotics.isTheta_of_div_tendsto_nhds_ne_zero hlim hg0).symm.norm_right using 1
  ext τ
  rw [norm_pow, Periodic.norm_qParam, ← exp_nat_mul, exp_eq_exp]
  simp only [neg_mul, coe_im, n, field]

/-- The order at infinity is the order of the cusp function divided by the period. -/
lemma orderAtInfty_eq_analyticOrderAt_div (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h)
    (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) :
    orderAtInfty f = analyticOrderAt (cuspFunction h f) 0 / h := by
  rcases eq_or_ne f 0 with rfl | hfne
  · have hcusp : cuspFunction h (0 : ℍ → ℂ) = 0 := by
      simp only [cuspFunction, Periodic.cuspFunction, Function.comp_def, Pi.zero_apply]
      rw [(tendsto_const_nhds (x := (0 : ℂ))).limUnder_eq]
      exact update_eq_self 0 (fun _ ↦ 0)
    have horder : analyticOrderAt (0 : ℂ → ℂ) 0 = ⊤ :=
      analyticOrderAt_eq_top.mpr (Filter.Eventually.of_forall fun _ ↦ rfl)
    rw [hcusp, horder, ENat.toENNReal_top, EReal.coe_ennreal_top,
      EReal.top_div_of_pos_ne_top (EReal.coe_pos.mpr hh) (EReal.coe_ne_top h)]
    exact orderAtInfty_eq_top_iff.mpr fun t ↦ Asymptotics.isBigO_zero _ _
  -- For a nonzero function, the analytic order is finite and the theta estimate is exact.
  have hfinite := analyticOrderAt_cuspFunction_ne_top hh hfper hfhol hfbdd hfne
  rw [← Nat.cast_analyticOrderNatAt hfinite]
  have htheta := isTheta_analyticOrderAt hh hfper hfhol hfbdd hfne
  simp only [mul_div_assoc] at htheta
  exact orderAtInfty_eq_of_isTheta htheta

/-- A periodic function holomorphic on `ℍ ∪ ∞` has infinite order exactly when it is zero. -/
lemma orderAtInfty_eq_top_iff_eq_zero (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h)
    (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) :
    orderAtInfty f = ⊤ ↔ f = 0 := by
  constructor
  · intro htop
    by_contra hfne
    have hfinite := analyticOrderAt_cuspFunction_ne_top hh hfper hfhol hfbdd hfne
    rw [orderAtInfty_eq_analyticOrderAt_div hh hfper hfhol hfbdd,
      ← Nat.cast_analyticOrderNatAt hfinite] at htop
    exact EReal.coe_ne_top _ htop
  · rintro rfl
    exact orderAtInfty_eq_top_iff.mpr fun t ↦ Asymptotics.isBigO_zero _ _

/-- A nonzero periodic function holomorphic on `ℍ ∪ ∞` has matching exponential bounds
at the rate given by its order at infinity. -/
lemma isTheta_orderAtInfty (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h)
    (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) (hfne : f ≠ 0) :
    f =Θ[atImInfty] fun τ ↦ exp (-2 * π * τ.im * (orderAtInfty f).toReal) := by
  have hfinite := analyticOrderAt_cuspFunction_ne_top hh hfper hfhol hfbdd hfne
  rw [orderAtInfty_eq_analyticOrderAt_div hh hfper hfhol hfbdd,
    ← Nat.cast_analyticOrderNatAt hfinite, ENat.toENNReal_coe, ← ENNReal.coe_natCast,
    EReal.coe_nnreal_eq_coe_real, NNReal.coe_natCast, ← EReal.coe_div, EReal.toReal_coe]
  simpa only [mul_div_assoc] using
    isTheta_analyticOrderAt hh hfper hfhol hfbdd hfne

/-- The order at infinity is additive on products of periodic functions holomorphic on `ℍ ∪ ∞`. -/
lemma orderAtInfty_mul_of_holo (hh : 0 < h)
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f)
    (hgper : Periodic (g ∘ ofComplex) h) (hghol : MDiff g) (hgbdd : IsBoundedAtImInfty g) :
    orderAtInfty (f * g) = orderAtInfty f + orderAtInfty g := by
  have hf := analyticAt_cuspFunction_zero hh hfper hfhol hfbdd
  have hg := analyticAt_cuspFunction_zero hh hgper hghol hgbdd
  rw [orderAtInfty_eq_analyticOrderAt_div (f := f * g) hh (hfper.mul hgper) (hfhol.mul hghol)
      (hfbdd.mul hgbdd), cuspFunction_mul hf.continuousAt hg.continuousAt,
    analyticOrderAt_mul hf hg, orderAtInfty_eq_analyticOrderAt_div hh hfper hfhol hfbdd,
    orderAtInfty_eq_analyticOrderAt_div hh hgper hghol hgbdd, ENat.toENNReal_add,
    EReal.coe_ennreal_add, EReal.add_div_of_nonneg_right (EReal.coe_nonneg.mpr hh.le)]

/-!
## Relation to the `q`-expansion
-/
/-- The order at infinity is the order of the `q`-expansion divided by the period. -/
lemma orderAtInfty_eq_qExpansion_order (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h)
    (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) :
    orderAtInfty f = (qExpansion h f).order / h := by
  suffices horder : analyticOrderAt (cuspFunction h f) 0 = (qExpansion h f).order by
    rw [orderAtInfty_eq_analyticOrderAt_div hh hfper hfhol hfbdd, horder]
  apply ENat.eq_of_forall_natCast_le_iff
  intro n
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
    (analyticAt_cuspFunction_zero hh hfper hfhol hfbdd)]
  -- Both orders are characterized by the vanishing of all coefficients below `n`.
  constructor
  · exact fun hn ↦ (qExpansion h f).nat_le_order n fun i hi ↦ by simp [qExpansion_coeff, hn i hi]
  · intro hn i hi
    have hcoeff : (qExpansion h f).coeff i = 0 :=
      (qExpansion h f).coeff_of_lt_order i ((ENat.natCast_lt_natCast.mpr hi).trans_le hn)
    simpa [qExpansion_coeff, Nat.factorial_ne_zero] using hcoeff

end Complex

end UpperHalfPlane

end
