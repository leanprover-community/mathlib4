/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Asymptotics.SuperpolynomialDecay
public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Order.BoundedOrder.Lattice
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Disjoint
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Filter.AtTopBot.Group
import Mathlib.Order.Filter.Map
import Mathlib.Order.Filter.Tendsto
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Closure
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.LeftRightNhds

/-!
# Phragmen-Lindelöf principle

In this file we prove several versions of the Phragmen-Lindelöf principle, a version of the maximum
modulus principle for an unbounded domain.

## Main statements

* `PhragmenLindelof.horizontal_strip`: the Phragmen-Lindelöf principle in a horizontal strip
  `{z : ℂ | a < complex.im z < b}`;

* `PhragmenLindelof.eq_zero_on_horizontal_strip`, `PhragmenLindelof.eqOn_horizontal_strip`:
  extensionality lemmas based on the Phragmen-Lindelöf principle in a horizontal strip;

* `PhragmenLindelof.vertical_strip`: the Phragmen-Lindelöf principle in a vertical strip
  `{z : ℂ | a < complex.re z < b}`;

* `PhragmenLindelof.eq_zero_on_vertical_strip`, `PhragmenLindelof.eqOn_vertical_strip`:
  extensionality lemmas based on the Phragmen-Lindelöf principle in a vertical strip;

* `PhragmenLindelof.quadrant_I`, `PhragmenLindelof.quadrant_II`, `PhragmenLindelof.quadrant_III`,
  `PhragmenLindelof.quadrant_IV`: the Phragmen-Lindelöf principle in the coordinate quadrants;

* `PhragmenLindelof.right_half_plane_of_tendsto_zero_on_real`,
  `PhragmenLindelof.right_half_plane_of_bounded_on_real`: two versions of the Phragmen-Lindelöf
  principle in the right half-plane;

* `PhragmenLindelof.eq_zero_on_right_half_plane_of_superexponential_decay`,
  `PhragmenLindelof.eqOn_right_half_plane_of_superexponential_decay`: extensionality lemmas based
  on the Phragmen-Lindelöf principle in the right half-plane.

In the case of the right half-plane, we prove a version of the Phragmen-Lindelöf principle that is
useful for Ilyashenko's proof of the individual finiteness theorem (a polynomial vector field on the
real plane has only finitely many limit cycles).
-/

public section

open Set Function Filter Asymptotics Metric Complex Bornology
open scoped Topology Filter Real

local notation "expR" => Real.exp

namespace PhragmenLindelof

/-!
### Auxiliary lemmas
-/


variable {E : Type*} [NormedAddCommGroup E]

/-- An auxiliary lemma that combines two double exponential estimates into a similar estimate
on the difference of the functions. -/
theorem isBigO_sub_exp_exp {a : ℝ} {f g : ℂ → E} {l : Filter ℂ} {u : ℂ → ℝ}
    (hBf : ∃ c < a, ∃ B, f =O[l] fun z => expR (B * expR (c * |u z|)))
    (hBg : ∃ c < a, ∃ B, g =O[l] fun z => expR (B * expR (c * |u z|))) :
    ∃ c < a, ∃ B, (f - g) =O[l] fun z => expR (B * expR (c * |u z|)) := by
  have : ∀ {c₁ c₂ B₁ B₂}, c₁ ≤ c₂ → 0 ≤ B₂ → B₁ ≤ B₂ → ∀ z,
      ‖expR (B₁ * expR (c₁ * |u z|))‖ ≤ ‖expR (B₂ * expR (c₂ * |u z|))‖ := fun hc hB₀ hB z ↦ by
    simp only [Real.norm_eq_abs, Real.abs_exp]; gcongr
  rcases hBf with ⟨cf, hcf, Bf, hOf⟩; rcases hBg with ⟨cg, hcg, Bg, hOg⟩
  refine ⟨max cf cg, max_lt hcf hcg, max 0 (max Bf Bg), ?_⟩
  refine (hOf.trans_le <| this ?_ ?_ ?_).sub (hOg.trans_le <| this ?_ ?_ ?_)
  exacts [le_max_left _ _, le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
    le_max_right _ _, le_max_left _ _, (le_max_right _ _).trans (le_max_right _ _)]

/-- An auxiliary lemma that combines two “exponential of a power” estimates into a similar estimate
on the difference of the functions. -/
theorem isBigO_sub_exp_rpow {a : ℝ} {f g : ℂ → E} {l : Filter ℂ}
    (hBf : ∃ c < a, ∃ B, f =O[cobounded ℂ ⊓ l] fun z => expR (B * ‖z‖ ^ c))
    (hBg : ∃ c < a, ∃ B, g =O[cobounded ℂ ⊓ l] fun z => expR (B * ‖z‖ ^ c)) :
    ∃ c < a, ∃ B, (f - g) =O[cobounded ℂ ⊓ l] fun z => expR (B * ‖z‖ ^ c) := by
  have : ∀ {c₁ c₂ B₁ B₂ : ℝ}, c₁ ≤ c₂ → 0 ≤ B₂ → B₁ ≤ B₂ →
      (fun z : ℂ => expR (B₁ * ‖z‖ ^ c₁)) =O[cobounded ℂ ⊓ l]
        fun z => expR (B₂ * ‖z‖ ^ c₂) := fun hc hB₀ hB ↦ .of_norm_eventuallyLE <| by
    filter_upwards [(eventually_cobounded_le_norm 1).filter_mono inf_le_left] with z hz
    simp only [Real.norm_eq_abs, Real.abs_exp]
    gcongr
  rcases hBf with ⟨cf, hcf, Bf, hOf⟩; rcases hBg with ⟨cg, hcg, Bg, hOg⟩
  refine ⟨max cf cg, max_lt hcf hcg, max 0 (max Bf Bg), ?_⟩
  refine (hOf.trans <| this ?_ ?_ ?_).sub (hOg.trans <| this ?_ ?_ ?_)
  exacts [le_max_left _ _, le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
    le_max_right _ _, le_max_left _ _, (le_max_right _ _).trans (le_max_right _ _)]

variable [NormedSpace ℂ E] {a b C : ℝ} {f g : ℂ → E} {z : ℂ}

/-!
### Phragmen-Lindelöf principle in a horizontal strip
-/

/-- **Phragmen-Lindelöf principle** in a strip `U = {z : ℂ | a < im z < b}`.
Let `f : ℂ → E` be a function such that

* `f` is differentiable on `U` and is continuous on its closure;
* `‖f z‖` is bounded from above by `A * exp(B * exp(c * |re z|))` on `U` for some `c < π / (b - a)`;
* `‖f z‖` is bounded from above by a constant `C` on the boundary of `U`.

Then `‖f z‖` is bounded by the same constant on the closed strip
`{z : ℂ | a ≤ im z ≤ b}`. Moreover, it suffices to verify the second assumption
only for sufficiently large values of `|re z|`.
-/
theorem horizontal_strip (hfd : DiffContOnCl ℂ f (im ⁻¹' Ioo a b))
    (hB : ∃ c < π / (b - a), ∃ B, f =O[comap (_root_.abs ∘ re) atTop ⊓ 𝓟 (im ⁻¹' Ioo a b)]
      fun z ↦ expR (B * expR (c * |z.re|)))
    (hle_a : ∀ z : ℂ, im z = a → ‖f z‖ ≤ C) (hle_b : ∀ z, im z = b → ‖f z‖ ≤ C) (hza : a ≤ im z)
    (hzb : im z ≤ b) : ‖f z‖ ≤ C := by
  -- If `im z = a` or `im z = b`, then we apply `hle_a` or `hle_b`, otherwise `im z ∈ Ioo a b`.
  rw [le_iff_eq_or_lt] at hza hzb
  rcases hza with hza | hza; · exact hle_a _ hza.symm
  rcases hzb with hzb | hzb; · exact hle_b _ hzb
  wlog hC₀ : 0 < C generalizing C
  · refine le_of_forall_gt_imp_ge_of_dense fun C' hC' => this (fun w hw => ?_) (fun w hw => ?_) ?_
    · exact (hle_a _ hw).trans hC'.le
    · exact (hle_b _ hw).trans hC'.le
    · refine ((norm_nonneg (f (a * I))).trans (hle_a _ ?_)).trans_lt hC'
      rw [mul_I_im, ofReal_re]
  -- After a change of variables, we deal with the strip `a - b < im z < a + b` instead
  -- of `a < im z < b`
  obtain ⟨a, b, rfl, rfl⟩ : ∃ a' b', a = a' - b' ∧ b = a' + b' :=
    ⟨(a + b) / 2, (b - a) / 2, by ring, by ring⟩
  have hab : a - b < a + b := hza.trans hzb
  have hb : 0 < b := by simpa only [sub_eq_add_neg, add_lt_add_iff_left, neg_lt_self_iff] using hab
  rw [add_sub_sub_cancel, ← two_mul, div_mul_eq_div_div] at hB
  have hπb : 0 < π / 2 / b := div_pos Real.pi_div_two_pos hb
  -- Choose some `c B : ℝ` satisfying `hB`, then choose `max c 0 < d < π / 2 / b`.
  rcases hB with ⟨c, hc, B, hO⟩
  obtain ⟨d, ⟨hcd, hd₀⟩, hd⟩ : ∃ d, (c < d ∧ 0 < d) ∧ d < π / 2 / b := by
    simpa only [max_lt_iff] using exists_between (max_lt hc hπb)
  have hb' : d * b < π / 2 := (lt_div_iff₀ hb).1 hd
  set aff := (fun w => d * (w - a * I) : ℂ → ℂ)
  set g := fun (ε : ℝ) (w : ℂ) => exp (ε * (exp (aff w) + exp (-aff w)))
  /- Since `g ε z → 1` as `ε → 0⁻`, it suffices to prove that `‖g ε z • f z‖ ≤ C`
    for all negative `ε`. -/
  suffices ∀ᶠ ε : ℝ in 𝓝[<] (0 : ℝ), ‖g ε z • f z‖ ≤ C by
    refine le_of_tendsto (Tendsto.mono_left ?_ nhdsWithin_le_nhds) this
    apply ((continuous_ofReal.mul continuous_const).cexp.smul continuous_const).norm.tendsto'
    simp
  filter_upwards [self_mem_nhdsWithin] with ε ε₀; change ε < 0 at ε₀
  -- An upper estimate on `‖g ε w‖` that will be used in two branches of the proof.
  obtain ⟨δ, δ₀, hδ⟩ :
    ∃ δ : ℝ,
      δ < 0 ∧ ∀ ⦃w⦄, im w ∈ Icc (a - b) (a + b) → ‖g ε w‖ ≤ expR (δ * expR (d * |re w|)) := by
    refine
      ⟨ε * Real.cos (d * b),
        mul_neg_of_neg_of_pos ε₀
          (Real.cos_pos_of_mem_Ioo <| abs_lt.1 <| (abs_of_pos (mul_pos hd₀ hb)).symm ▸ hb'),
        fun w hw => ?_⟩
    replace hw : |im (aff w)| ≤ d * b := by
      rw [← Real.closedBall_eq_Icc, mem_closedBall, Real.dist_eq] at hw
      rw [im_ofReal_mul, sub_im, mul_I_im, ofReal_re, _root_.abs_mul, abs_of_pos hd₀]
      gcongr
    simpa only [aff, re_ofReal_mul, _root_.abs_mul, abs_of_pos hd₀, sub_re, mul_I_re, ofReal_im,
      zero_mul, neg_zero, sub_zero] using
      norm_exp_mul_exp_add_exp_neg_le_of_abs_im_le ε₀.le hw hb'.le
  -- `abs (g ε w) ≤ 1` on the lines `w.im = a ± b` (actually, it holds everywhere in the strip)
  have hg₁ : ∀ w, im w = a - b ∨ im w = a + b → ‖g ε w‖ ≤ 1 := by
    refine fun w hw => (hδ <| hw.by_cases ?_ ?_).trans (Real.exp_le_one_iff.2 ?_)
    exacts [fun h => h.symm ▸ left_mem_Icc.2 hab.le, fun h => h.symm ▸ right_mem_Icc.2 hab.le,
      mul_nonpos_of_nonpos_of_nonneg δ₀.le (Real.exp_pos _).le]
  /- Our a priori estimate on `f` implies that `g ε w • f w → 0` as `|w.re| → ∞` along the strip. In
    particular, its norm is less than or equal to `C` for sufficiently large `|w.re|`. -/
  obtain ⟨R, hzR, hR⟩ :
    ∃ R : ℝ, |z.re| < R ∧ ∀ w, |re w| = R → im w ∈ Ioo (a - b) (a + b) → ‖g ε w • f w‖ ≤ C := by
    refine ((eventually_gt_atTop _).and ?_).exists
    rcases hO.exists_pos with ⟨A, hA₀, hA⟩
    simp only [isBigOWith_iff, eventually_inf_principal, eventually_comap, mem_Ioo,
      mem_preimage, (· ∘ ·), Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hA
    suffices
        Tendsto (fun R => expR (δ * expR (d * R) + B * expR (c * R) + Real.log A)) atTop (𝓝 0) by
      filter_upwards [this.eventually (ge_mem_nhds hC₀), hA] with R hR Hle w hre him
      calc
        ‖g ε w • f w‖ ≤ expR (δ * expR (d * R) + B * expR (c * R) + Real.log A) := ?_
        _ ≤ C := hR
      rw [norm_smul, Real.exp_add, ← hre, Real.exp_add, Real.exp_log hA₀, mul_assoc, mul_comm _ A]
      gcongr
      exacts [hδ <| Ioo_subset_Icc_self him, Hle _ hre him]
    refine Real.tendsto_exp_atBot.comp ?_
    suffices H : Tendsto (fun R => δ + B * (expR ((d - c) * R))⁻¹) atTop (𝓝 (δ + B * 0)) by
      rw [mul_zero, add_zero] at H
      refine Tendsto.atBot_add ?_ tendsto_const_nhds
      simpa only [id, (· ∘ ·), add_mul, mul_assoc, ← div_eq_inv_mul, ← Real.exp_sub, ← sub_mul,
        sub_sub_cancel]
        using H.neg_mul_atTop δ₀ <| Real.tendsto_exp_atTop.comp <| tendsto_id.const_mul_atTop hd₀
    refine tendsto_const_nhds.add (tendsto_const_nhds.mul ?_)
    exact tendsto_inv_atTop_zero.comp <| Real.tendsto_exp_atTop.comp <|
      tendsto_id.const_mul_atTop (sub_pos.2 hcd)
  have hR₀ : 0 < R := (_root_.abs_nonneg _).trans_lt hzR
  /- Finally, we apply the bounded version of the maximum modulus principle to the rectangle
    `(-R, R) × (a - b, a + b)`. The function is bounded by `C` on the horizontal sides by assumption
    (and because `‖g ε w‖ ≤ 1`) and on the vertical sides by the choice of `R`. -/
  have hgd : Differentiable ℂ (g ε) :=
    ((((differentiable_id.sub_const _).const_mul _).cexp.add
            ((differentiable_id.sub_const _).const_mul _).neg.cexp).const_mul _).cexp
  replace hd : DiffContOnCl ℂ (fun w => g ε w • f w) (Ioo (-R) R ×ℂ Ioo (a - b) (a + b)) :=
    (hgd.diffContOnCl.smul hfd).mono inter_subset_right
  convert norm_le_of_forall_mem_frontier_norm_le ((isBounded_Ioo _ _).reProdIm (isBounded_Ioo _ _))
    hd (fun w hw => _) _
  · rw [frontier_reProdIm, closure_Ioo (neg_lt_self hR₀).ne, frontier_Ioo hab, closure_Ioo hab.ne,
      frontier_Ioo (neg_lt_self hR₀)] at hw
    by_cases him : w.im = a - b ∨ w.im = a + b
    · rw [norm_smul, ← one_mul C]
      gcongr
      exacts [hg₁ _ him, him.by_cases (hle_a _) (hle_b _)]
    · replace hw : w ∈ {-R, R} ×ℂ Icc (a - b) (a + b) := hw.resolve_left fun h ↦ him h.2
      have hw' := eq_endpoints_or_mem_Ioo_of_mem_Icc hw.2; rw [← or_assoc] at hw'
      exact hR _ ((abs_eq hR₀.le).2 hw.1.symm) (hw'.resolve_left him)
  · rw [closure_reProdIm, closure_Ioo hab.ne, closure_Ioo (neg_lt_self hR₀).ne]
    exact ⟨abs_le.1 hzR.le, ⟨hza.le, hzb.le⟩⟩

/-- **Phragmen-Lindelöf principle** in a strip `U = {z : ℂ | a < im z < b}`.
Let `f : ℂ → E` be a function such that

* `f` is differentiable on `U` and is continuous on its closure;
* `‖f z‖` is bounded from above by `A * exp(B * exp(c * |re z|))` on `U` for some `c < π / (b - a)`;
* `f z = 0` on the boundary of `U`.

Then `f` is equal to zero on the closed strip `{z : ℂ | a ≤ im z ≤ b}`.
-/
theorem eq_zero_on_horizontal_strip (hd : DiffContOnCl ℂ f (im ⁻¹' Ioo a b))
    (hB : ∃ c < π / (b - a), ∃ B, f =O[comap (_root_.abs ∘ re) atTop ⊓ 𝓟 (im ⁻¹' Ioo a b)]
      fun z ↦ expR (B * expR (c * |z.re|)))
    (ha : ∀ z : ℂ, z.im = a → f z = 0) (hb : ∀ z : ℂ, z.im = b → f z = 0) :
    EqOn f 0 (im ⁻¹' Icc a b) := fun _z hz =>
  norm_le_zero_iff.1 <| horizontal_strip hd hB (fun z hz => (ha z hz).symm ▸ norm_zero.le)
    (fun z hz => (hb z hz).symm ▸ norm_zero.le) hz.1 hz.2

/-- **Phragmen-Lindelöf principle** in a strip `U = {z : ℂ | a < im z < b}`.
Let `f g : ℂ → E` be functions such that

* `f` and `g` are differentiable on `U` and are continuous on its closure;
* `‖f z‖` and `‖g z‖` are bounded from above by `A * exp(B * exp(c * |re z|))` on `U` for some
  `c < π / (b - a)`;
* `f z = g z` on the boundary of `U`.

Then `f` is equal to `g` on the closed strip `{z : ℂ | a ≤ im z ≤ b}`.
-/
theorem eqOn_horizontal_strip {g : ℂ → E} (hdf : DiffContOnCl ℂ f (im ⁻¹' Ioo a b))
    (hBf : ∃ c < π / (b - a), ∃ B, f =O[comap (_root_.abs ∘ re) atTop ⊓ 𝓟 (im ⁻¹' Ioo a b)]
      fun z ↦ expR (B * expR (c * |z.re|)))
    (hdg : DiffContOnCl ℂ g (im ⁻¹' Ioo a b))
    (hBg : ∃ c < π / (b - a), ∃ B, g =O[comap (_root_.abs ∘ re) atTop ⊓ 𝓟 (im ⁻¹' Ioo a b)]
      fun z ↦ expR (B * expR (c * |z.re|)))
    (ha : ∀ z : ℂ, z.im = a → f z = g z) (hb : ∀ z : ℂ, z.im = b → f z = g z) :
    EqOn f g (im ⁻¹' Icc a b) := fun _z hz =>
  sub_eq_zero.1 (eq_zero_on_horizontal_strip (hdf.sub hdg) (isBigO_sub_exp_exp hBf hBg)
    (fun w hw => sub_eq_zero.2 (ha w hw)) (fun w hw => sub_eq_zero.2 (hb w hw)) hz)

/-!
### Phragmen-Lindelöf principle in a vertical strip
-/

/-- **Phragmen-Lindelöf principle** in a strip `U = {z : ℂ | a < re z < b}`.
Let `f : ℂ → E` be a function such that

* `f` is differentiable on `U` and is continuous on its closure;
* `‖f z‖` is bounded from above by `A * exp(B * exp(c * |im z|))` on `U` for some `c < π / (b - a)`;
* `‖f z‖` is bounded from above by a constant `C` on the boundary of `U`.

Then `‖f z‖` is bounded by the same constant on the closed strip
`{z : ℂ | a ≤ re z ≤ b}`. Moreover, it suffices to verify the second assumption
only for sufficiently large values of `|im z|`.
-/
theorem vertical_strip (hfd : DiffContOnCl ℂ f (re ⁻¹' Ioo a b))
    (hB : ∃ c < π / (b - a), ∃ B, f =O[comap (_root_.abs ∘ im) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b)]
      fun z ↦ expR (B * expR (c * |z.im|)))
    (hle_a : ∀ z : ℂ, re z = a → ‖f z‖ ≤ C) (hle_b : ∀ z, re z = b → ‖f z‖ ≤ C) (hza : a ≤ re z)
    (hzb : re z ≤ b) : ‖f z‖ ≤ C := by
  suffices ‖f (z * I * -I)‖ ≤ C by simpa [mul_assoc] using this
  have H : MapsTo (· * -I) (im ⁻¹' Ioo a b) (re ⁻¹' Ioo a b) := fun z hz ↦ by simpa using hz
  refine horizontal_strip (f := fun z ↦ f (z * -I))
    (hfd.comp (differentiable_id.mul_const _).diffContOnCl H) ?_ (fun z hz => hle_a _ ?_)
    (fun z hz => hle_b _ ?_) ?_ ?_
  · rcases hB with ⟨c, hc, B, hO⟩
    refine ⟨c, hc, B, ?_⟩
    have : Tendsto (· * -I) (comap (|re ·|) atTop ⊓ 𝓟 (im ⁻¹' Ioo a b))
        (comap (|im ·|) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b)) := by
      refine (tendsto_comap_iff.2 ?_).inf H.tendsto
      simpa [Function.comp_def] using tendsto_comap
    simpa [Function.comp_def] using hO.comp_tendsto this
  all_goals simpa

/-- **Phragmen-Lindelöf principle** in a strip `U = {z : ℂ | a < re z < b}`.
Let `f : ℂ → E` be a function such that

* `f` is differentiable on `U` and is continuous on its closure;
* `‖f z‖` is bounded from above by `A * exp(B * exp(c * |im z|))` on `U` for some `c < π / (b - a)`;
* `f z = 0` on the boundary of `U`.

Then `f` is equal to zero on the closed strip `{z : ℂ | a ≤ re z ≤ b}`.
-/
theorem eq_zero_on_vertical_strip (hd : DiffContOnCl ℂ f (re ⁻¹' Ioo a b))
    (hB : ∃ c < π / (b - a), ∃ B, f =O[comap (_root_.abs ∘ im) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b)]
      fun z ↦ expR (B * expR (c * |z.im|)))
    (ha : ∀ z : ℂ, re z = a → f z = 0) (hb : ∀ z : ℂ, re z = b → f z = 0) :
    EqOn f 0 (re ⁻¹' Icc a b) := fun _z hz =>
  norm_le_zero_iff.1 <| vertical_strip hd hB (fun z hz => (ha z hz).symm ▸ norm_zero.le)
    (fun z hz => (hb z hz).symm ▸ norm_zero.le) hz.1 hz.2

/-- **Phragmen-Lindelöf principle** in a strip `U = {z : ℂ | a < re z < b}`.
Let `f g : ℂ → E` be functions such that

* `f` and `g` are differentiable on `U` and are continuous on its closure;
* `‖f z‖` and `‖g z‖` are bounded from above by `A * exp(B * exp(c * |im z|))` on `U` for some
  `c < π / (b - a)`;
* `f z = g z` on the boundary of `U`.

Then `f` is equal to `g` on the closed strip `{z : ℂ | a ≤ re z ≤ b}`.
-/
theorem eqOn_vertical_strip {g : ℂ → E} (hdf : DiffContOnCl ℂ f (re ⁻¹' Ioo a b))
    (hBf : ∃ c < π / (b - a), ∃ B, f =O[comap (_root_.abs ∘ im) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b)]
      fun z ↦ expR (B * expR (c * |z.im|)))
    (hdg : DiffContOnCl ℂ g (re ⁻¹' Ioo a b))
    (hBg : ∃ c < π / (b - a), ∃ B, g =O[comap (_root_.abs ∘ im) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b)]
      fun z ↦ expR (B * expR (c * |z.im|)))
    (ha : ∀ z : ℂ, re z = a → f z = g z) (hb : ∀ z : ℂ, re z = b → f z = g z) :
    EqOn f g (re ⁻¹' Icc a b) := fun _z hz =>
  sub_eq_zero.1 (eq_zero_on_vertical_strip (hdf.sub hdg) (isBigO_sub_exp_exp hBf hBg)
    (fun w hw => sub_eq_zero.2 (ha w hw)) (fun w hw => sub_eq_zero.2 (hb w hw)) hz)

/-!
### Phragmen-Lindelöf principle in coordinate quadrants
-/

/-- **Phragmen-Lindelöf principle** in the first quadrant. Let `f : ℂ → E` be a function such that

* `f` is differentiable in the open first quadrant and is continuous on its closure;
* `‖f z‖` is bounded from above by `A * exp(B * ‖z‖ ^ c)` on the open first quadrant
  for some `c < 2`;
* `‖f z‖` is bounded from above by a constant `C` on the boundary of the first quadrant.

Then `‖f z‖` is bounded from above by the same constant on the closed first quadrant. -/
nonrec theorem quadrant_I (hd : DiffContOnCl ℂ f (Ioi 0 ×ℂ Ioi 0))
    (hB : ∃ c < (2 : ℝ), ∃ B,
      f =O[cobounded ℂ ⊓ 𝓟 (Ioi 0 ×ℂ Ioi 0)] fun z => expR (B * ‖z‖ ^ c))
    (hre : ∀ x : ℝ, 0 ≤ x → ‖f x‖ ≤ C) (him : ∀ x : ℝ, 0 ≤ x → ‖f (x * I)‖ ≤ C) (hz_re : 0 ≤ z.re)
    (hz_im : 0 ≤ z.im) : ‖f z‖ ≤ C := by
  -- The case `z = 0` is trivial.
  rcases eq_or_ne z 0 with (rfl | hzne)
  · exact hre 0 le_rfl
  -- Otherwise, `z = e ^ ζ` for some `ζ : ℂ`, `0 < Im ζ < π / 2`.
  obtain ⟨ζ, hζ, rfl⟩ : ∃ ζ : ℂ, ζ.im ∈ Icc 0 (π / 2) ∧ exp ζ = z := by
    refine ⟨log z, ?_, exp_log hzne⟩
    rw [log_im]
    exact ⟨arg_nonneg_iff.2 hz_im, arg_le_pi_div_two_iff.2 (Or.inl hz_re)⟩
  -- We are going to apply `PhragmenLindelof.horizontal_strip` to `f ∘ Complex.exp` and `ζ`.
  change ‖(f ∘ exp) ζ‖ ≤ C
  have H : MapsTo exp (im ⁻¹' Ioo 0 (π / 2)) (Ioi 0 ×ℂ Ioi 0) := fun z hz ↦ by
    rw [mem_reProdIm, exp_re, exp_im, mem_Ioi, mem_Ioi]
    have : 0 < Real.cos z.im := Real.cos_pos_of_mem_Ioo ⟨by linarith [hz.1, hz.2], hz.2⟩
    have : 0 < Real.sin z.im :=
      Real.sin_pos_of_mem_Ioo ⟨hz.1, hz.2.trans (half_lt_self Real.pi_pos)⟩
    constructor <;> positivity
  refine horizontal_strip (hd.comp differentiable_exp.diffContOnCl H) ?_ ?_ ?_ hζ.1 hζ.2
  · -- The estimate `hB` on `f` implies the required estimate on
    -- `f ∘ exp` with the same `c` and `B' = max B 0`.
    rw [sub_zero, div_div_cancel₀ Real.pi_pos.ne']
    rcases hB with ⟨c, hc, B, hO⟩
    refine ⟨c, hc, max B 0, ?_⟩
    rw [← comap_comap, comap_abs_atTop, comap_sup, inf_sup_right]
    -- We prove separately the estimates as `ζ.re → ∞` and as `ζ.re → -∞`
    refine IsBigO.sup ?_ <| (hO.comp_tendsto <| tendsto_exp_comap_re_atTop.inf H.tendsto).trans <|
      .of_norm_eventuallyLE ?_
    · -- For the estimate as `ζ.re → -∞`, note that `f` is continuous within the first quadrant at
      -- zero, hence `f (exp ζ)` has a limit as `ζ.re → -∞`, `0 < ζ.im < π / 2`.
      have hc : ContinuousWithinAt f (Ioi 0 ×ℂ Ioi 0) 0 := by
        refine (hd.continuousOn _ ?_).mono subset_closure
        simp [closure_reProdIm, mem_reProdIm]
      refine ((hc.tendsto.comp <| tendsto_exp_comap_re_atBot.inf H.tendsto).isBigO_one ℝ).trans
        (isBigO_of_le _ fun w => ?_)
      rw [norm_one, Real.norm_of_nonneg (Real.exp_pos _).le, Real.one_le_exp_iff]
      positivity
    · -- For the estimate as `ζ.re → ∞`, we reuse the upper estimate on `f`
      simp only [EventuallyLE, eventually_inf_principal, eventually_comap, comp_apply,
        Real.norm_of_nonneg (Real.exp_pos _).le, norm_exp, ← Real.exp_mul, Real.exp_le_exp]
      filter_upwards [eventually_ge_atTop 0] with x hx z hz _
      rw [hz, abs_of_nonneg hx, mul_comm _ c]
      gcongr; apply le_max_left
  · -- If `ζ.im = 0`, then `Complex.exp ζ` is a positive real number
    intro ζ hζ; lift ζ to ℝ using hζ
    rw [comp_apply, ← ofReal_exp]
    exact hre _ (Real.exp_pos _).le
  · -- If `ζ.im = π / 2`, then `Complex.exp ζ` is a purely imaginary number with positive `im`
    intro ζ hζ
    rw [← re_add_im ζ, hζ, comp_apply, exp_add_mul_I, ← ofReal_cos, ← ofReal_sin,
      Real.cos_pi_div_two, Real.sin_pi_div_two, ofReal_zero, ofReal_one, one_mul, zero_add, ←
      ofReal_exp]
    exact him _ (Real.exp_pos _).le

/-- **Phragmen-Lindelöf principle** in the first quadrant. Let `f : ℂ → E` be a function such that

* `f` is differentiable in the open first quadrant and is continuous on its closure;
* `‖f z‖` is bounded from above by `A * exp(B * ‖z‖ ^ c)` on the open first quadrant
  for some `A`, `B`, and `c < 2`;
* `f` is equal to zero on the boundary of the first quadrant.

Then `f` is equal to zero on the closed first quadrant. -/
theorem eq_zero_on_quadrant_I (hd : DiffContOnCl ℂ f (Ioi 0 ×ℂ Ioi 0))
    (hB : ∃ c < (2 : ℝ), ∃ B,
      f =O[cobounded ℂ ⊓ 𝓟 (Ioi 0 ×ℂ Ioi 0)] fun z => expR (B * ‖z‖ ^ c))
    (hre : ∀ x : ℝ, 0 ≤ x → f x = 0) (him : ∀ x : ℝ, 0 ≤ x → f (x * I) = 0) :
    EqOn f 0 {z | 0 ≤ z.re ∧ 0 ≤ z.im} := fun _z hz =>
  norm_le_zero_iff.1 <|
    quadrant_I hd hB (fun x hx => norm_le_zero_iff.2 <| hre x hx)
      (fun x hx => norm_le_zero_iff.2 <| him x hx) hz.1 hz.2

/-- **Phragmen-Lindelöf principle** in the first quadrant. Let `f g : ℂ → E` be functions such that

* `f` and `g` are differentiable in the open first quadrant and are continuous on its closure;
* `‖f z‖` and `‖g z‖` are bounded from above by `A * exp(B * ‖z‖ ^ c)` on the open first
  quadrant for some `A`, `B`, and `c < 2`;
* `f` is equal to `g` on the boundary of the first quadrant.

Then `f` is equal to `g` on the closed first quadrant. -/
theorem eqOn_quadrant_I (hdf : DiffContOnCl ℂ f (Ioi 0 ×ℂ Ioi 0))
    (hBf : ∃ c < (2 : ℝ), ∃ B,
      f =O[cobounded ℂ ⊓ 𝓟 (Ioi 0 ×ℂ Ioi 0)] fun z => expR (B * ‖z‖ ^ c))
    (hdg : DiffContOnCl ℂ g (Ioi 0 ×ℂ Ioi 0))
    (hBg : ∃ c < (2 : ℝ), ∃ B,
      g =O[cobounded ℂ ⊓ 𝓟 (Ioi 0 ×ℂ Ioi 0)] fun z => expR (B * ‖z‖ ^ c))
    (hre : ∀ x : ℝ, 0 ≤ x → f x = g x) (him : ∀ x : ℝ, 0 ≤ x → f (x * I) = g (x * I)) :
    EqOn f g {z | 0 ≤ z.re ∧ 0 ≤ z.im} := fun _z hz =>
  sub_eq_zero.1 <|
    eq_zero_on_quadrant_I (hdf.sub hdg) (isBigO_sub_exp_rpow hBf hBg)
      (fun x hx => sub_eq_zero.2 <| hre x hx) (fun x hx => sub_eq_zero.2 <| him x hx) hz

/-- **Phragmen-Lindelöf principle** in the second quadrant. Let `f : ℂ → E` be a function such that

* `f` is differentiable in the open second quadrant and is continuous on its closure;
* `‖f z‖` is bounded from above by `A * exp(B * ‖z‖ ^ c)` on the open second quadrant
  for some `c < 2`;
* `‖f z‖` is bounded from above by a constant `C` on the boundary of the second quadrant.

Then `‖f z‖` is bounded from above by the same constant on the closed second quadrant. -/
theorem quadrant_II (hd : DiffContOnCl ℂ f (Iio 0 ×ℂ Ioi 0))
    (hB : ∃ c < (2 : ℝ), ∃ B,
      f =O[cobounded ℂ ⊓ 𝓟 (Iio 0 ×ℂ Ioi 0)] fun z => expR (B * ‖z‖ ^ c))
    (hre : ∀ x : ℝ, x ≤ 0 → ‖f x‖ ≤ C) (him : ∀ x : ℝ, 0 ≤ x → ‖f (x * I)‖ ≤ C) (hz_re : z.re ≤ 0)
    (hz_im : 0 ≤ z.im) : ‖f z‖ ≤ C := by
  obtain ⟨z, rfl⟩ : ∃ z', z' * I = z := ⟨z / I, div_mul_cancel₀ _ I_ne_zero⟩
  simp only [mul_I_re, mul_I_im, neg_nonpos] at hz_re hz_im
  change ‖(f ∘ (· * I)) z‖ ≤ C
  have H : MapsTo (· * I) (Ioi 0 ×ℂ Ioi 0) (Iio 0 ×ℂ Ioi 0) := fun w hw ↦ by
    simpa only [mem_reProdIm, mul_I_re, mul_I_im, neg_lt_zero, mem_Iio] using hw.symm
  rcases hB with ⟨c, hc, B, hO⟩
  refine quadrant_I (hd.comp (differentiable_id.mul_const _).diffContOnCl H) ⟨c, hc, B, ?_⟩ him
    (fun x hx => ?_) hz_im hz_re
  · simpa only [Function.comp_def, norm_mul, norm_I, mul_one]
      using hO.comp_tendsto ((tendsto_mul_right_cobounded I_ne_zero).inf H.tendsto)
  · rw [comp_apply, mul_assoc, I_mul_I, mul_neg_one, ← ofReal_neg]
    exact hre _ (neg_nonpos.2 hx)

/-- **Phragmen-Lindelöf principle** in the second quadrant. Let `f : ℂ → E` be a function such that

* `f` is differentiable in the open second quadrant and is continuous on its closure;
* `‖f z‖` is bounded from above by `A * exp(B * ‖z‖ ^ c)` on the open second quadrant
  for some `A`, `B`, and `c < 2`;
* `f` is equal to zero on the boundary of the second quadrant.

Then `f` is equal to zero on the closed second quadrant. -/
theorem eq_zero_on_quadrant_II (hd : DiffContOnCl ℂ f (Iio 0 ×ℂ Ioi 0))
    (hB : ∃ c < (2 : ℝ), ∃ B,
      f =O[cobounded ℂ ⊓ 𝓟 (Iio 0 ×ℂ Ioi 0)] fun z => expR (B * ‖z‖ ^ c))
    (hre : ∀ x : ℝ, x ≤ 0 → f x = 0) (him : ∀ x : ℝ, 0 ≤ x → f (x * I) = 0) :
    EqOn f 0 {z | z.re ≤ 0 ∧ 0 ≤ z.im} := fun _z hz =>
  norm_le_zero_iff.1 <|
    quadrant_II hd hB (fun x hx => norm_le_zero_iff.2 <| hre x hx)
      (fun x hx => norm_le_zero_iff.2 <| him x hx) hz.1 hz.2

/-- **Phragmen-Lindelöf principle** in the second quadrant. Let `f g : ℂ → E` be functions such that

* `f` and `g` are differentiable in the open second quadrant and are continuous on its closure;
* `‖f z‖` and `‖g z‖` are bounded from above by `A * exp(B * ‖z‖ ^ c)` on the open second
  quadrant for some `A`, `B`, and `c < 2`;
* `f` is equal to `g` on the boundary of the second quadrant.

Then `f` is equal to `g` on the closed second quadrant. -/
theorem eqOn_quadrant_II (hdf : DiffContOnCl ℂ f (Iio 0 ×ℂ Ioi 0))
    (hBf : ∃ c < (2 : ℝ), ∃ B,
      f =O[cobounded ℂ ⊓ 𝓟 (Iio 0 ×ℂ Ioi 0)] fun z => expR (B * ‖z‖ ^ c))
    (hdg : DiffContOnCl ℂ g (Iio 0 ×ℂ Ioi 0))
    (hBg : ∃ c < (2 : ℝ), ∃ B,
      g =O[cobounded ℂ ⊓ 𝓟 (Iio 0 ×ℂ Ioi 0)] fun z => expR (B * ‖z‖ ^ c))
    (hre : ∀ x : ℝ, x ≤ 0 → f x = g x) (him : ∀ x : ℝ, 0 ≤ x → f (x * I) = g (x * I)) :
    EqOn f g {z | z.re ≤ 0 ∧ 0 ≤ z.im} := fun _z hz =>
  sub_eq_zero.1 <| eq_zero_on_quadrant_II (hdf.sub hdg) (isBigO_sub_exp_rpow hBf hBg)
    (fun x hx => sub_eq_zero.2 <| hre x hx) (fun x hx => sub_eq_zero.2 <| him x hx) hz

/-- **Phragmen-Lindelöf principle** in the third quadrant. Let `f : ℂ → E` be a function such that

* `f` is differentiable in the open third quadrant and is continuous on its closure;
* `‖f z‖` is bounded from above by `A * exp (B * ‖z‖ ^ c)` on the open third quadrant
  for some `c < 2`;
* `‖f z‖` is bounded from above by a constant `C` on the boundary of the third quadrant.

Then `‖f z‖` is bounded from above by the same constant on the closed third quadrant. -/
theorem quadrant_III (hd : DiffContOnCl ℂ f (Iio 0 ×ℂ Iio 0))
    (hB : ∃ c < (2 : ℝ), ∃ B,
      f =O[cobounded ℂ ⊓ 𝓟 (Iio 0 ×ℂ Iio 0)] fun z => expR (B * ‖z‖ ^ c))
    (hre : ∀ x : ℝ, x ≤ 0 → ‖f x‖ ≤ C) (him : ∀ x : ℝ, x ≤ 0 → ‖f (x * I)‖ ≤ C) (hz_re : z.re ≤ 0)
    (hz_im : z.im ≤ 0) : ‖f z‖ ≤ C := by
  obtain ⟨z, rfl⟩ : ∃ z', -z' = z := ⟨-z, neg_neg z⟩
  simp only [neg_re, neg_im, neg_nonpos] at hz_re hz_im
  change ‖(f ∘ Neg.neg) z‖ ≤ C
  have H : MapsTo Neg.neg (Ioi 0 ×ℂ Ioi 0) (Iio 0 ×ℂ Iio 0) := by
    intro w hw
    simpa only [mem_reProdIm, neg_re, neg_im, neg_lt_zero, mem_Iio] using hw
  refine
    quadrant_I (hd.comp differentiable_neg.diffContOnCl H) ?_ (fun x hx => ?_) (fun x hx => ?_)
      hz_re hz_im
  · rcases hB with ⟨c, hc, B, hO⟩
    refine ⟨c, hc, B, ?_⟩
    simpa only [Function.comp_def, norm_neg]
      using hO.comp_tendsto (Filter.tendsto_neg_cobounded.inf H.tendsto)
  · rw [comp_apply, ← ofReal_neg]
    exact hre (-x) (neg_nonpos.2 hx)
  · rw [comp_apply, ← neg_mul, ← ofReal_neg]
    exact him (-x) (neg_nonpos.2 hx)

/-- **Phragmen-Lindelöf principle** in the third quadrant. Let `f : ℂ → E` be a function such that

* `f` is differentiable in the open third quadrant and is continuous on its closure;
* `‖f z‖` is bounded from above by `A * exp(B * ‖z‖ ^ c)` on the open third quadrant
  for some `A`, `B`, and `c < 2`;
* `f` is equal to zero on the boundary of the third quadrant.

Then `f` is equal to zero on the closed third quadrant. -/
theorem eq_zero_on_quadrant_III (hd : DiffContOnCl ℂ f (Iio 0 ×ℂ Iio 0))
    (hB : ∃ c < (2 : ℝ), ∃ B,
      f =O[cobounded ℂ ⊓ 𝓟 (Iio 0 ×ℂ Iio 0)] fun z => expR (B * ‖z‖ ^ c))
    (hre : ∀ x : ℝ, x ≤ 0 → f x = 0) (him : ∀ x : ℝ, x ≤ 0 → f (x * I) = 0) :
    EqOn f 0 {z | z.re ≤ 0 ∧ z.im ≤ 0} := fun _z hz =>
  norm_le_zero_iff.1 <| quadrant_III hd hB (fun x hx => norm_le_zero_iff.2 <| hre x hx)
    (fun x hx => norm_le_zero_iff.2 <| him x hx) hz.1 hz.2

/-- **Phragmen-Lindelöf principle** in the third quadrant. Let `f g : ℂ → E` be functions such that

* `f` and `g` are differentiable in the open third quadrant and are continuous on its closure;
* `‖f z‖` and `‖g z‖` are bounded from above by `A * exp(B * ‖z‖ ^ c)` on the open third
  quadrant for some `A`, `B`, and `c < 2`;
* `f` is equal to `g` on the boundary of the third quadrant.

Then `f` is equal to `g` on the closed third quadrant. -/
theorem eqOn_quadrant_III (hdf : DiffContOnCl ℂ f (Iio 0 ×ℂ Iio 0))
    (hBf : ∃ c < (2 : ℝ), ∃ B,
      f =O[cobounded ℂ ⊓ 𝓟 (Iio 0 ×ℂ Iio 0)] fun z => expR (B * ‖z‖ ^ c))
    (hdg : DiffContOnCl ℂ g (Iio 0 ×ℂ Iio 0))
    (hBg : ∃ c < (2 : ℝ), ∃ B,
      g =O[cobounded ℂ ⊓ 𝓟 (Iio 0 ×ℂ Iio 0)] fun z => expR (B * ‖z‖ ^ c))
    (hre : ∀ x : ℝ, x ≤ 0 → f x = g x) (him : ∀ x : ℝ, x ≤ 0 → f (x * I) = g (x * I)) :
    EqOn f g {z | z.re ≤ 0 ∧ z.im ≤ 0} := fun _z hz =>
  sub_eq_zero.1 <| eq_zero_on_quadrant_III (hdf.sub hdg) (isBigO_sub_exp_rpow hBf hBg)
    (fun x hx => sub_eq_zero.2 <| hre x hx) (fun x hx => sub_eq_zero.2 <| him x hx) hz

/-- **Phragmen-Lindelöf principle** in the fourth quadrant. Let `f : ℂ → E` be a function such that

* `f` is differentiable in the open fourth quadrant and is continuous on its closure;
* `‖f z‖` is bounded from above by `A * exp(B * ‖z‖ ^ c)` on the open fourth quadrant
  for some `c < 2`;
* `‖f z‖` is bounded from above by a constant `C` on the boundary of the fourth quadrant.

Then `‖f z‖` is bounded from above by the same constant on the closed fourth quadrant. -/
theorem quadrant_IV (hd : DiffContOnCl ℂ f (Ioi 0 ×ℂ Iio 0))
    (hB : ∃ c < (2 : ℝ), ∃ B,
      f =O[cobounded ℂ ⊓ 𝓟 (Ioi 0 ×ℂ Iio 0)] fun z => expR (B * ‖z‖ ^ c))
    (hre : ∀ x : ℝ, 0 ≤ x → ‖f x‖ ≤ C) (him : ∀ x : ℝ, x ≤ 0 → ‖f (x * I)‖ ≤ C) (hz_re : 0 ≤ z.re)
    (hz_im : z.im ≤ 0) : ‖f z‖ ≤ C := by
  obtain ⟨z, rfl⟩ : ∃ z', -z' = z := ⟨-z, neg_neg z⟩
  simp only [neg_re, neg_im, neg_nonpos, neg_nonneg] at hz_re hz_im
  change ‖(f ∘ Neg.neg) z‖ ≤ C
  have H : MapsTo Neg.neg (Iio 0 ×ℂ Ioi 0) (Ioi 0 ×ℂ Iio 0) := fun w hw ↦ by
    simpa only [mem_reProdIm, neg_re, neg_im, neg_lt_zero, neg_pos, mem_Ioi, mem_Iio] using hw
  refine quadrant_II
    (hd.comp differentiable_neg.diffContOnCl H) ?_ (fun x hx => ?_) (fun x hx => ?_) hz_re hz_im
  · rcases hB with ⟨c, hc, B, hO⟩
    refine ⟨c, hc, B, ?_⟩
    simpa only [Function.comp_def, norm_neg]
      using hO.comp_tendsto (Filter.tendsto_neg_cobounded.inf H.tendsto)
  · rw [comp_apply, ← ofReal_neg]
    exact hre (-x) (neg_nonneg.2 hx)
  · rw [comp_apply, ← neg_mul, ← ofReal_neg]
    exact him (-x) (neg_nonpos.2 hx)

/-- **Phragmen-Lindelöf principle** in the fourth quadrant. Let `f : ℂ → E` be a function such that

* `f` is differentiable in the open fourth quadrant and is continuous on its closure;
* `‖f z‖` is bounded from above by `A * exp(B * ‖z‖ ^ c)` on the open fourth quadrant
  for some `A`, `B`, and `c < 2`;
* `f` is equal to zero on the boundary of the fourth quadrant.

Then `f` is equal to zero on the closed fourth quadrant. -/
theorem eq_zero_on_quadrant_IV (hd : DiffContOnCl ℂ f (Ioi 0 ×ℂ Iio 0))
    (hB : ∃ c < (2 : ℝ), ∃ B,
      f =O[cobounded ℂ ⊓ 𝓟 (Ioi 0 ×ℂ Iio 0)] fun z => expR (B * ‖z‖ ^ c))
    (hre : ∀ x : ℝ, 0 ≤ x → f x = 0) (him : ∀ x : ℝ, x ≤ 0 → f (x * I) = 0) :
    EqOn f 0 {z | 0 ≤ z.re ∧ z.im ≤ 0} := fun _z hz =>
  norm_le_zero_iff.1 <|
    quadrant_IV hd hB (fun x hx => norm_le_zero_iff.2 <| hre x hx)
      (fun x hx => norm_le_zero_iff.2 <| him x hx) hz.1 hz.2

/-- **Phragmen-Lindelöf principle** in the fourth quadrant. Let `f g : ℂ → E` be functions such that

* `f` and `g` are differentiable in the open fourth quadrant and are continuous on its closure;
* `‖f z‖` and `‖g z‖` are bounded from above by `A * exp(B * ‖z‖ ^ c)` on the open fourth
  quadrant for some `A`, `B`, and `c < 2`;
* `f` is equal to `g` on the boundary of the fourth quadrant.

Then `f` is equal to `g` on the closed fourth quadrant. -/
theorem eqOn_quadrant_IV (hdf : DiffContOnCl ℂ f (Ioi 0 ×ℂ Iio 0))
    (hBf : ∃ c < (2 : ℝ), ∃ B,
      f =O[cobounded ℂ ⊓ 𝓟 (Ioi 0 ×ℂ Iio 0)] fun z => expR (B * ‖z‖ ^ c))
    (hdg : DiffContOnCl ℂ g (Ioi 0 ×ℂ Iio 0))
    (hBg : ∃ c < (2 : ℝ), ∃ B,
      g =O[cobounded ℂ ⊓ 𝓟 (Ioi 0 ×ℂ Iio 0)] fun z => expR (B * ‖z‖ ^ c))
    (hre : ∀ x : ℝ, 0 ≤ x → f x = g x) (him : ∀ x : ℝ, x ≤ 0 → f (x * I) = g (x * I)) :
    EqOn f g {z | 0 ≤ z.re ∧ z.im ≤ 0} := fun _z hz =>
  sub_eq_zero.1 <| eq_zero_on_quadrant_IV (hdf.sub hdg) (isBigO_sub_exp_rpow hBf hBg)
    (fun x hx => sub_eq_zero.2 <| hre x hx) (fun x hx => sub_eq_zero.2 <| him x hx) hz

/-!
### Phragmen-Lindelöf principle in the right half-plane
-/


/-- **Phragmen-Lindelöf principle** in the right half-plane. Let `f : ℂ → E` be a function such that

* `f` is differentiable in the open right half-plane and is continuous on its closure;
* `‖f z‖` is bounded from above by `A * exp(B * ‖z‖ ^ c)` on the open right half-plane
  for some `c < 2`;
* `‖f z‖` is bounded from above by a constant `C` on the imaginary axis;
* `f x → 0` as `x : ℝ` tends to infinity.

Then `‖f z‖` is bounded from above by the same constant on the closed right half-plane.
See also `PhragmenLindelof.right_half_plane_of_bounded_on_real` for a stronger version. -/
theorem right_half_plane_of_tendsto_zero_on_real (hd : DiffContOnCl ℂ f {z | 0 < z.re})
    (hexp : ∃ c < (2 : ℝ), ∃ B,
      f =O[cobounded ℂ ⊓ 𝓟 {z | 0 < z.re}] fun z => expR (B * ‖z‖ ^ c))
    (hre : Tendsto (fun x : ℝ => f x) atTop (𝓝 0)) (him : ∀ x : ℝ, ‖f (x * I)‖ ≤ C)
    (hz : 0 ≤ z.re) : ‖f z‖ ≤ C := by
  /- We are going to apply the Phragmen-Lindelöf principle in the first and fourth quadrants.
    The lemmas immediately imply that for any upper estimate `C'` on `‖f x‖`, `x : ℝ`, `0 ≤ x`,
    the number `max C C'` is an upper estimate on `f` in the whole right half-plane. -/
  revert z
  have hle : ∀ C', (∀ x : ℝ, 0 ≤ x → ‖f x‖ ≤ C') →
      ∀ z : ℂ, 0 ≤ z.re → ‖f z‖ ≤ max C C' := fun C' hC' z hz ↦ by
    rcases hexp with ⟨c, hc, B, hO⟩
    rcases le_total z.im 0 with h | h
    · refine quadrant_IV (hd.mono fun _ => And.left) ⟨c, hc, B, ?_⟩
          (fun x hx => (hC' x hx).trans <| le_max_right _ _)
          (fun x _ => (him x).trans (le_max_left _ _)) hz h
      exact hO.mono (inf_le_inf_left _ <| principal_mono.2 fun _ => And.left)
    · refine quadrant_I (hd.mono fun _ => And.left) ⟨c, hc, B, ?_⟩
          (fun x hx => (hC' x hx).trans <| le_max_right _ _)
          (fun x _ => (him x).trans (le_max_left _ _)) hz h
      exact hO.mono (inf_le_inf_left _ <| principal_mono.2 fun _ => And.left)
  -- Since `f` is continuous on `Ici 0` and `‖f x‖` tends to zero as `x → ∞`,
  -- the norm `‖f x‖` takes its maximum value at some `x₀ : ℝ`.
  obtain ⟨x₀, hx₀, hmax⟩ : ∃ x : ℝ, 0 ≤ x ∧ ∀ y : ℝ, 0 ≤ y → ‖f y‖ ≤ ‖f x‖ := by
    have hfc : ContinuousOn (fun x : ℝ => f x) (Ici 0) := by
      refine hd.continuousOn.comp continuous_ofReal.continuousOn fun x hx => ?_
      rwa [closure_setOf_lt_re]
    by_cases! h₀ : ∀ x : ℝ, 0 ≤ x → f x = 0
    · refine ⟨0, le_rfl, fun y hy => ?_⟩; rw [h₀ y hy, h₀ 0 le_rfl]
    rcases h₀ with ⟨x₀, hx₀, hne⟩
    have hlt : ‖(0 : E)‖ < ‖f x₀‖ := by rwa [norm_zero, norm_pos_iff]
    suffices ∀ᶠ x : ℝ in cocompact ℝ ⊓ 𝓟 (Ici 0), ‖f x‖ ≤ ‖f x₀‖ by
      simpa only [exists_prop] using hfc.norm.exists_isMaxOn' isClosed_Ici hx₀ this
    rw [cocompact_eq_atBot_atTop, inf_sup_right, (disjoint_atBot_principal_Ici (0 : ℝ)).eq_bot,
      bot_sup_eq]
    exact (hre.norm.eventually <| ge_mem_nhds hlt).filter_mono inf_le_left
  rcases le_or_gt ‖f x₀‖ C with h | h
  · -- If `‖f x₀‖ ≤ C`, then `hle` implies the required estimate
    simpa only [max_eq_left h] using hle _ hmax
  · -- Otherwise, `‖f z‖ ≤ ‖f x₀‖` for all `z` in the right half-plane due to `hle`.
    replace hmax : IsMaxOn (norm ∘ f) {z | 0 < z.re} x₀ := by
      rintro z (hz : 0 < z.re)
      simpa [max_eq_right h.le] using hle _ hmax _ hz.le
    -- Due to the maximum modulus principle applied to the closed ball of radius `x₀.re`,
    -- `‖f 0‖ = ‖f x₀‖`.
    have : ‖f 0‖ = ‖f x₀‖ := by
      apply norm_eq_norm_of_isMaxOn_of_ball_subset hd hmax
      -- move to a lemma?
      intro z hz
      rw [mem_ball, dist_zero_left, dist_eq, Complex.norm_of_nonneg hx₀] at hz
      rw [mem_setOf_eq]
      contrapose! hz
      calc
        x₀ ≤ x₀ - z.re := (le_sub_self_iff _).2 hz
        _ ≤ |x₀ - z.re| := le_abs_self _
        _ = |(z - x₀).re| := by rw [sub_re, ofReal_re, _root_.abs_sub_comm]
        _ ≤ ‖z - x₀‖ := abs_re_le_norm _
    -- Thus we have `C < ‖f x₀‖ = ‖f 0‖ ≤ C`. Contradiction completes the proof.
    refine (h.not_ge <| this ▸ ?_).elim
    simpa using him 0

/-- **Phragmen-Lindelöf principle** in the right half-plane. Let `f : ℂ → E` be a function such that

* `f` is differentiable in the open right half-plane and is continuous on its closure;
* `‖f z‖` is bounded from above by `A * exp(B * ‖z‖ ^ c)` on the open right half-plane
  for some `c < 2`;
* `‖f z‖` is bounded from above by a constant `C` on the imaginary axis;
* `‖f x‖` is bounded from above by a constant for large real values of `x`.

Then `‖f z‖` is bounded from above by `C` on the closed right half-plane.
See also `PhragmenLindelof.right_half_plane_of_tendsto_zero_on_real` for a weaker version. -/
theorem right_half_plane_of_bounded_on_real (hd : DiffContOnCl ℂ f {z | 0 < z.re})
    (hexp : ∃ c < (2 : ℝ), ∃ B,
      f =O[cobounded ℂ ⊓ 𝓟 {z | 0 < z.re}] fun z => expR (B * ‖z‖ ^ c))
    (hre : IsBoundedUnder (· ≤ ·) atTop fun x : ℝ => ‖f x‖) (him : ∀ x : ℝ, ‖f (x * I)‖ ≤ C)
    (hz : 0 ≤ z.re) : ‖f z‖ ≤ C := by
  -- For each `ε < 0`, the function `fun z ↦ exp (ε * z) • f z` satisfies assumptions of
  -- `right_half_plane_of_tendsto_zero_on_real`, hence `‖exp (ε * z) • f z‖ ≤ C` for all `ε < 0`.
  -- Taking the limit as `ε → 0`, we obtain the required inequality.
  suffices ∀ᶠ ε : ℝ in 𝓝[<] 0, ‖exp (ε * z) • f z‖ ≤ C by
    refine le_of_tendsto (Tendsto.mono_left ?_ nhdsWithin_le_nhds) this
    exact Continuous.tendsto' (by fun_prop) _ _ (by simp)
  filter_upwards [self_mem_nhdsWithin] with ε ε₀; change ε < 0 at ε₀
  set g : ℂ → E := fun z => exp (ε * z) • f z; change ‖g z‖ ≤ C
  replace hd : DiffContOnCl ℂ g {z : ℂ | 0 < z.re} :=
    (differentiable_id.const_mul _).cexp.diffContOnCl.smul hd
  have hgn : ∀ z, ‖g z‖ = expR (ε * z.re) * ‖f z‖ := fun z ↦ by
    rw [norm_smul, norm_exp, re_ofReal_mul]
  refine right_half_plane_of_tendsto_zero_on_real hd ?_ ?_ (fun y => ?_) hz
  · rcases hexp with ⟨c, hc, B, hO⟩
    refine ⟨c, hc, B, .trans (.of_bound' ?_) hO⟩
    refine eventually_inf_principal.2 <| Eventually.of_forall fun z hz => ?_
    rw [hgn]
    refine mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.2 ?_)
    exact mul_nonpos_of_nonpos_of_nonneg ε₀.le (le_of_lt hz)
  · simp_rw [g, ← ofReal_mul, ← ofReal_exp, coe_smul]
    have h₀ : Tendsto (fun x : ℝ => expR (ε * x)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_const_nhds.neg_mul_atTop ε₀ tendsto_id)
    exact h₀.zero_smul_isBoundedUnder_le hre
  · rw [hgn, re_ofReal_mul, I_re, mul_zero, mul_zero, Real.exp_zero,
      one_mul]
    exact him y

/-- **Phragmen-Lindelöf principle** in the right half-plane. Let `f : ℂ → E` be a function such that

* `f` is differentiable in the open right half-plane and is continuous on its closure;
* `‖f z‖` is bounded from above by `A * exp(B * ‖z‖ ^ c)` on the open right half-plane
  for some `c < 2`;
* `‖f z‖` is bounded from above by a constant on the imaginary axis;
* `f x`, `x : ℝ`, tends to zero superexponentially fast as `x → ∞`:
  for any natural `n`, `exp (n * x) * ‖f x‖` tends to zero as `x → ∞`.

Then `f` is equal to zero on the closed right half-plane. -/
theorem eq_zero_on_right_half_plane_of_superexponential_decay (hd : DiffContOnCl ℂ f {z | 0 < z.re})
    (hexp : ∃ c < (2 : ℝ), ∃ B,
      f =O[cobounded ℂ ⊓ 𝓟 {z | 0 < z.re}] fun z => expR (B * ‖z‖ ^ c))
    (hre : SuperpolynomialDecay atTop expR fun x => ‖f x‖) (him : ∃ C, ∀ x : ℝ, ‖f (x * I)‖ ≤ C) :
    EqOn f 0 {z : ℂ | 0 ≤ z.re} := by
  rcases him with ⟨C, hC⟩
  -- Due to continuity, it suffices to prove the equality on the open right half-plane.
  suffices ∀ z : ℂ, 0 < z.re → f z = 0 by
    simpa only [closure_setOf_lt_re] using
      EqOn.of_subset_closure this hd.continuousOn continuousOn_const subset_closure Subset.rfl
  -- Consider $g_n(z)=e^{nz}f(z)$.
  set g : ℕ → ℂ → E := fun (n : ℕ) (z : ℂ) => exp z ^ n • f z
  have hg : ∀ n z, ‖g n z‖ = expR z.re ^ n * ‖f z‖ := fun n z ↦ by
    simp only [g, norm_smul, norm_pow, norm_exp]
  intro z hz
  -- Since `e^{nz} → ∞` as `n → ∞`, it suffices to show that each `g_n` is bounded from above by `C`
  suffices H : ∀ n : ℕ, ‖g n z‖ ≤ C by
    contrapose! H
    simp only [hg]
    exact (((tendsto_pow_atTop_atTop_of_one_lt (Real.one_lt_exp_iff.2 hz)).atTop_mul_const
      (norm_pos_iff.2 H)).eventually (eventually_gt_atTop C)).exists
  intro n
  -- This estimate follows from the Phragmen-Lindelöf principle in the right half-plane.
  refine right_half_plane_of_tendsto_zero_on_real ((differentiable_exp.pow n).diffContOnCl.smul hd)
    ?_ ?_ (fun y => ?_) hz.le
  · rcases hexp with ⟨c, hc, B, hO⟩
    refine ⟨max c 1, max_lt hc one_lt_two, n + max B 0, .of_norm_left ?_⟩
    simp only [hg]
    refine ((isBigO_refl (fun z : ℂ => expR z.re ^ n) _).mul hO.norm_left).trans (.of_bound' ?_)
    filter_upwards [(eventually_cobounded_le_norm 1).filter_mono inf_le_left] with z hz
    simp only [← Real.exp_nat_mul, ← Real.exp_add, Real.norm_eq_abs, Real.abs_exp, add_mul]
    gcongr
    · calc
        z.re ≤ ‖z‖ := re_le_norm _
        _ = ‖z‖ ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ ‖z‖ ^ max c 1 := Real.rpow_le_rpow_of_exponent_le hz (le_max_right _ _)
    exacts [le_max_left _ _, le_max_left _ _]
  · rw [tendsto_zero_iff_norm_tendsto_zero]; simp only [hg]
    exact hre n
  · rw [hg, re_ofReal_mul, I_re, mul_zero, Real.exp_zero, one_pow, one_mul]
    exact hC y

/-- **Phragmen-Lindelöf principle** in the right half-plane. Let `f g : ℂ → E` be functions such
that

* `f` and `g` are differentiable in the open right half-plane and are continuous on its closure;
* `‖f z‖` and `‖g z‖` are bounded from above by `A * exp(B * ‖z‖ ^ c)` on the open right
  half-plane for some `c < 2`;
* `‖f z‖` and `‖g z‖` are bounded from above by constants on the imaginary axis;
* `f x - g x`, `x : ℝ`, tends to zero superexponentially fast as `x → ∞`:
  for any natural `n`, `exp (n * x) * ‖f x - g x‖` tends to zero as `x → ∞`.

Then `f` is equal to `g` on the closed right half-plane. -/
theorem eqOn_right_half_plane_of_superexponential_decay {g : ℂ → E}
    (hfd : DiffContOnCl ℂ f {z | 0 < z.re}) (hgd : DiffContOnCl ℂ g {z | 0 < z.re})
    (hfexp : ∃ c < (2 : ℝ), ∃ B,
      f =O[cobounded ℂ ⊓ 𝓟 {z | 0 < z.re}] fun z => expR (B * ‖z‖ ^ c))
    (hgexp : ∃ c < (2 : ℝ), ∃ B,
      g =O[cobounded ℂ ⊓ 𝓟 {z | 0 < z.re}] fun z => expR (B * ‖z‖ ^ c))
    (hre : SuperpolynomialDecay atTop expR fun x => ‖f x - g x‖)
    (hfim : ∃ C, ∀ x : ℝ, ‖f (x * I)‖ ≤ C) (hgim : ∃ C, ∀ x : ℝ, ‖g (x * I)‖ ≤ C) :
    EqOn f g {z : ℂ | 0 ≤ z.re} := by
  suffices EqOn (f - g) 0 {z : ℂ | 0 ≤ z.re} by
    simpa only [EqOn, Pi.sub_apply, Pi.zero_apply, sub_eq_zero] using this
  refine eq_zero_on_right_half_plane_of_superexponential_decay (hfd.sub hgd) ?_ hre ?_
  · exact isBigO_sub_exp_rpow hfexp hgexp
  · rcases hfim with ⟨Cf, hCf⟩; rcases hgim with ⟨Cg, hCg⟩
    exact ⟨Cf + Cg, fun x => norm_sub_le_of_le (hCf x) (hCg x)⟩

end PhragmenLindelof
