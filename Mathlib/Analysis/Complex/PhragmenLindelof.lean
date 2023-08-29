/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Asymptotics.SuperpolynomialDecay

#align_import analysis.complex.phragmen_lindelof from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

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

open Set Function Filter Asymptotics Metric Complex
open scoped Topology Filter Real

local notation "expR" => Real.exp
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

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
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.abs_exp, Real.abs_exp, Real.exp_le_exp]
    exact
      mul_le_mul hB (Real.exp_le_exp.2 <| mul_le_mul_of_nonneg_right hc <| abs_nonneg _)
        (Real.exp_pos _).le hB₀
  rcases hBf with ⟨cf, hcf, Bf, hOf⟩; rcases hBg with ⟨cg, hcg, Bg, hOg⟩
  -- ⊢ ∃ c, c < a ∧ ∃ B, (f - g) =O[l] fun z => expR (B * expR (c * |u z|))
                                      -- ⊢ ∃ c, c < a ∧ ∃ B, (f - g) =O[l] fun z => expR (B * expR (c * |u z|))
  refine' ⟨max cf cg, max_lt hcf hcg, max 0 (max Bf Bg), _⟩
  -- ⊢ (f - g) =O[l] fun z => expR (max 0 (max Bf Bg) * expR (max cf cg * |u z|))
  refine' (hOf.trans_le <| this _ _ _).sub (hOg.trans_le <| this _ _ _)
  exacts [le_max_left _ _, le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
    le_max_right _ _, le_max_left _ _, (le_max_right _ _).trans (le_max_right _ _)]
set_option linter.uppercaseLean3 false in
#align phragmen_lindelof.is_O_sub_exp_exp PhragmenLindelof.isBigO_sub_exp_exp

/-- An auxiliary lemma that combines two “exponential of a power” estimates into a similar estimate
on the difference of the functions. -/
theorem isBigO_sub_exp_rpow {a : ℝ} {f g : ℂ → E} {l : Filter ℂ}
    (hBf : ∃ c < a, ∃ B, f =O[comap Complex.abs atTop ⊓ l] fun z => expR (B * abs z ^ c))
    (hBg : ∃ c < a, ∃ B, g =O[comap Complex.abs atTop ⊓ l] fun z => expR (B * abs z ^ c)) :
    ∃ c < a, ∃ B, (f - g) =O[comap Complex.abs atTop ⊓ l] fun z => expR (B * abs z ^ c) := by
  have : ∀ {c₁ c₂ B₁ B₂ : ℝ}, c₁ ≤ c₂ → 0 ≤ B₂ → B₁ ≤ B₂ →
      (fun z : ℂ => expR (B₁ * abs z ^ c₁)) =O[comap Complex.abs atTop ⊓ l]
        fun z => expR (B₂ * abs z ^ c₂) := fun hc hB₀ hB ↦ .of_bound 1 <| by
    have : ∀ᶠ z : ℂ in comap Complex.abs atTop ⊓ l, 1 ≤ abs z :=
      ((eventually_ge_atTop 1).comap _).filter_mono inf_le_left
    refine this.mono fun z hz => ?_
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.abs_exp, Real.abs_exp, Real.exp_le_exp]
    exact mul_le_mul hB (Real.rpow_le_rpow_of_exponent_le hz hc)
      (Real.rpow_nonneg_of_nonneg (Complex.abs.nonneg _) _) hB₀
  rcases hBf with ⟨cf, hcf, Bf, hOf⟩; rcases hBg with ⟨cg, hcg, Bg, hOg⟩
  -- ⊢ ∃ c, c < a ∧ ∃ B, (f - g) =O[comap (↑Complex.abs) atTop ⊓ l] fun z => expR ( …
                                      -- ⊢ ∃ c, c < a ∧ ∃ B, (f - g) =O[comap (↑Complex.abs) atTop ⊓ l] fun z => expR ( …
  refine' ⟨max cf cg, max_lt hcf hcg, max 0 (max Bf Bg), _⟩
  -- ⊢ (f - g) =O[comap (↑Complex.abs) atTop ⊓ l] fun z => expR (max 0 (max Bf Bg)  …
  refine' (hOf.trans <| this _ _ _).sub (hOg.trans <| this _ _ _)
  exacts [le_max_left _ _, le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
    le_max_right _ _, le_max_left _ _, (le_max_right _ _).trans (le_max_right _ _)]
set_option linter.uppercaseLean3 false in
#align phragmen_lindelof.is_O_sub_exp_rpow PhragmenLindelof.isBigO_sub_exp_rpow

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
    (hB : ∃ c < π / (b - a), ∃ B,
      f =O[comap (Abs.abs ∘ re) atTop ⊓ 𝓟 (im ⁻¹' Ioo a b)] fun z ↦ expR (B * expR (c * |z.re|)))
    (hle_a : ∀ z : ℂ, im z = a → ‖f z‖ ≤ C) (hle_b : ∀ z, im z = b → ‖f z‖ ≤ C) (hza : a ≤ im z)
    (hzb : im z ≤ b) : ‖f z‖ ≤ C := by
  -- If `im z = a` or `im z = b`, then we apply `hle_a` or `hle_b`, otherwise `im z ∈ Ioo a b`.
  rw [le_iff_eq_or_lt] at hza hzb
  -- ⊢ ‖f z‖ ≤ C
  cases' hza with hza hza; · exact hle_a _ hza.symm
  -- ⊢ ‖f z‖ ≤ C
                             -- 🎉 no goals
  cases' hzb with hzb hzb; · exact hle_b _ hzb
  -- ⊢ ‖f z‖ ≤ C
                             -- 🎉 no goals
  wlog hC₀ : 0 < C generalizing C
  -- ⊢ ‖f z‖ ≤ C
  · refine' le_of_forall_le_of_dense fun C' hC' => this (fun w hw => _) (fun w hw => _) _
    · exact (hle_a _ hw).trans hC'.le
      -- 🎉 no goals
    · exact (hle_b _ hw).trans hC'.le
      -- 🎉 no goals
    · refine' ((norm_nonneg (f (a * I))).trans (hle_a _ _)).trans_lt hC'
      -- ⊢ (↑a * I).im = a
      rw [mul_I_im, ofReal_re]
      -- 🎉 no goals
  -- After a change of variables, we deal with the strip `a - b < im z < a + b` instead
  -- of `a < im z < b`
  obtain ⟨a, b, rfl, rfl⟩ : ∃ a' b', a = a' - b' ∧ b = a' + b' :=
    ⟨(a + b) / 2, (b - a) / 2, by ring, by ring⟩
  have hab : a - b < a + b := hza.trans hzb
  -- ⊢ ‖f z‖ ≤ C
  have hb : 0 < b := by simpa only [sub_eq_add_neg, add_lt_add_iff_left, neg_lt_self_iff] using hab
  -- ⊢ ‖f z‖ ≤ C
  rw [add_sub_sub_cancel, ← two_mul, div_mul_eq_div_div] at hB
  -- ⊢ ‖f z‖ ≤ C
  have hπb : 0 < π / 2 / b := div_pos Real.pi_div_two_pos hb
  -- ⊢ ‖f z‖ ≤ C
  -- Choose some `c B : ℝ` satisfying `hB`, then choose `max c 0 < d < π / 2 / b`.
  rcases hB with ⟨c, hc, B, hO⟩
  -- ⊢ ‖f z‖ ≤ C
  obtain ⟨d, ⟨hcd, hd₀⟩, hd⟩ : ∃ d, (c < d ∧ 0 < d) ∧ d < π / 2 / b := by
    simpa only [max_lt_iff] using exists_between (max_lt hc hπb)
  have hb' : d * b < π / 2 := (lt_div_iff hb).1 hd
  -- ⊢ ‖f z‖ ≤ C
  set aff := (fun w => d * (w - a * I) : ℂ → ℂ)
  -- ⊢ ‖f z‖ ≤ C
  set g := fun (ε : ℝ) (w : ℂ) => exp (ε * (exp (aff w) + exp (-aff w)))
  -- ⊢ ‖f z‖ ≤ C
  /- Since `g ε z → 1` as `ε → 0⁻`, it suffices to prove that `‖g ε z • f z‖ ≤ C`
    for all negative `ε`. -/
  suffices : ∀ᶠ ε : ℝ in 𝓝[<] (0 : ℝ), ‖g ε z • f z‖ ≤ C
  -- ⊢ ‖f z‖ ≤ C
  · refine' le_of_tendsto (Tendsto.mono_left _ nhdsWithin_le_nhds) this
    -- ⊢ Tendsto (fun c => ‖g c z • f z‖) (𝓝 0) (𝓝 ‖f z‖)
    apply ((continuous_ofReal.mul continuous_const).cexp.smul continuous_const).norm.tendsto'
    -- ⊢ ‖exp (↑0 * (exp (aff z) + exp (-aff z))) • f z‖ = ‖f z‖
    simp
    -- 🎉 no goals
  filter_upwards [self_mem_nhdsWithin] with ε ε₀; change ε < 0 at ε₀
  -- ⊢ ‖exp (↑ε * (exp (↑d * (z - ↑a * I)) + exp (-(↑d * (z - ↑a * I))))) • f z‖ ≤ C
                                                  -- ⊢ ‖exp (↑ε * (exp (↑d * (z - ↑a * I)) + exp (-(↑d * (z - ↑a * I))))) • f z‖ ≤ C
  -- An upper estimate on `‖g ε w‖` that will be used in two branches of the proof.
  obtain ⟨δ, δ₀, hδ⟩ :
    ∃ δ : ℝ,
      δ < 0 ∧ ∀ ⦃w⦄, im w ∈ Icc (a - b) (a + b) → abs (g ε w) ≤ expR (δ * expR (d * |re w|)) := by
    refine'
      ⟨ε * Real.cos (d * b),
        mul_neg_of_neg_of_pos ε₀
          (Real.cos_pos_of_mem_Ioo <| abs_lt.1 <| (abs_of_pos (mul_pos hd₀ hb)).symm ▸ hb'),
        fun w hw => _⟩
    replace hw : |im (aff w)| ≤ d * b
    · rw [← Real.closedBall_eq_Icc] at hw
      rwa [ofReal_mul_im, sub_im, mul_I_im, ofReal_re, _root_.abs_mul, abs_of_pos hd₀,
        mul_le_mul_left hd₀]
    simpa only [ofReal_mul_re, _root_.abs_mul, abs_of_pos hd₀, sub_re, mul_I_re, ofReal_im,
      zero_mul, neg_zero, sub_zero] using
      abs_exp_mul_exp_add_exp_neg_le_of_abs_im_le ε₀.le hw hb'.le
  -- `abs (g ε w) ≤ 1` on the lines `w.im = a ± b` (actually, it holds everywhere in the strip)
  have hg₁ : ∀ w, im w = a - b ∨ im w = a + b → abs (g ε w) ≤ 1 := by
    refine' fun w hw => (hδ <| hw.by_cases _ _).trans (Real.exp_le_one_iff.2 _)
    exacts [fun h => h.symm ▸ left_mem_Icc.2 hab.le, fun h => h.symm ▸ right_mem_Icc.2 hab.le,
      mul_nonpos_of_nonpos_of_nonneg δ₀.le (Real.exp_pos _).le]
  /- Our apriori estimate on `f` implies that `g ε w • f w → 0` as `|w.re| → ∞` along the strip. In
    particular, its norm is less than or equal to `C` for sufficiently large `|w.re|`. -/
  obtain ⟨R, hzR, hR⟩ :
    ∃ R : ℝ, |z.re| < R ∧ ∀ w, |re w| = R → im w ∈ Ioo (a - b) (a + b) → ‖g ε w • f w‖ ≤ C := by
    refine' ((eventually_gt_atTop _).and _).exists
    rcases hO.exists_pos with ⟨A, hA₀, hA⟩
    simp only [isBigOWith_iff, eventually_inf_principal, eventually_comap, mem_Ioo, ← abs_lt,
      mem_preimage, (· ∘ ·), Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hA
    suffices :
        Tendsto (fun R => expR (δ * expR (d * R) + B * expR (c * R) + Real.log A)) atTop (𝓝 0)
    · filter_upwards [this.eventually (ge_mem_nhds hC₀), hA] with R hR Hle w hre him
      calc
        ‖g ε w • f w‖ ≤ expR (δ * expR (d * R) + B * expR (c * R) + Real.log A) := ?_
        _ ≤ C := hR
      rw [norm_smul, Real.exp_add, ← hre, Real.exp_add, Real.exp_log hA₀, mul_assoc, mul_comm _ A]
      exact mul_le_mul (hδ <| Ioo_subset_Icc_self him) (Hle _ hre him) (norm_nonneg _)
        (Real.exp_pos _).le
    refine' Real.tendsto_exp_atBot.comp _
    suffices H : Tendsto (fun R => δ + B * (expR ((d - c) * R))⁻¹) atTop (𝓝 (δ + B * 0))
    · rw [mul_zero, add_zero] at H
      refine' Tendsto.atBot_add _ tendsto_const_nhds
      simpa only [id, (· ∘ ·), add_mul, mul_assoc, ← div_eq_inv_mul, ← Real.exp_sub, ← sub_mul,
        sub_sub_cancel]
        using H.neg_mul_atTop δ₀ <| Real.tendsto_exp_atTop.comp <|
          tendsto_const_nhds.mul_atTop hd₀ tendsto_id
    refine' tendsto_const_nhds.add (tendsto_const_nhds.mul _)
    exact tendsto_inv_atTop_zero.comp <| Real.tendsto_exp_atTop.comp <|
      tendsto_const_nhds.mul_atTop (sub_pos.2 hcd) tendsto_id
  have hR₀ : 0 < R := (_root_.abs_nonneg _).trans_lt hzR
  -- ⊢ ‖exp (↑ε * (exp (↑d * (z - ↑a * I)) + exp (-(↑d * (z - ↑a * I))))) • f z‖ ≤ C
  /- Finally, we apply the bounded version of the maximum modulus principle to the rectangle
    `(-R, R) × (a - b, a + b)`. The function is bounded by `C` on the horizontal sides by assumption
    (and because `‖g ε w‖ ≤ 1`) and on the vertical sides by the choice of `R`. -/
  have hgd : Differentiable ℂ (g ε) :=
    ((((differentiable_id.sub_const _).const_mul _).cexp.add
            ((differentiable_id.sub_const _).const_mul _).neg.cexp).const_mul _).cexp
  replace hd : DiffContOnCl ℂ (fun w => g ε w • f w) (Ioo (-R) R ×ℂ Ioo (a - b) (a + b))
  -- ⊢ DiffContOnCl ℂ (fun w => g ε w • f w) (Ioo (-R) R ×ℂ Ioo (a - b) (a + b))
  exact (hgd.diffContOnCl.smul hfd).mono (inter_subset_right _ _)
  -- ⊢ ‖exp (↑ε * (exp (↑d * (z - ↑a * I)) + exp (-(↑d * (z - ↑a * I))))) • f z‖ ≤ C
  convert norm_le_of_forall_mem_frontier_norm_le ((bounded_Ioo _ _).reProdIm (bounded_Ioo _ _)) hd
    (fun w hw => _) _
  · rw [frontier_reProdIm, closure_Ioo (neg_lt_self hR₀).ne, frontier_Ioo hab, closure_Ioo hab.ne,
      frontier_Ioo (neg_lt_self hR₀)] at hw
    by_cases him : w.im = a - b ∨ w.im = a + b
    -- ⊢ ‖g ε w • f w‖ ≤ C
    · rw [norm_smul, ← one_mul C]
      -- ⊢ ‖g ε w‖ * ‖f w‖ ≤ 1 * C
      exact mul_le_mul (hg₁ _ him) (him.by_cases (hle_a _) (hle_b _)) (norm_nonneg _) zero_le_one
      -- 🎉 no goals
    · replace hw : w ∈ {-R, R} ×ℂ Icc (a - b) (a + b); exact hw.resolve_left fun h => him h.2
      -- ⊢ w ∈ {-R, R} ×ℂ Icc (a - b) (a + b)
                                                       -- ⊢ ‖g ε w • f w‖ ≤ C
      have hw' := eq_endpoints_or_mem_Ioo_of_mem_Icc hw.2; rw [← or_assoc] at hw'
      -- ⊢ ‖g ε w • f w‖ ≤ C
                                                           -- ⊢ ‖g ε w • f w‖ ≤ C
      exact hR _ ((abs_eq hR₀.le).2 hw.1.symm) (hw'.resolve_left him)
      -- 🎉 no goals
  · rw [closure_reProdIm, closure_Ioo hab.ne, closure_Ioo (neg_lt_self hR₀).ne]
    -- ⊢ z ∈ Icc (-R) R ×ℂ Icc (a - b) (a + b)
    exact ⟨abs_le.1 hzR.le, ⟨hza.le, hzb.le⟩⟩
    -- 🎉 no goals
#align phragmen_lindelof.horizontal_strip PhragmenLindelof.horizontal_strip

/-- **Phragmen-Lindelöf principle** in a strip `U = {z : ℂ | a < im z < b}`.
Let `f : ℂ → E` be a function such that

* `f` is differentiable on `U` and is continuous on its closure;
* `‖f z‖` is bounded from above by `A * exp(B * exp(c * |re z|))` on `U` for some `c < π / (b - a)`;
* `f z = 0` on the boundary of `U`.

Then `f` is equal to zero on the closed strip `{z : ℂ | a ≤ im z ≤ b}`.
-/
theorem eq_zero_on_horizontal_strip (hd : DiffContOnCl ℂ f (im ⁻¹' Ioo a b))
    (hB : ∃ c < π / (b - a), ∃ B,
      f =O[comap (Abs.abs ∘ re) atTop ⊓ 𝓟 (im ⁻¹' Ioo a b)] fun z ↦ expR (B * expR (c * |z.re|)))
    (ha : ∀ z : ℂ, z.im = a → f z = 0) (hb : ∀ z : ℂ, z.im = b → f z = 0) :
    EqOn f 0 (im ⁻¹' Icc a b) := fun _z hz =>
  norm_le_zero_iff.1 <| horizontal_strip hd hB (fun z hz => (ha z hz).symm ▸ norm_zero.le)
    (fun z hz => (hb z hz).symm ▸ norm_zero.le) hz.1 hz.2
#align phragmen_lindelof.eq_zero_on_horizontal_strip PhragmenLindelof.eq_zero_on_horizontal_strip

/-- **Phragmen-Lindelöf principle** in a strip `U = {z : ℂ | a < im z < b}`.
Let `f g : ℂ → E` be functions such that

* `f` and `g` are differentiable on `U` and are continuous on its closure;
* `‖f z‖` and `‖g z‖` are bounded from above by `A * exp(B * exp(c * |re z|))` on `U` for some
  `c < π / (b - a)`;
* `f z = g z` on the boundary of `U`.

Then `f` is equal to `g` on the closed strip `{z : ℂ | a ≤ im z ≤ b}`.
-/
theorem eqOn_horizontal_strip {g : ℂ → E} (hdf : DiffContOnCl ℂ f (im ⁻¹' Ioo a b))
    (hBf : ∃ c < π / (b - a), ∃ B,
      f =O[comap (Abs.abs ∘ re) atTop ⊓ 𝓟 (im ⁻¹' Ioo a b)] fun z ↦ expR (B * expR (c * |z.re|)))
    (hdg : DiffContOnCl ℂ g (im ⁻¹' Ioo a b))
    (hBg : ∃ c < π / (b - a), ∃ B,
      g =O[comap (Abs.abs ∘ re) atTop ⊓ 𝓟 (im ⁻¹' Ioo a b)] fun z ↦ expR (B * expR (c * |z.re|)))
    (ha : ∀ z : ℂ, z.im = a → f z = g z) (hb : ∀ z : ℂ, z.im = b → f z = g z) :
    EqOn f g (im ⁻¹' Icc a b) := fun _z hz =>
  sub_eq_zero.1 (eq_zero_on_horizontal_strip (hdf.sub hdg) (isBigO_sub_exp_exp hBf hBg)
    (fun w hw => sub_eq_zero.2 (ha w hw)) (fun w hw => sub_eq_zero.2 (hb w hw)) hz)
#align phragmen_lindelof.eq_on_horizontal_strip PhragmenLindelof.eqOn_horizontal_strip

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
    (hB : ∃ c < π / (b - a), ∃ B,
      f =O[comap (Abs.abs ∘ im) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b)] fun z ↦ expR (B * expR (c * |z.im|)))
    (hle_a : ∀ z : ℂ, re z = a → ‖f z‖ ≤ C) (hle_b : ∀ z, re z = b → ‖f z‖ ≤ C) (hza : a ≤ re z)
    (hzb : re z ≤ b) : ‖f z‖ ≤ C := by
  suffices ‖f (z * I * -I)‖ ≤ C by simpa [mul_assoc] using this
  -- ⊢ ‖f (z * I * -I)‖ ≤ C
  have H : MapsTo (· * -I) (im ⁻¹' Ioo a b) (re ⁻¹' Ioo a b) := fun z hz ↦ by simpa using hz
  -- ⊢ ‖f (z * I * -I)‖ ≤ C
  refine' horizontal_strip (f := fun z ↦ f (z * -I))
    (hfd.comp (differentiable_id.mul_const _).diffContOnCl H) _ (fun z hz => hle_a _ _)
    (fun z hz => hle_b _ _) _ _
  · rcases hB with ⟨c, hc, B, hO⟩
    -- ⊢ ∃ c, c < π / (b - a) ∧ ∃ B, (fun z => f (z * -I)) =O[comap (Abs.abs ∘ re) at …
    refine ⟨c, hc, B, ?_⟩
    -- ⊢ (fun z => f (z * -I)) =O[comap (Abs.abs ∘ re) atTop ⊓ 𝓟 (im ⁻¹' Ioo a b)] fu …
    have : Tendsto (· * -I) (comap (|re ·|) atTop ⊓ 𝓟 (im ⁻¹' Ioo a b))
        (comap (|im ·|) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b)) := by
      refine' (tendsto_comap_iff.2 _).inf H.tendsto
      simpa [(· ∘ ·)] using tendsto_comap
    simpa [(· ∘ ·)] using hO.comp_tendsto this
    -- 🎉 no goals
  all_goals simpa
  -- 🎉 no goals
#align phragmen_lindelof.vertical_strip PhragmenLindelof.vertical_strip

/-- **Phragmen-Lindelöf principle** in a strip `U = {z : ℂ | a < re z < b}`.
Let `f : ℂ → E` be a function such that

* `f` is differentiable on `U` and is continuous on its closure;
* `‖f z‖` is bounded from above by `A * exp(B * exp(c * |im z|))` on `U` for some `c < π / (b - a)`;
* `f z = 0` on the boundary of `U`.

Then `f` is equal to zero on the closed strip `{z : ℂ | a ≤ re z ≤ b}`.
-/
theorem eq_zero_on_vertical_strip (hd : DiffContOnCl ℂ f (re ⁻¹' Ioo a b))
    (hB : ∃ c < π / (b - a), ∃ B,
      f =O[comap (Abs.abs ∘ im) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b)] fun z ↦ expR (B * expR (c * |z.im|)))
    (ha : ∀ z : ℂ, re z = a → f z = 0) (hb : ∀ z : ℂ, re z = b → f z = 0) :
    EqOn f 0 (re ⁻¹' Icc a b) := fun _z hz =>
  norm_le_zero_iff.1 <| vertical_strip hd hB (fun z hz => (ha z hz).symm ▸ norm_zero.le)
    (fun z hz => (hb z hz).symm ▸ norm_zero.le) hz.1 hz.2
#align phragmen_lindelof.eq_zero_on_vertical_strip PhragmenLindelof.eq_zero_on_vertical_strip

/-- **Phragmen-Lindelöf principle** in a strip `U = {z : ℂ | a < re z < b}`.
Let `f g : ℂ → E` be functions such that

* `f` and `g` are differentiable on `U` and are continuous on its closure;
* `‖f z‖` and `‖g z‖` are bounded from above by `A * exp(B * exp(c * |im z|))` on `U` for some
  `c < π / (b - a)`;
* `f z = g z` on the boundary of `U`.

Then `f` is equal to `g` on the closed strip `{z : ℂ | a ≤ re z ≤ b}`.
-/
theorem eqOn_vertical_strip {g : ℂ → E} (hdf : DiffContOnCl ℂ f (re ⁻¹' Ioo a b))
    (hBf : ∃ c < π / (b - a), ∃ B,
      f =O[comap (Abs.abs ∘ im) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b)] fun z ↦ expR (B * expR (c * |z.im|)))
    (hdg : DiffContOnCl ℂ g (re ⁻¹' Ioo a b))
    (hBg : ∃ c < π / (b - a), ∃ B,
      g =O[comap (Abs.abs ∘ im) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b)] fun z ↦ expR (B * expR (c * |z.im|)))
    (ha : ∀ z : ℂ, re z = a → f z = g z) (hb : ∀ z : ℂ, re z = b → f z = g z) :
    EqOn f g (re ⁻¹' Icc a b) := fun _z hz =>
  sub_eq_zero.1 (eq_zero_on_vertical_strip (hdf.sub hdg) (isBigO_sub_exp_exp hBf hBg)
    (fun w hw => sub_eq_zero.2 (ha w hw)) (fun w hw => sub_eq_zero.2 (hb w hw)) hz)
#align phragmen_lindelof.eq_on_vertical_strip PhragmenLindelof.eqOn_vertical_strip

/-!
### Phragmen-Lindelöf principle in coordinate quadrants
-/

/-- **Phragmen-Lindelöf principle** in the first quadrant. Let `f : ℂ → E` be a function such that

* `f` is differentiable in the open first quadrant and is continuous on its closure;
* `‖f z‖` is bounded from above by `A * exp(B * (abs z) ^ c)` on the open first quadrant
  for some `c < 2`;
* `‖f z‖` is bounded from above by a constant `C` on the boundary of the first quadrant.

Then `‖f z‖` is bounded from above by the same constant on the closed first quadrant. -/
nonrec theorem quadrant_I (hd : DiffContOnCl ℂ f (Ioi 0 ×ℂ Ioi 0))
    (hB : ∃ c < (2 : ℝ), ∃ B,
      f =O[comap Complex.abs atTop ⊓ 𝓟 (Ioi 0 ×ℂ Ioi 0)] fun z => expR (B * abs z ^ c))
    (hre : ∀ x : ℝ, 0 ≤ x → ‖f x‖ ≤ C) (him : ∀ x : ℝ, 0 ≤ x → ‖f (x * I)‖ ≤ C) (hz_re : 0 ≤ z.re)
    (hz_im : 0 ≤ z.im) : ‖f z‖ ≤ C := by
  -- The case `z = 0` is trivial.
  rcases eq_or_ne z 0 with (rfl | hzne);
  -- ⊢ ‖f 0‖ ≤ C
  · exact hre 0 le_rfl
    -- 🎉 no goals
  -- Otherwise, `z = e ^ ζ` for some `ζ : ℂ`, `0 < Im ζ < π / 2`.
  obtain ⟨ζ, hζ, rfl⟩ : ∃ ζ : ℂ, ζ.im ∈ Icc 0 (π / 2) ∧ exp ζ = z := by
    refine' ⟨log z, _, exp_log hzne⟩
    rw [log_im]
    exact ⟨arg_nonneg_iff.2 hz_im, arg_le_pi_div_two_iff.2 (Or.inl hz_re)⟩
  -- porting note: failed to clear `clear hz_re hz_im hzne`
  -- We are going to apply `PhragmenLindelof.horizontal_strip` to `f ∘ Complex.exp` and `ζ`.
  change ‖(f ∘ exp) ζ‖ ≤ C
  -- ⊢ ‖(f ∘ exp) ζ‖ ≤ C
  have H : MapsTo exp (im ⁻¹' Ioo 0 (π / 2)) (Ioi 0 ×ℂ Ioi 0) := fun z hz ↦ by
    rw [mem_reProdIm, exp_re, exp_im, mem_Ioi, mem_Ioi]
    have : 0 < Real.cos z.im := Real.cos_pos_of_mem_Ioo ⟨by linarith [hz.1, hz.2], hz.2⟩
    have : 0 < Real.sin z.im :=
      Real.sin_pos_of_mem_Ioo ⟨hz.1, hz.2.trans (half_lt_self Real.pi_pos)⟩
    constructor <;> positivity
  refine' horizontal_strip (hd.comp differentiable_exp.diffContOnCl H) _ _ _ hζ.1 hζ.2
  -- porting note: failed to clear hζ ζ
  · -- The estimate `hB` on `f` implies the required estimate on
    -- `f ∘ exp` with the same `c` and `B' = max B 0`.
    rw [sub_zero, div_div_cancel' Real.pi_pos.ne']
    -- ⊢ ∃ c, c < 2 ∧ ∃ B, (f ∘ exp) =O[comap (Abs.abs ∘ re) atTop ⊓ 𝓟 (im ⁻¹' Ioo 0  …
    rcases hB with ⟨c, hc, B, hO⟩
    -- ⊢ ∃ c, c < 2 ∧ ∃ B, (f ∘ exp) =O[comap (Abs.abs ∘ re) atTop ⊓ 𝓟 (im ⁻¹' Ioo 0  …
    refine' ⟨c, hc, max B 0, _⟩
    -- ⊢ (f ∘ exp) =O[comap (Abs.abs ∘ re) atTop ⊓ 𝓟 (im ⁻¹' Ioo 0 (π / 2))] fun z => …
    rw [← comap_comap, comap_abs_atTop, comap_sup, inf_sup_right]
    -- ⊢ (f ∘ exp) =O[comap re atBot ⊓ 𝓟 (im ⁻¹' Ioo 0 (π / 2)) ⊔ comap re atTop ⊓ 𝓟  …
    -- We prove separately the estimates as `ζ.re → ∞` and as `ζ.re → -∞`
    refine' IsBigO.sup _
      ((hO.comp_tendsto <| tendsto_exp_comap_re_atTop.inf H.tendsto).trans <| .of_bound 1 _)
    · -- For the estimate as `ζ.re → -∞`, note that `f` is continuous within the first quadrant at
      -- zero, hence `f (exp ζ)` has a limit as `ζ.re → -∞`, `0 < ζ.im < π / 2`.
      have hc : ContinuousWithinAt f (Ioi 0 ×ℂ Ioi 0) 0 := by
        refine' (hd.continuousOn _ _).mono subset_closure
        simp [closure_reProdIm, mem_reProdIm]
      refine'
        ((hc.tendsto.comp <| tendsto_exp_comap_re_atBot.inf H.tendsto).isBigO_one ℝ).trans
          (isBigO_of_le _ fun w => _)
      rw [norm_one, Real.norm_of_nonneg (Real.exp_pos _).le, Real.one_le_exp_iff]
      -- ⊢ 0 ≤ max B 0 * expR (c * |w.re|)
      exact mul_nonneg (le_max_right _ _) (Real.exp_pos _).le
      -- 🎉 no goals
    · -- For the estimate as `ζ.re → ∞`, we reuse the upper estimate on `f`
      simp only [eventually_inf_principal, eventually_comap, comp_apply, one_mul,
        Real.norm_of_nonneg (Real.exp_pos _).le, abs_exp, ← Real.exp_mul, Real.exp_le_exp]
      refine' (eventually_ge_atTop 0).mono fun x hx z hz _ => _
      -- ⊢ B * expR (z.re * c) ≤ max B 0 * expR (c * |z.re|)
      rw [hz, _root_.abs_of_nonneg hx, mul_comm _ c]
      -- ⊢ B * expR (c * x) ≤ max B 0 * expR (c * x)
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
      -- 🎉 no goals
  · -- If `ζ.im = 0`, then `Complex.exp ζ` is a positive real number
    intro ζ hζ; lift ζ to ℝ using hζ
    -- ⊢ ‖(f ∘ exp) ζ‖ ≤ C
                -- ⊢ ‖(f ∘ exp) ↑ζ‖ ≤ C
    rw [comp_apply, ← ofReal_exp]
    -- ⊢ ‖f ↑(expR ζ)‖ ≤ C
    exact hre _ (Real.exp_pos _).le
    -- 🎉 no goals
  · -- If `ζ.im = π / 2`, then `Complex.exp ζ` is a purely imaginary number with positive `im`
    intro ζ hζ
    -- ⊢ ‖(f ∘ exp) ζ‖ ≤ C
    rw [← re_add_im ζ, hζ, comp_apply, exp_add_mul_I, ← ofReal_cos, ← ofReal_sin,
      Real.cos_pi_div_two, Real.sin_pi_div_two, ofReal_zero, ofReal_one, one_mul, zero_add, ←
      ofReal_exp]
    exact him _ (Real.exp_pos _).le
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align phragmen_lindelof.quadrant_I PhragmenLindelof.quadrant_I

/-- **Phragmen-Lindelöf principle** in the first quadrant. Let `f : ℂ → E` be a function such that

* `f` is differentiable in the open first quadrant and is continuous on its closure;
* `‖f z‖` is bounded from above by `A * exp(B * (abs z) ^ c)` on the open first quadrant
  for some `A`, `B`, and `c < 2`;
* `f` is equal to zero on the boundary of the first quadrant.

Then `f` is equal to zero on the closed first quadrant. -/
theorem eq_zero_on_quadrant_I (hd : DiffContOnCl ℂ f (Ioi 0 ×ℂ Ioi 0))
    (hB : ∃ c < (2 : ℝ), ∃ B,
      f =O[comap Complex.abs atTop ⊓ 𝓟 (Ioi 0 ×ℂ Ioi 0)] fun z => expR (B * abs z ^ c))
    (hre : ∀ x : ℝ, 0 ≤ x → f x = 0) (him : ∀ x : ℝ, 0 ≤ x → f (x * I) = 0) :
    EqOn f 0 {z | 0 ≤ z.re ∧ 0 ≤ z.im} := fun _z hz =>
  norm_le_zero_iff.1 <|
    quadrant_I hd hB (fun x hx => norm_le_zero_iff.2 <| hre x hx)
      (fun x hx => norm_le_zero_iff.2 <| him x hx) hz.1 hz.2
set_option linter.uppercaseLean3 false in
#align phragmen_lindelof.eq_zero_on_quadrant_I PhragmenLindelof.eq_zero_on_quadrant_I

/-- **Phragmen-Lindelöf principle** in the first quadrant. Let `f g : ℂ → E` be functions such that

* `f` and `g` are differentiable in the open first quadrant and are continuous on its closure;
* `‖f z‖` and `‖g z‖` are bounded from above by `A * exp(B * (abs z) ^ c)` on the open first
  quadrant for some `A`, `B`, and `c < 2`;
* `f` is equal to `g` on the boundary of the first quadrant.

Then `f` is equal to `g` on the closed first quadrant. -/
theorem eqOn_quadrant_I (hdf : DiffContOnCl ℂ f (Ioi 0 ×ℂ Ioi 0))
    (hBf : ∃ c < (2 : ℝ), ∃ B,
      f =O[comap Complex.abs atTop ⊓ 𝓟 (Ioi 0 ×ℂ Ioi 0)] fun z => expR (B * abs z ^ c))
    (hdg : DiffContOnCl ℂ g (Ioi 0 ×ℂ Ioi 0))
    (hBg : ∃ c < (2 : ℝ), ∃ B,
      g =O[comap Complex.abs atTop ⊓ 𝓟 (Ioi 0 ×ℂ Ioi 0)] fun z => expR (B * abs z ^ c))
    (hre : ∀ x : ℝ, 0 ≤ x → f x = g x) (him : ∀ x : ℝ, 0 ≤ x → f (x * I) = g (x * I)) :
    EqOn f g {z | 0 ≤ z.re ∧ 0 ≤ z.im} := fun _z hz =>
  sub_eq_zero.1 <|
    eq_zero_on_quadrant_I (hdf.sub hdg) (isBigO_sub_exp_rpow hBf hBg)
      (fun x hx => sub_eq_zero.2 <| hre x hx) (fun x hx => sub_eq_zero.2 <| him x hx) hz
set_option linter.uppercaseLean3 false in
#align phragmen_lindelof.eq_on_quadrant_I PhragmenLindelof.eqOn_quadrant_I

/-- **Phragmen-Lindelöf principle** in the second quadrant. Let `f : ℂ → E` be a function such that

* `f` is differentiable in the open second quadrant and is continuous on its closure;
* `‖f z‖` is bounded from above by `A * exp(B * (abs z) ^ c)` on the open second quadrant
  for some `c < 2`;
* `‖f z‖` is bounded from above by a constant `C` on the boundary of the second quadrant.

Then `‖f z‖` is bounded from above by the same constant on the closed second quadrant. -/
theorem quadrant_II (hd : DiffContOnCl ℂ f (Iio 0 ×ℂ Ioi 0))
    (hB : ∃ c < (2 : ℝ), ∃ B,
      f =O[comap Complex.abs atTop ⊓ 𝓟 (Iio 0 ×ℂ Ioi 0)] fun z => expR (B * abs z ^ c))
    (hre : ∀ x : ℝ, x ≤ 0 → ‖f x‖ ≤ C) (him : ∀ x : ℝ, 0 ≤ x → ‖f (x * I)‖ ≤ C) (hz_re : z.re ≤ 0)
    (hz_im : 0 ≤ z.im) : ‖f z‖ ≤ C := by
  obtain ⟨z, rfl⟩ : ∃ z', z' * I = z; exact ⟨z / I, div_mul_cancel _ I_ne_zero⟩
  -- ⊢ ∃ z', z' * I = z
                                      -- ⊢ ‖f (z * I)‖ ≤ C
  simp only [mul_I_re, mul_I_im, neg_nonpos] at hz_re hz_im
  -- ⊢ ‖f (z * I)‖ ≤ C
  change ‖(f ∘ (· * I)) z‖ ≤ C
  -- ⊢ ‖(f ∘ fun x => x * I) z‖ ≤ C
  have H : MapsTo (· * I) (Ioi 0 ×ℂ Ioi 0) (Iio 0 ×ℂ Ioi 0) := fun w hw ↦ by
    simpa only [mem_reProdIm, mul_I_re, mul_I_im, neg_lt_zero, mem_Iio] using hw.symm
  rcases hB with ⟨c, hc, B, hO⟩
  -- ⊢ ‖(f ∘ fun x => x * I) z‖ ≤ C
  refine' quadrant_I (hd.comp (differentiable_id.mul_const _).diffContOnCl H) ⟨c, hc, B, ?_⟩ him
    (fun x hx => _) hz_im hz_re
  · simpa only [(· ∘ ·), map_mul, abs_I, mul_one]
      using hO.comp_tendsto ((tendsto_mul_right_cobounded I_ne_zero).inf H.tendsto)
  · rw [comp_apply, mul_assoc, I_mul_I, mul_neg_one, ← ofReal_neg]
    -- ⊢ ‖f ↑(-x)‖ ≤ C
    exact hre _ (neg_nonpos.2 hx)
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align phragmen_lindelof.quadrant_II PhragmenLindelof.quadrant_II

/-- **Phragmen-Lindelöf principle** in the second quadrant. Let `f : ℂ → E` be a function such that

* `f` is differentiable in the open second quadrant and is continuous on its closure;
* `‖f z‖` is bounded from above by `A * exp(B * (abs z) ^ c)` on the open second quadrant
  for some `A`, `B`, and `c < 2`;
* `f` is equal to zero on the boundary of the second quadrant.

Then `f` is equal to zero on the closed second quadrant. -/
theorem eq_zero_on_quadrant_II (hd : DiffContOnCl ℂ f (Iio 0 ×ℂ Ioi 0))
    (hB : ∃ c < (2 : ℝ), ∃ B,
      f =O[comap Complex.abs atTop ⊓ 𝓟 (Iio 0 ×ℂ Ioi 0)] fun z => expR (B * abs z ^ c))
    (hre : ∀ x : ℝ, x ≤ 0 → f x = 0) (him : ∀ x : ℝ, 0 ≤ x → f (x * I) = 0) :
    EqOn f 0 {z | z.re ≤ 0 ∧ 0 ≤ z.im} := fun _z hz =>
  norm_le_zero_iff.1 <|
    quadrant_II hd hB (fun x hx => norm_le_zero_iff.2 <| hre x hx)
      (fun x hx => norm_le_zero_iff.2 <| him x hx) hz.1 hz.2
set_option linter.uppercaseLean3 false in
#align phragmen_lindelof.eq_zero_on_quadrant_II PhragmenLindelof.eq_zero_on_quadrant_II

/-- **Phragmen-Lindelöf principle** in the second quadrant. Let `f g : ℂ → E` be functions such that

* `f` and `g` are differentiable in the open second quadrant and are continuous on its closure;
* `‖f z‖` and `‖g z‖` are bounded from above by `A * exp(B * (abs z) ^ c)` on the open second
  quadrant for some `A`, `B`, and `c < 2`;
* `f` is equal to `g` on the boundary of the second quadrant.

Then `f` is equal to `g` on the closed second quadrant. -/
theorem eqOn_quadrant_II (hdf : DiffContOnCl ℂ f (Iio 0 ×ℂ Ioi 0))
    (hBf : ∃ c < (2 : ℝ), ∃ B,
      f =O[comap Complex.abs atTop ⊓ 𝓟 (Iio 0 ×ℂ Ioi 0)] fun z => expR (B * abs z ^ c))
    (hdg : DiffContOnCl ℂ g (Iio 0 ×ℂ Ioi 0))
    (hBg : ∃ c < (2 : ℝ), ∃ B,
      g =O[comap Complex.abs atTop ⊓ 𝓟 (Iio 0 ×ℂ Ioi 0)] fun z => expR (B * abs z ^ c))
    (hre : ∀ x : ℝ, x ≤ 0 → f x = g x) (him : ∀ x : ℝ, 0 ≤ x → f (x * I) = g (x * I)) :
    EqOn f g {z | z.re ≤ 0 ∧ 0 ≤ z.im} := fun _z hz =>
  sub_eq_zero.1 <| eq_zero_on_quadrant_II (hdf.sub hdg) (isBigO_sub_exp_rpow hBf hBg)
    (fun x hx => sub_eq_zero.2 <| hre x hx) (fun x hx => sub_eq_zero.2 <| him x hx) hz
set_option linter.uppercaseLean3 false in
#align phragmen_lindelof.eq_on_quadrant_II PhragmenLindelof.eqOn_quadrant_II

/-- **Phragmen-Lindelöf principle** in the third quadrant. Let `f : ℂ → E` be a function such that

* `f` is differentiable in the open third quadrant and is continuous on its closure;
* `‖f z‖` is bounded from above by `A * exp (B * (abs z) ^ c)` on the open third quadrant
  for some `c < 2`;
* `‖f z‖` is bounded from above by a constant `C` on the boundary of the third quadrant.

Then `‖f z‖` is bounded from above by the same constant on the closed third quadrant. -/
theorem quadrant_III (hd : DiffContOnCl ℂ f (Iio 0 ×ℂ Iio 0))
    (hB : ∃ c < (2 : ℝ), ∃ B,
      f =O[comap Complex.abs atTop ⊓ 𝓟 (Iio 0 ×ℂ Iio 0)] fun z => expR (B * abs z ^ c))
    (hre : ∀ x : ℝ, x ≤ 0 → ‖f x‖ ≤ C) (him : ∀ x : ℝ, x ≤ 0 → ‖f (x * I)‖ ≤ C) (hz_re : z.re ≤ 0)
    (hz_im : z.im ≤ 0) : ‖f z‖ ≤ C := by
  obtain ⟨z, rfl⟩ : ∃ z', -z' = z; exact ⟨-z, neg_neg z⟩
  -- ⊢ ∃ z', -z' = z
                                   -- ⊢ ‖f (-z)‖ ≤ C
  simp only [neg_re, neg_im, neg_nonpos] at hz_re hz_im
  -- ⊢ ‖f (-z)‖ ≤ C
  change ‖(f ∘ Neg.neg) z‖ ≤ C
  -- ⊢ ‖(f ∘ Neg.neg) z‖ ≤ C
  have H : MapsTo Neg.neg (Ioi 0 ×ℂ Ioi 0) (Iio 0 ×ℂ Iio 0) := by
    intro w hw
    simpa only [mem_reProdIm, neg_re, neg_im, neg_lt_zero, mem_Iio] using hw
  refine'
    quadrant_I (hd.comp differentiable_neg.diffContOnCl H) _ (fun x hx => _) (fun x hx => _)
      hz_re hz_im
  · rcases hB with ⟨c, hc, B, hO⟩
    -- ⊢ ∃ c, c < 2 ∧ ∃ B, (f ∘ Neg.neg) =O[comap (↑Complex.abs) atTop ⊓ 𝓟 (Ioi 0 ×ℂ  …
    refine ⟨c, hc, B, ?_⟩
    -- ⊢ (f ∘ Neg.neg) =O[comap (↑Complex.abs) atTop ⊓ 𝓟 (Ioi 0 ×ℂ Ioi 0)] fun z => e …
    simpa only [(· ∘ ·), Complex.abs.map_neg]
      using hO.comp_tendsto (tendsto_neg_cobounded.inf H.tendsto)
  · rw [comp_apply, ← ofReal_neg]
    -- ⊢ ‖f ↑(-x)‖ ≤ C
    exact hre (-x) (neg_nonpos.2 hx)
    -- 🎉 no goals
  · rw [comp_apply, ← neg_mul, ← ofReal_neg]
    -- ⊢ ‖f (↑(-x) * I)‖ ≤ C
    exact him (-x) (neg_nonpos.2 hx)
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align phragmen_lindelof.quadrant_III PhragmenLindelof.quadrant_III

/-- **Phragmen-Lindelöf principle** in the third quadrant. Let `f : ℂ → E` be a function such that

* `f` is differentiable in the open third quadrant and is continuous on its closure;
* `‖f z‖` is bounded from above by `A * exp(B * (abs z) ^ c)` on the open third quadrant
  for some `A`, `B`, and `c < 2`;
* `f` is equal to zero on the boundary of the third quadrant.

Then `f` is equal to zero on the closed third quadrant. -/
theorem eq_zero_on_quadrant_III (hd : DiffContOnCl ℂ f (Iio 0 ×ℂ Iio 0))
    (hB : ∃ c < (2 : ℝ), ∃ B,
      f =O[comap Complex.abs atTop ⊓ 𝓟 (Iio 0 ×ℂ Iio 0)] fun z => expR (B * abs z ^ c))
    (hre : ∀ x : ℝ, x ≤ 0 → f x = 0) (him : ∀ x : ℝ, x ≤ 0 → f (x * I) = 0) :
    EqOn f 0 {z | z.re ≤ 0 ∧ z.im ≤ 0} := fun _z hz =>
  norm_le_zero_iff.1 <| quadrant_III hd hB (fun x hx => norm_le_zero_iff.2 <| hre x hx)
    (fun x hx => norm_le_zero_iff.2 <| him x hx) hz.1 hz.2
set_option linter.uppercaseLean3 false in
#align phragmen_lindelof.eq_zero_on_quadrant_III PhragmenLindelof.eq_zero_on_quadrant_III

/-- **Phragmen-Lindelöf principle** in the third quadrant. Let `f g : ℂ → E` be functions such that

* `f` and `g` are differentiable in the open third quadrant and are continuous on its closure;
* `‖f z‖` and `‖g z‖` are bounded from above by `A * exp(B * (abs z) ^ c)` on the open third
  quadrant for some `A`, `B`, and `c < 2`;
* `f` is equal to `g` on the boundary of the third quadrant.

Then `f` is equal to `g` on the closed third quadrant. -/
theorem eqOn_quadrant_III (hdf : DiffContOnCl ℂ f (Iio 0 ×ℂ Iio 0))
    (hBf : ∃ c < (2 : ℝ), ∃ B,
      f =O[comap Complex.abs atTop ⊓ 𝓟 (Iio 0 ×ℂ Iio 0)] fun z => expR (B * abs z ^ c))
    (hdg : DiffContOnCl ℂ g (Iio 0 ×ℂ Iio 0))
    (hBg : ∃ c < (2 : ℝ), ∃ B,
      g =O[comap Complex.abs atTop ⊓ 𝓟 (Iio 0 ×ℂ Iio 0)] fun z => expR (B * abs z ^ c))
    (hre : ∀ x : ℝ, x ≤ 0 → f x = g x) (him : ∀ x : ℝ, x ≤ 0 → f (x * I) = g (x * I)) :
    EqOn f g {z | z.re ≤ 0 ∧ z.im ≤ 0} := fun _z hz =>
  sub_eq_zero.1 <| eq_zero_on_quadrant_III (hdf.sub hdg) (isBigO_sub_exp_rpow hBf hBg)
    (fun x hx => sub_eq_zero.2 <| hre x hx) (fun x hx => sub_eq_zero.2 <| him x hx) hz
set_option linter.uppercaseLean3 false in
#align phragmen_lindelof.eq_on_quadrant_III PhragmenLindelof.eqOn_quadrant_III

/-- **Phragmen-Lindelöf principle** in the fourth quadrant. Let `f : ℂ → E` be a function such that

* `f` is differentiable in the open fourth quadrant and is continuous on its closure;
* `‖f z‖` is bounded from above by `A * exp(B * (abs z) ^ c)` on the open fourth quadrant
  for some `c < 2`;
* `‖f z‖` is bounded from above by a constant `C` on the boundary of the fourth quadrant.

Then `‖f z‖` is bounded from above by the same constant on the closed fourth quadrant. -/
theorem quadrant_IV (hd : DiffContOnCl ℂ f (Ioi 0 ×ℂ Iio 0))
    (hB : ∃ c < (2 : ℝ), ∃ B,
      f =O[comap Complex.abs atTop ⊓ 𝓟 (Ioi 0 ×ℂ Iio 0)] fun z => expR (B * abs z ^ c))
    (hre : ∀ x : ℝ, 0 ≤ x → ‖f x‖ ≤ C) (him : ∀ x : ℝ, x ≤ 0 → ‖f (x * I)‖ ≤ C) (hz_re : 0 ≤ z.re)
    (hz_im : z.im ≤ 0) : ‖f z‖ ≤ C := by
  obtain ⟨z, rfl⟩ : ∃ z', -z' = z := ⟨-z, neg_neg z⟩
  -- ⊢ ‖f (-z)‖ ≤ C
  simp only [neg_re, neg_im, neg_nonpos, neg_nonneg] at hz_re hz_im
  -- ⊢ ‖f (-z)‖ ≤ C
  change ‖(f ∘ Neg.neg) z‖ ≤ C
  -- ⊢ ‖(f ∘ Neg.neg) z‖ ≤ C
  have H : MapsTo Neg.neg (Iio 0 ×ℂ Ioi 0) (Ioi 0 ×ℂ Iio 0) := fun w hw ↦ by
    simpa only [mem_reProdIm, neg_re, neg_im, neg_lt_zero, neg_pos, mem_Ioi, mem_Iio] using hw
  refine' quadrant_II (hd.comp differentiable_neg.diffContOnCl H) _ (fun x hx => _) (fun x hx => _)
    hz_re hz_im
  · rcases hB with ⟨c, hc, B, hO⟩
    -- ⊢ ∃ c, c < 2 ∧ ∃ B, (f ∘ Neg.neg) =O[comap (↑Complex.abs) atTop ⊓ 𝓟 (Iio 0 ×ℂ  …
    refine ⟨c, hc, B, ?_⟩
    -- ⊢ (f ∘ Neg.neg) =O[comap (↑Complex.abs) atTop ⊓ 𝓟 (Iio 0 ×ℂ Ioi 0)] fun z => e …
    simpa only [(· ∘ ·), Complex.abs.map_neg]
      using hO.comp_tendsto (tendsto_neg_cobounded.inf H.tendsto)
  · rw [comp_apply, ← ofReal_neg]
    -- ⊢ ‖f ↑(-x)‖ ≤ C
    exact hre (-x) (neg_nonneg.2 hx)
    -- 🎉 no goals
  · rw [comp_apply, ← neg_mul, ← ofReal_neg]
    -- ⊢ ‖f (↑(-x) * I)‖ ≤ C
    exact him (-x) (neg_nonpos.2 hx)
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align phragmen_lindelof.quadrant_IV PhragmenLindelof.quadrant_IV

/-- **Phragmen-Lindelöf principle** in the fourth quadrant. Let `f : ℂ → E` be a function such that

* `f` is differentiable in the open fourth quadrant and is continuous on its closure;
* `‖f z‖` is bounded from above by `A * exp(B * (abs z) ^ c)` on the open fourth quadrant
  for some `A`, `B`, and `c < 2`;
* `f` is equal to zero on the boundary of the fourth quadrant.

Then `f` is equal to zero on the closed fourth quadrant. -/
theorem eq_zero_on_quadrant_IV (hd : DiffContOnCl ℂ f (Ioi 0 ×ℂ Iio 0))
    (hB : ∃ c < (2 : ℝ), ∃ B,
      f =O[comap Complex.abs atTop ⊓ 𝓟 (Ioi 0 ×ℂ Iio 0)] fun z => expR (B * abs z ^ c))
    (hre : ∀ x : ℝ, 0 ≤ x → f x = 0) (him : ∀ x : ℝ, x ≤ 0 → f (x * I) = 0) :
    EqOn f 0 {z | 0 ≤ z.re ∧ z.im ≤ 0} := fun _z hz =>
  norm_le_zero_iff.1 <|
    quadrant_IV hd hB (fun x hx => norm_le_zero_iff.2 <| hre x hx)
      (fun x hx => norm_le_zero_iff.2 <| him x hx) hz.1 hz.2
set_option linter.uppercaseLean3 false in
#align phragmen_lindelof.eq_zero_on_quadrant_IV PhragmenLindelof.eq_zero_on_quadrant_IV

/-- **Phragmen-Lindelöf principle** in the fourth quadrant. Let `f g : ℂ → E` be functions such that

* `f` and `g` are differentiable in the open fourth quadrant and are continuous on its closure;
* `‖f z‖` and `‖g z‖` are bounded from above by `A * exp(B * (abs z) ^ c)` on the open fourth
  quadrant for some `A`, `B`, and `c < 2`;
* `f` is equal to `g` on the boundary of the fourth quadrant.

Then `f` is equal to `g` on the closed fourth quadrant. -/
theorem eqOn_quadrant_IV (hdf : DiffContOnCl ℂ f (Ioi 0 ×ℂ Iio 0))
    (hBf : ∃ c < (2 : ℝ), ∃ B,
      f =O[comap Complex.abs atTop ⊓ 𝓟 (Ioi 0 ×ℂ Iio 0)] fun z => expR (B * abs z ^ c))
    (hdg : DiffContOnCl ℂ g (Ioi 0 ×ℂ Iio 0))
    (hBg : ∃ c < (2 : ℝ), ∃ B,
      g =O[comap Complex.abs atTop ⊓ 𝓟 (Ioi 0 ×ℂ Iio 0)] fun z => expR (B * abs z ^ c))
    (hre : ∀ x : ℝ, 0 ≤ x → f x = g x) (him : ∀ x : ℝ, x ≤ 0 → f (x * I) = g (x * I)) :
    EqOn f g {z | 0 ≤ z.re ∧ z.im ≤ 0} := fun _z hz =>
  sub_eq_zero.1 <| eq_zero_on_quadrant_IV (hdf.sub hdg) (isBigO_sub_exp_rpow hBf hBg)
    (fun x hx => sub_eq_zero.2 <| hre x hx) (fun x hx => sub_eq_zero.2 <| him x hx) hz
set_option linter.uppercaseLean3 false in
#align phragmen_lindelof.eq_on_quadrant_IV PhragmenLindelof.eqOn_quadrant_IV

/-!
### Phragmen-Lindelöf principle in the right half-plane
-/


/-- **Phragmen-Lindelöf principle** in the right half-plane. Let `f : ℂ → E` be a function such that

* `f` is differentiable in the open right half-plane and is continuous on its closure;
* `‖f z‖` is bounded from above by `A * exp(B * (abs z) ^ c)` on the open right half-plane
  for some `c < 2`;
* `‖f z‖` is bounded from above by a constant `C` on the imaginary axis;
* `f x → 0` as `x : ℝ` tends to infinity.

Then `‖f z‖` is bounded from above by the same constant on the closed right half-plane.
See also `PhragmenLindelof.right_half_plane_of_bounded_on_real` for a stronger version. -/
theorem right_half_plane_of_tendsto_zero_on_real (hd : DiffContOnCl ℂ f {z | 0 < z.re})
    (hexp : ∃ c < (2 : ℝ), ∃ B,
      f =O[comap Complex.abs atTop ⊓ 𝓟 {z | 0 < z.re}] fun z => expR (B * abs z ^ c))
    (hre : Tendsto (fun x : ℝ => f x) atTop (𝓝 0)) (him : ∀ x : ℝ, ‖f (x * I)‖ ≤ C)
    (hz : 0 ≤ z.re) : ‖f z‖ ≤ C := by
  /- We are going to apply the Phragmen-Lindelöf principle in the first and fourth quadrants.
    The lemmas immediately imply that for any upper estimate `C'` on `‖f x‖`, `x : ℝ`, `0 ≤ x`,
    the number `max C C'` is an upper estimate on `f` in the whole right half-plane. -/
  revert z
  -- ⊢ ∀ {z : ℂ}, 0 ≤ z.re → ‖f z‖ ≤ C
  have hle : ∀ C', (∀ x : ℝ, 0 ≤ x → ‖f x‖ ≤ C') →
      ∀ z : ℂ, 0 ≤ z.re → ‖f z‖ ≤ max C C' := fun C' hC' z hz ↦ by
    rcases hexp with ⟨c, hc, B, hO⟩
    cases' le_total z.im 0 with h h
    · refine quadrant_IV (hd.mono fun _ => And.left) ⟨c, hc, B, ?_⟩
          (fun x hx => (hC' x hx).trans <| le_max_right _ _)
          (fun x _ => (him x).trans (le_max_left _ _)) hz h
      exact hO.mono (inf_le_inf_left _ <| principal_mono.2 fun _ => And.left)
    · refine' quadrant_I (hd.mono fun _ => And.left) ⟨c, hc, B, ?_⟩
          (fun x hx => (hC' x hx).trans <| le_max_right _ _)
          (fun x _ => (him x).trans (le_max_left _ _)) hz h
      exact hO.mono (inf_le_inf_left _ <| principal_mono.2 fun _ => And.left)
  -- Since `f` is continuous on `Ici 0` and `‖f x‖` tends to zero as `x → ∞`,
  -- the norm `‖f x‖` takes its maximum value at some `x₀ : ℝ`.
  obtain ⟨x₀, hx₀, hmax⟩ : ∃ x : ℝ, 0 ≤ x ∧ ∀ y : ℝ, 0 ≤ y → ‖f y‖ ≤ ‖f x‖ := by
    have hfc : ContinuousOn (fun x : ℝ => f x) (Ici 0) := by
      refine' hd.continuousOn.comp continuous_ofReal.continuousOn fun x hx => _
      rwa [closure_setOf_lt_re]
    by_cases h₀ : ∀ x : ℝ, 0 ≤ x → f x = 0
    · refine' ⟨0, le_rfl, fun y hy => _⟩; rw [h₀ y hy, h₀ 0 le_rfl]
    push_neg at h₀
    rcases h₀ with ⟨x₀, hx₀, hne⟩
    have hlt : ‖(0 : E)‖ < ‖f x₀‖ := by rwa [norm_zero, norm_pos_iff]
    suffices ∀ᶠ x : ℝ in cocompact ℝ ⊓ 𝓟 (Ici 0), ‖f x‖ ≤ ‖f x₀‖ by
      simpa only [exists_prop] using hfc.norm.exists_forall_ge' isClosed_Ici hx₀ this
    rw [Real.cocompact_eq, inf_sup_right, (disjoint_atBot_principal_Ici (0 : ℝ)).eq_bot,
      bot_sup_eq]
    exact (hre.norm.eventually <| ge_mem_nhds hlt).filter_mono inf_le_left
  cases' le_or_lt ‖f x₀‖ C with h h
  -- ⊢ ∀ {z : ℂ}, 0 ≤ z.re → ‖f z‖ ≤ C
  ·-- If `‖f x₀‖ ≤ C`, then `hle` implies the required estimate
    simpa only [max_eq_left h] using hle _ hmax
    -- 🎉 no goals
  · -- Otherwise, `‖f z‖ ≤ ‖f x₀‖` for all `z` in the right half-plane due to `hle`.
    replace hmax : IsMaxOn (norm ∘ f) {z | 0 < z.re} x₀
    -- ⊢ IsMaxOn (norm ∘ f) {z | 0 < z.re} ↑x₀
    · rintro z (hz : 0 < z.re)
      -- ⊢ z ∈ {x | (fun x => (norm ∘ f) x ≤ (norm ∘ f) ↑x₀) x}
      simpa [max_eq_right h.le] using hle _ hmax _ hz.le
      -- 🎉 no goals
    -- Due to the maximum modulus principle applied to the closed ball of radius `x₀.re`,
    -- `‖f 0‖ = ‖f x₀‖`.
    have : ‖f 0‖ = ‖f x₀‖ := by
      apply norm_eq_norm_of_isMaxOn_of_ball_subset hd hmax
      -- move to a lemma?
      intro z hz
      rw [mem_ball, dist_zero_left, dist_eq, norm_eq_abs, Complex.abs_of_nonneg hx₀] at hz
      rw [mem_setOf_eq]
      contrapose! hz
      calc
        x₀ ≤ x₀ - z.re := (le_sub_self_iff _).2 hz
        _ ≤ |x₀ - z.re| := (le_abs_self _)
        _ = |(z - x₀).re| := by rw [sub_re, ofReal_re, _root_.abs_sub_comm]
        _ ≤ abs (z - x₀) := abs_re_le_abs _
    -- Thus we have `C < ‖f x₀‖ = ‖f 0‖ ≤ C`. Contradiction completes the proof.
    refine' (h.not_le <| this ▸ _).elim
    -- ⊢ ‖f 0‖ ≤ C
    simpa using him 0
    -- 🎉 no goals
#align phragmen_lindelof.right_half_plane_of_tendsto_zero_on_real PhragmenLindelof.right_half_plane_of_tendsto_zero_on_real

/-- **Phragmen-Lindelöf principle** in the right half-plane. Let `f : ℂ → E` be a function such that

* `f` is differentiable in the open right half-plane and is continuous on its closure;
* `‖f z‖` is bounded from above by `A * exp(B * (abs z) ^ c)` on the open right half-plane
  for some `c < 2`;
* `‖f z‖` is bounded from above by a constant `C` on the imaginary axis;
* `‖f x‖` is bounded from above by a constant for large real values of `x`.

Then `‖f z‖` is bounded from above by `C` on the closed right half-plane.
See also `PhragmenLindelof.right_half_plane_of_tendsto_zero_on_real` for a weaker version. -/
theorem right_half_plane_of_bounded_on_real (hd : DiffContOnCl ℂ f {z | 0 < z.re})
    (hexp : ∃ c < (2 : ℝ), ∃ B,
      f =O[comap Complex.abs atTop ⊓ 𝓟 {z | 0 < z.re}] fun z => expR (B * abs z ^ c))
    (hre : IsBoundedUnder (· ≤ ·) atTop fun x : ℝ => ‖f x‖) (him : ∀ x : ℝ, ‖f (x * I)‖ ≤ C)
    (hz : 0 ≤ z.re) : ‖f z‖ ≤ C := by
  -- For each `ε < 0`, the function `fun z ↦ exp (ε * z) • f z` satisfies assumptions of
  -- `right_half_plane_of_tendsto_zero_on_real`, hence `‖exp (ε * z) • f z‖ ≤ C` for all `ε < 0`.
  -- Taking the limit as `ε → 0`, we obtain the required inequality.
  suffices ∀ᶠ ε : ℝ in 𝓝[<] 0, ‖exp (ε * z) • f z‖ ≤ C by
    refine' le_of_tendsto (Tendsto.mono_left _ nhdsWithin_le_nhds) this
    apply ((continuous_ofReal.mul continuous_const).cexp.smul continuous_const).norm.tendsto'
    simp
  filter_upwards [self_mem_nhdsWithin] with ε ε₀; change ε < 0 at ε₀
  -- ⊢ ‖exp (↑ε * z) • f z‖ ≤ C
                                                  -- ⊢ ‖exp (↑ε * z) • f z‖ ≤ C
  set g : ℂ → E := fun z => exp (ε * z) • f z; change ‖g z‖ ≤ C
  -- ⊢ ‖exp (↑ε * z) • f z‖ ≤ C
                                               -- ⊢ ‖g z‖ ≤ C
  replace hd : DiffContOnCl ℂ g {z : ℂ | 0 < z.re}
  -- ⊢ DiffContOnCl ℂ g {z | 0 < z.re}
  exact (differentiable_id.const_mul _).cexp.diffContOnCl.smul hd
  -- ⊢ ‖g z‖ ≤ C
  have hgn : ∀ z, ‖g z‖ = expR (ε * z.re) * ‖f z‖ := fun z ↦ by
    rw [norm_smul, norm_eq_abs, abs_exp, ofReal_mul_re]
  refine' right_half_plane_of_tendsto_zero_on_real hd _ _ (fun y => _) hz
  · rcases hexp with ⟨c, hc, B, hO⟩
    -- ⊢ ∃ c, c < 2 ∧ ∃ B, g =O[comap (↑Complex.abs) atTop ⊓ 𝓟 {z | 0 < z.re}] fun z  …
    refine ⟨c, hc, B, (IsBigO.of_bound 1 ?_).trans hO⟩
    -- ⊢ ∀ᶠ (x : ℂ) in comap (↑Complex.abs) atTop ⊓ 𝓟 {z | 0 < z.re}, ‖g x‖ ≤ 1 * ‖f x‖
    refine' eventually_inf_principal.2 <| eventually_of_forall fun z hz => _
    -- ⊢ ‖g z‖ ≤ 1 * ‖f z‖
    rw [hgn, one_mul]
    -- ⊢ expR (ε * z.re) * ‖f z‖ ≤ ‖f z‖
    refine' mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.2 _)
    -- ⊢ ε * z.re ≤ 0
    exact mul_nonpos_of_nonpos_of_nonneg ε₀.le (le_of_lt hz)
    -- 🎉 no goals
  · simp_rw [← ofReal_mul, ← ofReal_exp, coe_smul]
    -- ⊢ Tendsto (fun x => expR (ε * x) • f ↑x) atTop (𝓝 0)
    have h₀ : Tendsto (fun x : ℝ => expR (ε * x)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_const_nhds.neg_mul_atTop ε₀ tendsto_id)
    exact h₀.zero_smul_isBoundedUnder_le hre
    -- 🎉 no goals
  · rw [hgn, ofReal_mul_re, I_re, mul_zero, mul_zero, Real.exp_zero,
      one_mul]
    exact him y
    -- 🎉 no goals
#align phragmen_lindelof.right_half_plane_of_bounded_on_real PhragmenLindelof.right_half_plane_of_bounded_on_real

/-- **Phragmen-Lindelöf principle** in the right half-plane. Let `f : ℂ → E` be a function such that

* `f` is differentiable in the open right half-plane and is continuous on its closure;
* `‖f z‖` is bounded from above by `A * exp(B * (abs z) ^ c)` on the open right half-plane
  for some `c < 2`;
* `‖f z‖` is bounded from above by a constant on the imaginary axis;
* `f x`, `x : ℝ`, tends to zero superexponentially fast as `x → ∞`:
  for any natural `n`, `exp (n * x) * ‖f x‖` tends to zero as `x → ∞`.

Then `f` is equal to zero on the closed right half-plane. -/
theorem eq_zero_on_right_half_plane_of_superexponential_decay (hd : DiffContOnCl ℂ f {z | 0 < z.re})
    (hexp : ∃ c < (2 : ℝ), ∃ B,
      f =O[comap Complex.abs atTop ⊓ 𝓟 {z | 0 < z.re}] fun z => expR (B * abs z ^ c))
    (hre : SuperpolynomialDecay atTop expR fun x => ‖f x‖) (him : ∃ C, ∀ x : ℝ, ‖f (x * I)‖ ≤ C) :
    EqOn f 0 {z : ℂ | 0 ≤ z.re} := by
  rcases him with ⟨C, hC⟩
  -- ⊢ EqOn f 0 {z | 0 ≤ z.re}
  -- Due to continuity, it suffices to prove the equality on the open right half-plane.
  suffices ∀ z : ℂ, 0 < z.re → f z = 0 by
    simpa only [closure_setOf_lt_re] using
      EqOn.of_subset_closure this hd.continuousOn continuousOn_const subset_closure Subset.rfl
  -- Consider $g_n(z)=e^{nz}f(z)$.
  set g : ℕ → ℂ → E := fun (n : ℕ) (z : ℂ) => exp z ^ n • f z
  -- ⊢ ∀ (z : ℂ), 0 < z.re → f z = 0
  have hg : ∀ n z, ‖g n z‖ = expR z.re ^ n * ‖f z‖ := fun n z ↦ by
    simp only [norm_smul, norm_eq_abs, Complex.abs_pow, abs_exp]
  intro z hz
  -- ⊢ f z = 0
  -- Since `e^{nz} → ∞` as `n → ∞`, it suffices to show that each `g_n` is bounded from above by `C`
  suffices H : ∀ n : ℕ, ‖g n z‖ ≤ C
  -- ⊢ f z = 0
  · contrapose! H
    -- ⊢ ∃ n, C < ‖(fun n z => exp z ^ n • f z) n z‖
    simp only [hg]
    -- ⊢ ∃ n, C < expR z.re ^ n * ‖f z‖
    exact (((tendsto_pow_atTop_atTop_of_one_lt (Real.one_lt_exp_iff.2 hz)).atTop_mul
      (norm_pos_iff.2 H) tendsto_const_nhds).eventually (eventually_gt_atTop C)).exists
  intro n
  -- ⊢ ‖g n z‖ ≤ C
  -- This estimate follows from the Phragmen-Lindelöf principle in the right half-plane.
  refine' right_half_plane_of_tendsto_zero_on_real ((differentiable_exp.pow n).diffContOnCl.smul hd)
    _ _ (fun y => _) hz.le
  · rcases hexp with ⟨c, hc, B, hO⟩
    -- ⊢ ∃ c, c < 2 ∧ ∃ B, g n =O[comap (↑Complex.abs) atTop ⊓ 𝓟 {z | 0 < z.re}] fun  …
    refine' ⟨max c 1, max_lt hc one_lt_two, n + max B 0, .of_norm_left _⟩
    -- ⊢ (fun x => ‖g n x‖) =O[comap (↑Complex.abs) atTop ⊓ 𝓟 {z | 0 < z.re}] fun z = …
    simp only [hg]
    -- ⊢ (fun x => expR x.re ^ n * ‖f x‖) =O[comap (↑Complex.abs) atTop ⊓ 𝓟 {z | 0 <  …
    refine' ((isBigO_refl (fun z : ℂ => expR z.re ^ n) _).mul hO.norm_left).trans (.of_bound 1 _)
    -- ⊢ ∀ᶠ (x : ℂ) in comap (↑Complex.abs) atTop ⊓ 𝓟 {z | 0 < z.re}, ‖expR x.re ^ n  …
    simp only [← Real.exp_nat_mul, ← Real.exp_add, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.exp_le_exp, add_mul, eventually_inf_principal, eventually_comap, one_mul]
    -- porting note: todo: `0 < z.re` is not used; where do we use it?
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr z hzr _; subst r
    -- ⊢ ↑n * z.re + B * ↑Complex.abs z ^ c ≤ ↑n * ↑Complex.abs z ^ max c 1 + max B 0 …
                                                                    -- ⊢ ↑n * z.re + B * ↑Complex.abs z ^ c ≤ ↑n * ↑Complex.abs z ^ max c 1 + max B 0 …
    refine' add_le_add (mul_le_mul_of_nonneg_left _ n.cast_nonneg) _
    -- ⊢ z.re ≤ ↑Complex.abs z ^ max c 1
    · calc
        z.re ≤ abs z := re_le_abs _
        _ = abs z ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ abs z ^ max c 1 := Real.rpow_le_rpow_of_exponent_le hr (le_max_right _ _)
    · exact mul_le_mul (le_max_left _ _) (Real.rpow_le_rpow_of_exponent_le hr (le_max_left _ _))
        (Real.rpow_nonneg_of_nonneg (Complex.abs.nonneg _) _) (le_max_right _ _)
  · rw [tendsto_zero_iff_norm_tendsto_zero]; simp only [hg]
    -- ⊢ Tendsto (fun e => ‖g n ↑e‖) atTop (𝓝 0)
                                             -- ⊢ Tendsto (fun e => expR (↑e).re ^ n * ‖f ↑e‖) atTop (𝓝 0)
    exact hre n
    -- 🎉 no goals
  · rw [hg, ofReal_mul_re, I_re, mul_zero, Real.exp_zero, one_pow, one_mul]
    -- ⊢ ‖f (↑y * I)‖ ≤ C
    exact hC y
    -- 🎉 no goals
#align phragmen_lindelof.eq_zero_on_right_half_plane_of_superexponential_decay PhragmenLindelof.eq_zero_on_right_half_plane_of_superexponential_decay

/-- **Phragmen-Lindelöf principle** in the right half-plane. Let `f g : ℂ → E` be functions such
that

* `f` and `g` are differentiable in the open right half-plane and are continuous on its closure;
* `‖f z‖` and `‖g z‖` are bounded from above by `A * exp(B * (abs z) ^ c)` on the open right
  half-plane for some `c < 2`;
* `‖f z‖` and `‖g z‖` are bounded from above by constants on the imaginary axis;
* `f x - g x`, `x : ℝ`, tends to zero superexponentially fast as `x → ∞`:
  for any natural `n`, `exp (n * x) * ‖f x - g x‖` tends to zero as `x → ∞`.

Then `f` is equal to `g` on the closed right half-plane. -/
theorem eqOn_right_half_plane_of_superexponential_decay {g : ℂ → E}
    (hfd : DiffContOnCl ℂ f {z | 0 < z.re}) (hgd : DiffContOnCl ℂ g {z | 0 < z.re})
    (hfexp : ∃ c < (2 : ℝ), ∃ B,
      f =O[comap Complex.abs atTop ⊓ 𝓟 {z | 0 < z.re}] fun z => expR (B * abs z ^ c))
    (hgexp : ∃ c < (2 : ℝ), ∃ B,
      g =O[comap Complex.abs atTop ⊓ 𝓟 {z | 0 < z.re}] fun z => expR (B * abs z ^ c))
    (hre : SuperpolynomialDecay atTop expR fun x => ‖f x - g x‖)
    (hfim : ∃ C, ∀ x : ℝ, ‖f (x * I)‖ ≤ C) (hgim : ∃ C, ∀ x : ℝ, ‖g (x * I)‖ ≤ C) :
    EqOn f g {z : ℂ | 0 ≤ z.re} := by
  suffices EqOn (f - g) 0 {z : ℂ | 0 ≤ z.re} by
    simpa only [EqOn, Pi.sub_apply, Pi.zero_apply, sub_eq_zero] using this
  refine' eq_zero_on_right_half_plane_of_superexponential_decay (hfd.sub hgd) _ hre _
  -- ⊢ ∃ c, c < 2 ∧ ∃ B, (f - g) =O[comap (↑Complex.abs) atTop ⊓ 𝓟 {z | 0 < z.re}]  …
  · set l : Filter ℂ := comap Complex.abs atTop ⊓ 𝓟 {z : ℂ | 0 < z.re}
    -- ⊢ ∃ c, c < 2 ∧ ∃ B, (f - g) =O[l] fun z => expR (B * ↑Complex.abs z ^ c)
    suffices ∀ {c₁ c₂ B₁ B₂ : ℝ}, c₁ ≤ c₂ → B₁ ≤ B₂ → 0 ≤ B₂ →
        (fun z => expR (B₁ * abs z ^ c₁)) =O[l] fun z => expR (B₂ * abs z ^ c₂) by
      rcases hfexp with ⟨cf, hcf, Bf, hOf⟩; rcases hgexp with ⟨cg, hcg, Bg, hOg⟩
      refine' ⟨max cf cg, max_lt hcf hcg, max 0 (max Bf Bg), _⟩
      refine' .sub (hOf.trans <| this _ _ _) (hOg.trans <| this _ _ _) <;> simp
    intro c₁ c₂ B₁ B₂ hc hB hB₂
    -- ⊢ (fun z => expR (B₁ * ↑Complex.abs z ^ c₁)) =O[l] fun z => expR (B₂ * ↑Comple …
    have : ∀ᶠ z : ℂ in l, 1 ≤ abs z := ((eventually_ge_atTop 1).comap _).filter_mono inf_le_left
    -- ⊢ (fun z => expR (B₁ * ↑Complex.abs z ^ c₁)) =O[l] fun z => expR (B₂ * ↑Comple …
    refine' .of_bound 1 (this.mono fun z hz => _)
    -- ⊢ ‖expR (B₁ * ↑Complex.abs z ^ c₁)‖ ≤ 1 * ‖expR (B₂ * ↑Complex.abs z ^ c₂)‖
    simp only [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_exp, one_mul]
    -- ⊢ B₁ * ↑Complex.abs z ^ c₁ ≤ B₂ * ↑Complex.abs z ^ c₂
    have := Real.rpow_le_rpow_of_exponent_le hz hc
    -- ⊢ B₁ * ↑Complex.abs z ^ c₁ ≤ B₂ * ↑Complex.abs z ^ c₂
    gcongr
    -- 🎉 no goals
  · rcases hfim with ⟨Cf, hCf⟩; rcases hgim with ⟨Cg, hCg⟩
    -- ⊢ ∃ C, ∀ (x : ℝ), ‖(f - g) (↑x * I)‖ ≤ C
                                -- ⊢ ∃ C, ∀ (x : ℝ), ‖(f - g) (↑x * I)‖ ≤ C
    exact ⟨Cf + Cg, fun x => norm_sub_le_of_le (hCf x) (hCg x)⟩
    -- 🎉 no goals
#align phragmen_lindelof.eq_on_right_half_plane_of_superexponential_decay PhragmenLindelof.eqOn_right_half_plane_of_superexponential_decay

end PhragmenLindelof
