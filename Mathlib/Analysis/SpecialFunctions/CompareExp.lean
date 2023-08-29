/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

#align_import analysis.special_functions.compare_exp from "leanprover-community/mathlib"@"0b9eaaa7686280fad8cce467f5c3c57ee6ce77f8"

/-!
# Growth estimates on `x ^ y` for complex `x`, `y`

Let `l` be a filter on `ℂ` such that `Complex.re` tends to infinity along `l` and `Complex.im z`
grows at a subexponential rate compared to `Complex.re z`. Then

- `Complex.isLittleO_log_abs_re`: `Real.log ∘ Complex.abs` is `o`-small of
  `Complex.re` along `l`;

- `Complex.isLittleO_cpow_mul_exp`: $z^{a_1}e^{b_1 * z} = o\left(z^{a_1}e^{b_1 * z}\right)$
  along `l` for any complex `a₁`, `a₂` and real `b₁ < b₂`.

We use these assumptions on `l` for two reasons. First, these are the assumptions that naturally
appear in the proof. Second, in some applications (e.g., in Ilyashenko's proof of the individual
finiteness theorem for limit cycles of polynomial ODEs with hyperbolic singularities only) natural
stronger assumptions (e.g., `im z` is bounded from below and from above) are not available.

-/


open Asymptotics Filter Function

open Topology

namespace Complex

/-- We say that `l : Filter ℂ` is an *exponential comparison filter* if the real part tends to
infinity along `l` and the imaginary part grows subexponentially compared to the real part. These
properties guarantee that `(fun z ↦ z ^ a₁ * exp (b₁ * z)) =o[l] (fun z ↦ z ^ a₂ * exp (b₂ * z))`
for any complex `a₁`, `a₂` and real `b₁ < b₂`.

In particular, the second property is automatically satisfied if the imaginary part is bounded along
`l`. -/
structure IsExpCmpFilter (l : Filter ℂ) : Prop where
  tendsto_re : Tendsto re l atTop
  isBigO_im_pow_re : ∀ n : ℕ, (fun z : ℂ => z.im ^ n) =O[l] fun z => Real.exp z.re
#align complex.is_exp_cmp_filter Complex.IsExpCmpFilter

namespace IsExpCmpFilter

variable {l : Filter ℂ}

/-!
### Alternative constructors
-/


theorem of_isBigO_im_re_rpow (hre : Tendsto re l atTop) (r : ℝ) (hr : im =O[l] fun z => z.re ^ r) :
    IsExpCmpFilter l :=
  ⟨hre, fun n =>
    IsLittleO.isBigO <|
      calc
        (fun z : ℂ => z.im ^ n) =O[l] fun z => (z.re ^ r) ^ n := by norm_cast; exact hr.pow n
                                                                    -- ⊢ (fun z => z.im ^ n) =O[l] fun z => (z.re ^ r) ^ n
                                                                               -- 🎉 no goals
        _ =ᶠ[l] fun z => z.re ^ (r * n) :=
          ((hre.eventually_ge_atTop 0).mono fun z hz => by
            simp only [Real.rpow_mul hz r n, Real.rpow_nat_cast])
            -- 🎉 no goals
        _ =o[l] fun z => Real.exp z.re := (isLittleO_rpow_exp_atTop _).comp_tendsto hre ⟩
set_option linter.uppercaseLean3 false in
#align complex.is_exp_cmp_filter.of_is_O_im_re_rpow Complex.IsExpCmpFilter.of_isBigO_im_re_rpow

theorem of_isBigO_im_re_pow (hre : Tendsto re l atTop) (n : ℕ) (hr : im =O[l] fun z => z.re ^ n) :
    IsExpCmpFilter l :=
  of_isBigO_im_re_rpow hre n <| by norm_cast at hr; simpa only [Real.rpow_nat_cast]
                                   -- ⊢ im =O[l] fun z => z.re ^ ↑n
                                                    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align complex.is_exp_cmp_filter.of_is_O_im_re_pow Complex.IsExpCmpFilter.of_isBigO_im_re_pow

theorem of_boundedUnder_abs_im (hre : Tendsto re l atTop)
    (him : IsBoundedUnder (· ≤ ·) l fun z => |z.im|) : IsExpCmpFilter l :=
  of_isBigO_im_re_pow hre 0 <| by
    norm_cast
    -- ⊢ im =O[l] fun z => z.re ^ 0
    simpa only [pow_zero] using @IsBoundedUnder.isBigO_const ℂ ℝ ℝ _ _ _ l him 1 one_ne_zero
    -- 🎉 no goals
#align complex.is_exp_cmp_filter.of_bounded_under_abs_im Complex.IsExpCmpFilter.of_boundedUnder_abs_im

theorem of_boundedUnder_im (hre : Tendsto re l atTop) (him_le : IsBoundedUnder (· ≤ ·) l im)
    (him_ge : IsBoundedUnder (· ≥ ·) l im) : IsExpCmpFilter l :=
  of_boundedUnder_abs_im hre <| isBoundedUnder_le_abs.2 ⟨him_le, him_ge⟩
#align complex.is_exp_cmp_filter.of_bounded_under_im Complex.IsExpCmpFilter.of_boundedUnder_im

/-!
### Preliminary lemmas
-/


theorem eventually_ne (hl : IsExpCmpFilter l) : ∀ᶠ w : ℂ in l, w ≠ 0 :=
  hl.tendsto_re.eventually_ne_atTop' _
#align complex.is_exp_cmp_filter.eventually_ne Complex.IsExpCmpFilter.eventually_ne

theorem tendsto_abs_re (hl : IsExpCmpFilter l) : Tendsto (fun z : ℂ => |z.re|) l atTop :=
  tendsto_abs_atTop_atTop.comp hl.tendsto_re
#align complex.is_exp_cmp_filter.tendsto_abs_re Complex.IsExpCmpFilter.tendsto_abs_re

theorem tendsto_abs (hl : IsExpCmpFilter l) : Tendsto abs l atTop :=
  tendsto_atTop_mono abs_re_le_abs hl.tendsto_abs_re
#align complex.is_exp_cmp_filter.tendsto_abs Complex.IsExpCmpFilter.tendsto_abs

theorem isLittleO_log_re_re (hl : IsExpCmpFilter l) : (fun z => Real.log z.re) =o[l] re :=
  Real.isLittleO_log_id_atTop.comp_tendsto hl.tendsto_re
#align complex.is_exp_cmp_filter.is_o_log_re_re Complex.IsExpCmpFilter.isLittleO_log_re_re

theorem isLittleO_im_pow_exp_re (hl : IsExpCmpFilter l) (n : ℕ) :
    (fun z : ℂ => z.im ^ n) =o[l] fun z => Real.exp z.re :=
  flip IsLittleO.of_pow two_ne_zero <|
    calc
      ((fun z : ℂ => (z.im ^ n)) ^ 2) = (fun z : ℂ => (z.im ^ n) ^ 2) := funext <| by simp
                                                                                      -- 🎉 no goals
      _ = fun z => (Complex.im z) ^ (2 * n) := funext <| fun _ => by norm_cast; rw [pow_mul']
                                                                     -- ⊢ (x✝.im ^ n) ^ 2 = x✝.im ^ (2 * n)
                                                                                -- 🎉 no goals
      _ =O[l] fun z => Real.exp z.re := by have := hl.isBigO_im_pow_re (2 * n); norm_cast at *
                                           -- ⊢ (fun z => z.im ^ (2 * ↑n)) =O[l] fun z => Real.exp z.re
                                                                                -- 🎉 no goals
      _ = fun z => Real.exp z.re ^ 1 := funext <| fun _ => by norm_cast; rw [pow_one]
                                                              -- ⊢ Real.exp x✝.re = Real.exp x✝.re ^ 1
                                                                         -- 🎉 no goals
      _ =o[l] fun z => Real.exp z.re ^ 2 := by
        have := (isLittleO_pow_pow_atTop_of_lt one_lt_two).comp_tendsto <|
          Real.tendsto_exp_atTop.comp hl.tendsto_re
        simpa only [pow_one, Real.rpow_one, Real.rpow_two]
        -- 🎉 no goals
      _ = (fun z => Real.exp z.re) ^ 2 := funext <| by simp
                                                       -- 🎉 no goals
#align complex.is_exp_cmp_filter.is_o_im_pow_exp_re Complex.IsExpCmpFilter.isLittleO_im_pow_exp_re

theorem abs_im_pow_eventuallyLE_exp_re (hl : IsExpCmpFilter l) (n : ℕ) :
    (fun z : ℂ => |z.im| ^ n) ≤ᶠ[l] fun z => Real.exp z.re := by
  simpa using (hl.isLittleO_im_pow_exp_re n).bound zero_lt_one
  -- 🎉 no goals
#align complex.is_exp_cmp_filter.abs_im_pow_eventually_le_exp_re Complex.IsExpCmpFilter.abs_im_pow_eventuallyLE_exp_re

/-- If `l : Filter ℂ` is an "exponential comparison filter", then $\log |z| =o(ℜ z)$ along `l`.
This is the main lemma in the proof of `Complex.IsExpCmpFilter.isLittleO_cpow_exp` below.
-/
theorem isLittleO_log_abs_re (hl : IsExpCmpFilter l) : (fun z => Real.log (abs z)) =o[l] re :=
  calc
    (fun z => Real.log (abs z)) =O[l] fun z =>
        Real.log (Real.sqrt 2) + Real.log (max z.re |z.im|) :=
      IsBigO.of_bound 1 <|
        (hl.tendsto_re.eventually_ge_atTop 1).mono fun z hz => by
          have h2 : 0 < Real.sqrt 2 := by simp
          -- ⊢ ‖Real.log (↑abs z)‖ ≤ 1 * ‖Real.log (Real.sqrt 2) + Real.log (max z.re |z.im …
          have hz' : 1 ≤ abs z := hz.trans (re_le_abs z)
          -- ⊢ ‖Real.log (↑abs z)‖ ≤ 1 * ‖Real.log (Real.sqrt 2) + Real.log (max z.re |z.im …
          have _ : 0 < abs z := one_pos.trans_le hz'
          -- ⊢ ‖Real.log (↑abs z)‖ ≤ 1 * ‖Real.log (Real.sqrt 2) + Real.log (max z.re |z.im …
          have hm₀ : 0 < max z.re |z.im| := lt_max_iff.2 (Or.inl <| one_pos.trans_le hz)
          -- ⊢ ‖Real.log (↑abs z)‖ ≤ 1 * ‖Real.log (Real.sqrt 2) + Real.log (max z.re |z.im …
          rw [one_mul, Real.norm_eq_abs, _root_.abs_of_nonneg (Real.log_nonneg hz')]
          -- ⊢ Real.log (↑abs z) ≤ ‖Real.log (Real.sqrt 2) + Real.log (max z.re |z.im|)‖
          refine' le_trans _ (le_abs_self _)
          -- ⊢ Real.log (↑abs z) ≤ Real.log (Real.sqrt 2) + Real.log (max z.re |z.im|)
          rw [← Real.log_mul, Real.log_le_log, ← _root_.abs_of_nonneg (le_trans zero_le_one hz)]
          exacts [abs_le_sqrt_two_mul_max z, one_pos.trans_le hz', mul_pos h2 hm₀, h2.ne', hm₀.ne']
          -- 🎉 no goals
    _ =o[l] re :=
      IsLittleO.add (isLittleO_const_left.2 <| Or.inr <| hl.tendsto_abs_re) <|
        isLittleO_iff_nat_mul_le.2 fun n => by
          filter_upwards [isLittleO_iff_nat_mul_le'.1 hl.isLittleO_log_re_re n,
            hl.abs_im_pow_eventuallyLE_exp_re n,
            hl.tendsto_re.eventually_gt_atTop 1] with z hre him h₁
          cases' le_total |z.im| z.re with hle hle
          -- ⊢ ↑n * ‖Real.log (max z.re |z.im|)‖ ≤ ‖z.re‖
          · rwa [max_eq_left hle]
            -- 🎉 no goals
          · have H : 1 < |z.im| := h₁.trans_le hle
            -- ⊢ ↑n * ‖Real.log (max z.re |z.im|)‖ ≤ ‖z.re‖
            norm_cast at *
            -- ⊢ ↑n * ‖Real.log (max z.re |z.im|)‖ ≤ ‖z.re‖
            rwa [max_eq_right hle, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.log_pos H),
              ← Real.log_pow, Real.log_le_iff_le_exp (pow_pos (one_pos.trans H) _),
              abs_of_pos (one_pos.trans h₁)]
#align complex.is_exp_cmp_filter.is_o_log_abs_re Complex.IsExpCmpFilter.isLittleO_log_abs_re

/-!
### Main results
-/


/-- If `l : Filter ℂ` is an "exponential comparison filter", then for any complex `a` and any
positive real `b`, we have `(fun z ↦ z ^ a) =o[l] (fun z ↦ exp (b * z))`. -/
theorem isLittleO_cpow_exp (hl : IsExpCmpFilter l) (a : ℂ) {b : ℝ} (hb : 0 < b) :
    (fun z => z ^ a) =o[l] fun z => exp (b * z) :=
  -- Porting note: Added `show ℂ → ℝ from`
  calc
    (fun z => z ^ a) =Θ[l] (show ℂ → ℝ from fun z => (abs z ^ re a)) :=
      isTheta_cpow_const_rpow fun _ _ => hl.eventually_ne
    _ =ᶠ[l] fun z => Real.exp (re a * Real.log (abs z)) :=
      (hl.eventually_ne.mono fun z hz => by simp only [Real.rpow_def_of_pos, abs.pos hz, mul_comm])
                                            -- 🎉 no goals
    _ =o[l] fun z => exp (b * z) :=
      IsLittleO.of_norm_right <| by
        simp only [norm_eq_abs, abs_exp, ofReal_mul_re, Real.isLittleO_exp_comp_exp_comp]
        -- ⊢ Tendsto (fun x => b * x.re - a.re * Real.log (↑abs x)) l atTop
        refine'
          (IsEquivalent.refl.sub_isLittleO _).symm.tendsto_atTop (hl.tendsto_re.const_mul_atTop hb)
        exact (hl.isLittleO_log_abs_re.const_mul_left _).const_mul_right hb.ne'
        -- 🎉 no goals
#align complex.is_exp_cmp_filter.is_o_cpow_exp Complex.IsExpCmpFilter.isLittleO_cpow_exp

/-- If `l : Filter ℂ` is an "exponential comparison filter", then for any complex `a₁`, `a₂` and any
real `b₁ < b₂`, we have `(fun z ↦ z ^ a₁ * exp (b₁ * z)) =o[l] (fun z ↦ z ^ a₂ * exp (b₂ * z))`. -/
theorem isLittleO_cpow_mul_exp {b₁ b₂ : ℝ} (hl : IsExpCmpFilter l) (hb : b₁ < b₂) (a₁ a₂ : ℂ) :
    (fun z => z ^ a₁ * exp (b₁ * z)) =o[l] fun z => z ^ a₂ * exp (b₂ * z) :=
  calc
    (fun z => z ^ a₁ * exp (b₁ * z)) =ᶠ[l] fun z => z ^ a₂ * exp (b₁ * z) * z ^ (a₁ - a₂) :=
      hl.eventually_ne.mono fun z hz => by
        simp only
        -- ⊢ z ^ a₁ * exp (↑b₁ * z) = z ^ a₂ * exp (↑b₁ * z) * z ^ (a₁ - a₂)
        rw [mul_right_comm, ← cpow_add _ _ hz, add_sub_cancel'_right]
        -- 🎉 no goals
    _ =o[l] fun z => z ^ a₂ * exp (b₁ * z) * exp (↑(b₂ - b₁) * z) :=
      ((isBigO_refl (fun z => z ^ a₂ * exp (b₁ * z)) l).mul_isLittleO <|
        hl.isLittleO_cpow_exp _ (sub_pos.2 hb))
    _ =ᶠ[l] fun z => z ^ a₂ * exp (b₂ * z) := by
      simp only [ofReal_sub, sub_mul, mul_assoc, ← exp_add, add_sub_cancel'_right]
      -- ⊢ (fun z => z ^ a₂ * exp (↑b₂ * z)) =ᶠ[l] fun z => z ^ a₂ * exp (↑b₂ * z)
      norm_cast
      -- 🎉 no goals
#align complex.is_exp_cmp_filter.is_o_cpow_mul_exp Complex.IsExpCmpFilter.isLittleO_cpow_mul_exp

/-- If `l : Filter ℂ` is an "exponential comparison filter", then for any complex `a` and any
negative real `b`, we have `(fun z ↦ exp (b * z)) =o[l] (fun z ↦ z ^ a)`. -/
theorem isLittleO_exp_cpow (hl : IsExpCmpFilter l) (a : ℂ) {b : ℝ} (hb : b < 0) :
    (fun z => exp (b * z)) =o[l] fun z => z ^ a := by simpa using hl.isLittleO_cpow_mul_exp hb 0 a
                                                      -- 🎉 no goals
#align complex.is_exp_cmp_filter.is_o_exp_cpow Complex.IsExpCmpFilter.isLittleO_exp_cpow

/-- If `l : Filter ℂ` is an "exponential comparison filter", then for any complex `a₁`, `a₂` and any
natural `b₁ < b₂`, we have
`(fun z ↦ z ^ a₁ * exp (b₁ * z)) =o[l] (fun z ↦ z ^ a₂ * exp (b₂ * z))`. -/
theorem isLittleO_pow_mul_exp {b₁ b₂ : ℝ} (hl : IsExpCmpFilter l) (hb : b₁ < b₂) (m n : ℕ) :
    (fun z => z ^ m * exp (b₁ * z)) =o[l] fun z => z ^ n * exp (b₂ * z) := by
  simpa only [cpow_nat_cast] using hl.isLittleO_cpow_mul_exp hb m n
  -- 🎉 no goals
#align complex.is_exp_cmp_filter.is_o_pow_mul_exp Complex.IsExpCmpFilter.isLittleO_pow_mul_exp

/-- If `l : Filter ℂ` is an "exponential comparison filter", then for any complex `a₁`, `a₂` and any
integer `b₁ < b₂`, we have
`(fun z ↦ z ^ a₁ * exp (b₁ * z)) =o[l] (fun z ↦ z ^ a₂ * exp (b₂ * z))`. -/
theorem isLittleO_zpow_mul_exp {b₁ b₂ : ℝ} (hl : IsExpCmpFilter l) (hb : b₁ < b₂) (m n : ℤ) :
    (fun z => z ^ m * exp (b₁ * z)) =o[l] fun z => z ^ n * exp (b₂ * z) := by
  simpa only [cpow_int_cast] using hl.isLittleO_cpow_mul_exp hb m n
  -- 🎉 no goals
#align complex.is_exp_cmp_filter.is_o_zpow_mul_exp Complex.IsExpCmpFilter.isLittleO_zpow_mul_exp

end IsExpCmpFilter

end Complex
