/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

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
open scoped Topology

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
        (fun z : ℂ => z.im ^ n) =O[l] fun z => (z.re ^ r) ^ n := hr.pow n
        _ =ᶠ[l] fun z => z.re ^ (r * n) :=
          ((hre.eventually_ge_atTop 0).mono fun z hz => by
            simp only [Real.rpow_mul hz r n, Real.rpow_natCast])
        _ =o[l] fun z => Real.exp z.re := (isLittleO_rpow_exp_atTop _).comp_tendsto hre ⟩

theorem of_isBigO_im_re_pow (hre : Tendsto re l atTop) (n : ℕ) (hr : im =O[l] fun z => z.re ^ n) :
    IsExpCmpFilter l :=
  of_isBigO_im_re_rpow hre n <| mod_cast hr

theorem of_boundedUnder_abs_im (hre : Tendsto re l atTop)
    (him : IsBoundedUnder (· ≤ ·) l fun z => |z.im|) : IsExpCmpFilter l :=
  of_isBigO_im_re_pow hre 0 <| by
    simpa only [pow_zero] using him.isBigO_const (f := im) one_ne_zero

theorem of_boundedUnder_im (hre : Tendsto re l atTop) (him_le : IsBoundedUnder (· ≤ ·) l im)
    (him_ge : IsBoundedUnder (· ≥ ·) l im) : IsExpCmpFilter l :=
  of_boundedUnder_abs_im hre <| isBoundedUnder_le_abs.2 ⟨him_le, him_ge⟩

/-!
### Preliminary lemmas
-/

theorem eventually_ne (hl : IsExpCmpFilter l) : ∀ᶠ w : ℂ in l, w ≠ 0 :=
  hl.tendsto_re.eventually_ne_atTop' _

theorem tendsto_abs_re (hl : IsExpCmpFilter l) : Tendsto (fun z : ℂ => |z.re|) l atTop :=
  tendsto_abs_atTop_atTop.comp hl.tendsto_re

theorem tendsto_norm (hl : IsExpCmpFilter l) : Tendsto norm l atTop :=
  tendsto_atTop_mono abs_re_le_norm hl.tendsto_abs_re

theorem isLittleO_log_re_re (hl : IsExpCmpFilter l) : (fun z => Real.log z.re) =o[l] re :=
  Real.isLittleO_log_id_atTop.comp_tendsto hl.tendsto_re

theorem isLittleO_im_pow_exp_re (hl : IsExpCmpFilter l) (n : ℕ) :
    (fun z : ℂ => z.im ^ n) =o[l] fun z => Real.exp z.re :=
  flip IsLittleO.of_pow two_ne_zero <|
    calc
      (fun z : ℂ ↦ (z.im ^ n) ^ 2) = (fun z ↦ z.im ^ (2 * n)) := by simp only [pow_mul']
      _ =O[l] fun z ↦ Real.exp z.re := hl.isBigO_im_pow_re _
      _ =     fun z ↦ (Real.exp z.re) ^ 1 := by simp only [pow_one]
      _ =o[l] fun z ↦ (Real.exp z.re) ^ 2 :=
        (isLittleO_pow_pow_atTop_of_lt one_lt_two).comp_tendsto <|
          Real.tendsto_exp_atTop.comp hl.tendsto_re

theorem abs_im_pow_eventuallyLE_exp_re (hl : IsExpCmpFilter l) (n : ℕ) :
    (fun z : ℂ => |z.im| ^ n) ≤ᶠ[l] fun z => Real.exp z.re := by
  simpa using (hl.isLittleO_im_pow_exp_re n).bound zero_lt_one

/-- If `l : Filter ℂ` is an "exponential comparison filter", then $\log |z| =o(ℜ z)$ along `l`.
This is the main lemma in the proof of `Complex.IsExpCmpFilter.isLittleO_cpow_exp` below.
-/
theorem isLittleO_log_norm_re (hl : IsExpCmpFilter l) : (fun z => Real.log ‖z‖) =o[l] re :=
  calc
    (fun z => Real.log ‖z‖) =O[l] fun z => Real.log (√2) + Real.log (max z.re |z.im|) :=
      .of_norm_eventuallyLE <|
        (hl.tendsto_re.eventually_ge_atTop 1).mono fun z hz => by
          have h2 : 0 < √2 := by simp
          have hz' : 1 ≤ ‖z‖ := hz.trans (re_le_norm z)
          have hm₀ : 0 < max z.re |z.im| := lt_max_iff.2 (Or.inl <| one_pos.trans_le hz)
          simp only [Real.norm_of_nonneg (Real.log_nonneg hz')]
          rw [← Real.log_mul, Real.log_le_log_iff, ← abs_of_nonneg (le_trans zero_le_one hz)]
          exacts [norm_le_sqrt_two_mul_max z, one_pos.trans_le hz', mul_pos h2 hm₀, h2.ne', hm₀.ne']
    _ =o[l] re :=
      IsLittleO.add (isLittleO_const_left.2 <| Or.inr <| hl.tendsto_abs_re) <|
        isLittleO_iff_nat_mul_le.2 fun n => by
          filter_upwards [isLittleO_iff_nat_mul_le'.1 hl.isLittleO_log_re_re n,
            hl.abs_im_pow_eventuallyLE_exp_re n,
            hl.tendsto_re.eventually_gt_atTop 1] with z hre him h₁
          rcases le_total |z.im| z.re with hle | hle
          · rwa [max_eq_left hle]
          · have H : 1 < |z.im| := h₁.trans_le hle
            norm_cast at *
            rwa [max_eq_right hle, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.log_pos H),
              ← Real.log_pow, Real.log_le_iff_le_exp (pow_pos (one_pos.trans H) _),
              abs_of_pos (one_pos.trans h₁)]

/-!
### Main results
-/

lemma isTheta_cpow_exp_re_mul_log (hl : IsExpCmpFilter l) (a : ℂ) :
    (· ^ a) =Θ[l] fun z ↦ Real.exp (re a * Real.log ‖z‖) :=
  calc
    (fun z => z ^ a) =Θ[l] (fun z : ℂ => ‖z‖ ^ re a) :=
      isTheta_cpow_const_rpow fun _ _ => hl.eventually_ne
    _ =ᶠ[l] fun z => Real.exp (re a * Real.log ‖z‖) :=
      (hl.eventually_ne.mono fun z hz => by simp
        [Real.rpow_def_of_pos, norm_pos_iff.mpr hz, mul_comm])

/-- If `l : Filter ℂ` is an "exponential comparison filter", then for any complex `a` and any
positive real `b`, we have `(fun z ↦ z ^ a) =o[l] (fun z ↦ exp (b * z))`. -/
theorem isLittleO_cpow_exp (hl : IsExpCmpFilter l) (a : ℂ) {b : ℝ} (hb : 0 < b) :
    (fun z => z ^ a) =o[l] fun z => exp (b * z) :=
  calc
    (fun z => z ^ a) =Θ[l] fun z => Real.exp (re a * Real.log ‖z‖) :=
      hl.isTheta_cpow_exp_re_mul_log a
    _ =o[l] fun z => exp (b * z) :=
      IsLittleO.of_norm_right <| by
        simp only [norm_exp, re_ofReal_mul, Real.isLittleO_exp_comp_exp_comp]
        refine (IsEquivalent.refl.sub_isLittleO ?_).symm.tendsto_atTop
          (hl.tendsto_re.const_mul_atTop hb)
        exact (hl.isLittleO_log_norm_re.const_mul_left _).const_mul_right hb.ne'

/-- If `l : Filter ℂ` is an "exponential comparison filter", then for any complex `a₁`, `a₂` and any
real `b₁ < b₂`, we have `(fun z ↦ z ^ a₁ * exp (b₁ * z)) =o[l] (fun z ↦ z ^ a₂ * exp (b₂ * z))`. -/
theorem isLittleO_cpow_mul_exp {b₁ b₂ : ℝ} (hl : IsExpCmpFilter l) (hb : b₁ < b₂) (a₁ a₂ : ℂ) :
    (fun z => z ^ a₁ * exp (b₁ * z)) =o[l] fun z => z ^ a₂ * exp (b₂ * z) :=
  calc
    (fun z => z ^ a₁ * exp (b₁ * z)) =ᶠ[l] fun z => z ^ a₂ * exp (b₁ * z) * z ^ (a₁ - a₂) :=
      hl.eventually_ne.mono fun z hz => by
        simp only
        rw [mul_right_comm, ← cpow_add _ _ hz, add_sub_cancel]
    _ =o[l] fun z => z ^ a₂ * exp (b₁ * z) * exp (↑(b₂ - b₁) * z) :=
      ((isBigO_refl (fun z => z ^ a₂ * exp (b₁ * z)) l).mul_isLittleO <|
        hl.isLittleO_cpow_exp _ (sub_pos.2 hb))
    _ =ᶠ[l] fun z => z ^ a₂ * exp (b₂ * z) := by
      simp only [ofReal_sub, sub_mul, mul_assoc, ← exp_add, add_sub_cancel]
      norm_cast

/-- If `l : Filter ℂ` is an "exponential comparison filter", then for any complex `a` and any
negative real `b`, we have `(fun z ↦ exp (b * z)) =o[l] (fun z ↦ z ^ a)`. -/
theorem isLittleO_exp_cpow (hl : IsExpCmpFilter l) (a : ℂ) {b : ℝ} (hb : b < 0) :
    (fun z => exp (b * z)) =o[l] fun z => z ^ a := by simpa using hl.isLittleO_cpow_mul_exp hb 0 a

/-- If `l : Filter ℂ` is an "exponential comparison filter", then for any complex `a₁`, `a₂` and any
natural `b₁ < b₂`, we have
`(fun z ↦ z ^ a₁ * exp (b₁ * z)) =o[l] (fun z ↦ z ^ a₂ * exp (b₂ * z))`. -/
theorem isLittleO_pow_mul_exp {b₁ b₂ : ℝ} (hl : IsExpCmpFilter l) (hb : b₁ < b₂) (m n : ℕ) :
    (fun z => z ^ m * exp (b₁ * z)) =o[l] fun z => z ^ n * exp (b₂ * z) := by
  simpa only [cpow_natCast] using hl.isLittleO_cpow_mul_exp hb m n

/-- If `l : Filter ℂ` is an "exponential comparison filter", then for any complex `a₁`, `a₂` and any
integer `b₁ < b₂`, we have
`(fun z ↦ z ^ a₁ * exp (b₁ * z)) =o[l] (fun z ↦ z ^ a₂ * exp (b₂ * z))`. -/
theorem isLittleO_zpow_mul_exp {b₁ b₂ : ℝ} (hl : IsExpCmpFilter l) (hb : b₁ < b₂) (m n : ℤ) :
    (fun z => z ^ m * exp (b₁ * z)) =o[l] fun z => z ^ n * exp (b₂ * z) := by
  simpa only [cpow_intCast] using hl.isLittleO_cpow_mul_exp hb m n

end IsExpCmpFilter

end Complex
