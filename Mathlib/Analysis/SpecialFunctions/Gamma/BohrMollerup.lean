/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! # Convexity properties of the Gamma function

In this file, we prove that `Gamma` and `log ∘ Gamma` are convex functions on the positive real
line. We then prove the Bohr-Mollerup theorem, which characterises `Gamma` as the *unique*
positive-real-valued, log-convex function on the positive reals satisfying `f (x + 1) = x f x` and
`f 1 = 1`.

The proof of the Bohr-Mollerup theorem is bound up with the proof of (a weak form of) the Euler
limit formula, `Real.BohrMollerup.tendsto_logGammaSeq`, stating that for positive
real `x` the sequence `x * log n + log n! - ∑ (m : ℕ) ∈ Finset.range (n + 1), log (x + m)`
tends to `log Γ(x)` as `n → ∞`. We prove that any function satisfying the hypotheses of the
Bohr-Mollerup theorem must agree with the limit in the Euler limit formula, so there is at most one
such function; then we show that `Γ` satisfies these conditions.

Since most of the auxiliary lemmas for the Bohr-Mollerup theorem are of no relevance outside the
context of this proof, we place them in a separate namespace `Real.BohrMollerup` to avoid clutter.
(This includes the logarithmic form of the Euler limit formula, since later we will prove a more
general form of the Euler limit formula valid for any real or complex `x`; see
`Real.Gamma_seq_tendsto_Gamma` and `Complex.Gamma_seq_tendsto_Gamma` in the file
`Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean`.)

As an application of the Bohr-Mollerup theorem we prove the Legendre doubling formula for the
Gamma function for real positive `s` (which will be upgraded to a proof for all complex `s` in a
later file).

TODO: This argument can be extended to prove the general `k`-multiplication formula (at least up
to a constant, and it should be possible to deduce the value of this constant using Stirling's
formula).
-/

@[expose] public section


noncomputable section

open Filter Set MeasureTheory

open scoped Nat ENNReal Topology Real

namespace Real

local notation "Γ" => Gamma

section Convexity

/-- Log-convexity of the Gamma function on the positive reals (stated in multiplicative form),
proved using the Hölder inequality applied to Euler's integral. -/
theorem Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma {s t a b : ℝ} (hs : 0 < s) (ht : 0 < t)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    Gamma (a * s + b * t) ≤ Gamma s ^ a * Gamma t ^ b := by
  -- We will apply Hölder's inequality, for the conjugate exponents `p = 1 / a`
  -- and `q = 1 / b`, to the functions `f a s` and `f b t`, where `f` is as follows:
  let f : ℝ → ℝ → ℝ → ℝ := fun c u x => exp (-c * x) * x ^ (c * (u - 1))
  have e : HolderConjugate (1 / a) (1 / b) := Real.holderConjugate_one_div ha hb hab
  have hab' : b = 1 - a := by linarith
  have hst : 0 < a * s + b * t := by positivity
  -- some properties of f:
  have posf : ∀ c u x : ℝ, x ∈ Ioi (0 : ℝ) → 0 ≤ f c u x := fun c u x hx =>
    mul_nonneg (exp_pos _).le (rpow_pos_of_pos hx _).le
  have posf' : ∀ c u : ℝ, ∀ᵐ x : ℝ ∂volume.restrict (Ioi 0), 0 ≤ f c u x := fun c u =>
    (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ (posf c u))
  have fpow :
    ∀ {c x : ℝ} (_ : 0 < c) (u : ℝ) (_ : 0 < x), exp (-x) * x ^ (u - 1) = f c u x ^ (1 / c) := by
    intro c x hc u hx
    dsimp only [f]
    rw [mul_rpow (exp_pos _).le ((rpow_nonneg hx.le) _), ← exp_mul, ← rpow_mul hx.le]
    congr 2 <;> field
  -- show `f c u` is in `ℒp` for `p = 1/c`:
  have f_mem_Lp :
    ∀ {c u : ℝ} (hc : 0 < c) (hu : 0 < u),
      MemLp (f c u) (ENNReal.ofReal (1 / c)) (volume.restrict (Ioi 0)) := by
    intro c u hc hu
    have A : ENNReal.ofReal (1 / c) ≠ 0 := by
      rwa [Ne, ENNReal.ofReal_eq_zero, not_le, one_div_pos]
    have B : ENNReal.ofReal (1 / c) ≠ ∞ := ENNReal.ofReal_ne_top
    rw [← memLp_norm_rpow_iff _ A B, ENNReal.toReal_ofReal (one_div_nonneg.mpr hc.le),
      ENNReal.div_self A B, memLp_one_iff_integrable]
    · apply Integrable.congr (GammaIntegral_convergent hu)
      refine eventuallyEq_of_mem (self_mem_ae_restrict measurableSet_Ioi) fun x hx => ?_
      dsimp only
      rw [fpow hc u hx]
      congr 1
      exact (norm_of_nonneg (posf _ _ x hx)).symm
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      refine .mul (by fun_prop) (continuousOn_of_forall_continuousAt fun x hx ↦ ?_)
      exact continuousAt_rpow_const _ _ (Or.inl (mem_Ioi.mp hx).ne')
  -- now apply Hölder:
  rw [Gamma_eq_integral hs, Gamma_eq_integral ht, Gamma_eq_integral hst]
  convert
    MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg e (posf' a s) (posf' b t) (f_mem_Lp ha hs)
      (f_mem_Lp hb ht) using
    1
  · refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    dsimp only
    have A : exp (-x) = exp (-a * x) * exp (-b * x) := by
      rw [← exp_add, ← add_mul, ← neg_add, hab, neg_one_mul]
    have B : x ^ (a * s + b * t - 1) = x ^ (a * (s - 1)) * x ^ (b * (t - 1)) := by
      rw [← rpow_add hx, hab']; congr 1; ring
    rw [A, B]
    ring
  · rw [one_div_one_div, one_div_one_div]
    congr 2 <;> exact setIntegral_congr_fun measurableSet_Ioi fun x hx => fpow (by assumption) _ hx

theorem convexOn_log_Gamma : ConvexOn ℝ (Ioi 0) (log ∘ Gamma) := by
  refine convexOn_iff_forall_pos.mpr ⟨convex_Ioi _, fun x hx y hy a b ha hb hab => ?_⟩
  have : b = 1 - a := by linarith
  subst this
  simp_rw [Function.comp_apply, smul_eq_mul]
  push _ ∈ _ at hx hy
  rw [← log_rpow, ← log_rpow, ← log_mul]
  · gcongr
    exact Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma hx hy ha hb hab
  all_goals positivity

theorem convexOn_Gamma : ConvexOn ℝ (Ioi 0) Gamma := by
  refine
    ((convexOn_exp.subset (subset_univ _) ?_).comp convexOn_log_Gamma
          (exp_monotone.monotoneOn _)).congr
      fun x hx => exp_log (Gamma_pos_of_pos hx)
  rw [convex_iff_isPreconnected]
  refine isPreconnected_Ioi.image _ fun x hx => ContinuousAt.continuousWithinAt ?_
  refine (differentiableAt_Gamma fun m => ?_).continuousAt.log (Gamma_pos_of_pos hx).ne'
  exact (neg_lt_iff_pos_add.mpr (add_pos_of_pos_of_nonneg (mem_Ioi.mp hx) (Nat.cast_nonneg m))).ne'

end Convexity

section BohrMollerup

namespace BohrMollerup

/-- The function `n ↦ x log n + log n! - (log x + ... + log (x + n))`, which we will show tends to
`log (Gamma x)` as `n → ∞`. -/
def logGammaSeq (x : ℝ) (n : ℕ) : ℝ :=
  x * log n + log n ! - ∑ m ∈ Finset.range (n + 1), log (x + m)

variable {f : ℝ → ℝ} {x : ℝ} {n : ℕ}

theorem f_nat_eq (hf_feq : ∀ {y : ℝ}, 0 < y → f (y + 1) = f y + log y) (hn : n ≠ 0) :
    f n = f 1 + log (n - 1)! := by
  refine Nat.le_induction (by simp) (fun m hm IH => ?_) n (Nat.one_le_iff_ne_zero.2 hn)
  have A : 0 < (m : ℝ) := Nat.cast_pos.2 hm
  simp only [hf_feq A, Nat.cast_add, Nat.cast_one, Nat.add_succ_sub_one, add_zero]
  rw [IH, add_assoc, ← log_mul (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)) A.ne', ←
    Nat.cast_mul]
  conv_rhs => rw [← Nat.succ_pred_eq_of_pos hm, Nat.factorial_succ, mul_comm]
  congr
  exact (Nat.succ_pred_eq_of_pos hm).symm

theorem f_add_nat_eq (hf_feq : ∀ {y : ℝ}, 0 < y → f (y + 1) = f y + log y) (hx : 0 < x) (n : ℕ) :
    f (x + n) = f x + ∑ m ∈ Finset.range n, log (x + m) := by
  induction n with
  | zero => simp
  | succ n hn =>
    have : x + n.succ = x + n + 1 := by push_cast; ring
    rw [this, hf_feq, hn]
    · rw [Finset.range_add_one, Finset.sum_insert Finset.notMem_range_self]
      abel
    · linarith [(Nat.cast_nonneg n : 0 ≤ (n : ℝ))]

/-- Linear upper bound for `f (x + n)` on unit interval -/
theorem f_add_nat_le (hf_conv : ConvexOn ℝ (Ioi 0) f)
    (hf_feq : ∀ {y : ℝ}, 0 < y → f (y + 1) = f y + log y) (hn : n ≠ 0) (hx : 0 < x) (hx' : x ≤ 1) :
    f (n + x) ≤ f n + x * log n := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have : f n + x * log n = (1 - x) * f n + x * f (n + 1) := by rw [hf_feq hn']; ring
  rw [this, (by ring : (n : ℝ) + x = (1 - x) * n + x * (n + 1))]
  simpa only [smul_eq_mul] using
    hf_conv.2 hn' (by linarith : 0 < (n + 1 : ℝ)) (by linarith : 0 ≤ 1 - x) hx.le (by linarith)

/-- Linear lower bound for `f (x + n)` on unit interval -/
theorem f_add_nat_ge (hf_conv : ConvexOn ℝ (Ioi 0) f)
    (hf_feq : ∀ {y : ℝ}, 0 < y → f (y + 1) = f y + log y) (hn : 2 ≤ n) (hx : 0 < x) :
    f n + x * log (n - 1) ≤ f (n + x) := by
  have npos : 0 < (n : ℝ) - 1 := by rw [← Nat.cast_one, sub_pos, Nat.cast_lt]; lia
  have c :=
    (convexOn_iff_slope_mono_adjacent.mp <| hf_conv).2 npos (by linarith : 0 < (n : ℝ) + x)
      (by linarith : (n : ℝ) - 1 < (n : ℝ)) (by linarith)
  rw [add_sub_cancel_left, sub_sub_cancel, div_one] at c
  have : f (↑n - 1) = f n - log (↑n - 1) := by
    rw [eq_sub_iff_add_eq, ← hf_feq npos, sub_add_cancel]
  rwa [this, le_div_iff₀ hx, sub_sub_cancel, le_sub_iff_add_le, mul_comm _ x, add_comm] at c

theorem logGammaSeq_add_one (x : ℝ) (n : ℕ) :
    logGammaSeq (x + 1) n = logGammaSeq x (n + 1) + log x - (x + 1) * (log (n + 1) - log n) := by
  dsimp only [Nat.factorial_succ, logGammaSeq]
  conv_rhs => rw [Finset.sum_range_succ', Nat.cast_zero, add_zero]
  rw [Nat.cast_mul, log_mul]; rotate_left
  · rw [Nat.cast_ne_zero]; exact Nat.succ_ne_zero n
  · rw [Nat.cast_ne_zero]; exact Nat.factorial_ne_zero n
  have :
    ∑ m ∈ Finset.range (n + 1), log (x + 1 + ↑m) =
      ∑ k ∈ Finset.range (n + 1), log (x + ↑(k + 1)) := by
    congr! 2 with m
    push_cast
    abel
  rw [← this, Nat.cast_add_one n]
  ring

theorem le_logGammaSeq (hf_conv : ConvexOn ℝ (Ioi 0) f)
    (hf_feq : ∀ {y : ℝ}, 0 < y → f (y + 1) = f y + log y) (hx : 0 < x) (hx' : x ≤ 1) (n : ℕ) :
    f x ≤ f 1 + x * log (n + 1) - x * log n + logGammaSeq x n := by
  rw [logGammaSeq, ← add_sub_assoc, le_sub_iff_add_le, ← f_add_nat_eq (@hf_feq) hx, add_comm x]
  refine (f_add_nat_le hf_conv (@hf_feq) (Nat.add_one_ne_zero n) hx hx').trans (le_of_eq ?_)
  rw [f_nat_eq @hf_feq (by lia : n + 1 ≠ 0), Nat.add_sub_cancel, Nat.cast_add_one]
  ring

theorem ge_logGammaSeq (hf_conv : ConvexOn ℝ (Ioi 0) f)
    (hf_feq : ∀ {y : ℝ}, 0 < y → f (y + 1) = f y + log y) (hx : 0 < x) (hn : n ≠ 0) :
    f 1 + logGammaSeq x n ≤ f x := by
  dsimp [logGammaSeq]
  rw [← add_sub_assoc, sub_le_iff_le_add, ← f_add_nat_eq (@hf_feq) hx, add_comm x _]
  refine le_trans (le_of_eq ?_) (f_add_nat_ge hf_conv @hf_feq ?_ hx)
  · rw [f_nat_eq @hf_feq, Nat.add_sub_cancel, Nat.cast_add_one, add_sub_cancel_right]
    · ring
    · exact Nat.succ_ne_zero _
  · lia

theorem tendsto_logGammaSeq_of_le_one (hf_conv : ConvexOn ℝ (Ioi 0) f)
    (hf_feq : ∀ {y : ℝ}, 0 < y → f (y + 1) = f y + log y) (hx : 0 < x) (hx' : x ≤ 1) :
    Tendsto (logGammaSeq x) atTop (𝓝 <| f x - f 1) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (f := logGammaSeq x)
    (g := fun n ↦ f x - f 1 - x * (log (n + 1) - log n)) ?_ tendsto_const_nhds ?_ ?_
  · have : f x - f 1 = f x - f 1 - x * 0 := by ring
    nth_rw 2 [this]
    exact Tendsto.sub tendsto_const_nhds (tendsto_log_nat_add_one_sub_log.const_mul _)
  · filter_upwards with n
    rw [sub_le_iff_le_add', sub_le_iff_le_add']
    convert le_logGammaSeq hf_conv (@hf_feq) hx hx' n using 1
    ring
  · change ∀ᶠ n : ℕ in atTop, logGammaSeq x n ≤ f x - f 1
    filter_upwards [eventually_ne_atTop 0] with n hn using
      le_sub_iff_add_le'.mpr (ge_logGammaSeq hf_conv hf_feq hx hn)

theorem tendsto_logGammaSeq (hf_conv : ConvexOn ℝ (Ioi 0) f)
    (hf_feq : ∀ {y : ℝ}, 0 < y → f (y + 1) = f y + log y) (hx : 0 < x) :
    Tendsto (logGammaSeq x) atTop (𝓝 <| f x - f 1) := by
  suffices ∀ m : ℕ, ↑m < x → x ≤ m + 1 → Tendsto (logGammaSeq x) atTop (𝓝 <| f x - f 1) by
    refine this ⌈x - 1⌉₊ ?_ ?_
    · rcases lt_or_ge x 1 with ⟨⟩
      · rwa [Nat.ceil_eq_zero.mpr (by linarith : x - 1 ≤ 0), Nat.cast_zero]
      · convert Nat.ceil_lt_add_one (by linarith : 0 ≤ x - 1)
        abel
    · rw [← sub_le_iff_le_add]; exact Nat.le_ceil _
  intro m
  induction m generalizing x with
  | zero =>
    rw [Nat.cast_zero, zero_add]
    exact fun _ hx' => tendsto_logGammaSeq_of_le_one hf_conv (@hf_feq) hx hx'
  | succ m hm =>
    intro hy hy'
    rw [Nat.cast_succ, ← sub_le_iff_le_add] at hy'
    rw [Nat.cast_succ, ← lt_sub_iff_add_lt] at hy
    specialize hm ((Nat.cast_nonneg _).trans_lt hy) hy hy'
    -- now massage gauss_product n (x - 1) into gauss_product (n - 1) x
    have :
      ∀ᶠ n : ℕ in atTop,
        logGammaSeq (x - 1) n =
          logGammaSeq x (n - 1) + x * (log (↑(n - 1) + 1) - log ↑(n - 1)) - log (x - 1) := by
      refine Eventually.mp (eventually_ge_atTop 1) (Eventually.of_forall fun n hn => ?_)
      have := logGammaSeq_add_one (x - 1) (n - 1)
      rw [sub_add_cancel, Nat.sub_add_cancel hn] at this
      rw [this]
      ring
    replace hm :=
      ((Tendsto.congr' this hm).add (tendsto_const_nhds : Tendsto (fun _ => log (x - 1)) _ _)).comp
        (tendsto_add_atTop_nat 1)
    have :
      ((fun x_1 : ℕ =>
            (fun n : ℕ =>
                  logGammaSeq x (n - 1) + x * (log (↑(n - 1) + 1) - log ↑(n - 1)) - log (x - 1))
                x_1 +
              (fun b : ℕ => log (x - 1)) x_1) ∘
          fun a : ℕ => a + 1) =
        fun n => logGammaSeq x n + x * (log (↑n + 1) - log ↑n) := by
      ext1 n
      dsimp only [Function.comp_apply]
      rw [sub_add_cancel, Nat.add_sub_cancel]
    rw [this] at hm
    convert hm.sub (tendsto_log_nat_add_one_sub_log.const_mul x) using 2
    · ring
    · have := hf_feq ((Nat.cast_nonneg m).trans_lt hy)
      rw [sub_add_cancel] at this
      rw [this]
      ring

theorem tendsto_log_gamma {x : ℝ} (hx : 0 < x) :
    Tendsto (logGammaSeq x) atTop (𝓝 <| log (Gamma x)) := by
  have : log (Gamma x) = (log ∘ Gamma) x - (log ∘ Gamma) 1 := by
    simp_rw [Function.comp_apply, Gamma_one, log_one, sub_zero]
  rw [this]
  refine BohrMollerup.tendsto_logGammaSeq convexOn_log_Gamma (fun {y} hy => ?_) hx
  rw [Function.comp_apply, Gamma_add_one hy.ne', log_mul hy.ne' (Gamma_pos_of_pos hy).ne', add_comm,
    Function.comp_apply]

end BohrMollerup

-- (namespace)
/-- The **Bohr-Mollerup theorem**: the Gamma function is the *unique* log-convex, positive-valued
function on the positive reals which satisfies `f 1 = 1` and `f (x + 1) = x * f x` for all `x`. -/
theorem eq_Gamma_of_log_convex {f : ℝ → ℝ} (hf_conv : ConvexOn ℝ (Ioi 0) (log ∘ f))
    (hf_feq : ∀ {y : ℝ}, 0 < y → f (y + 1) = y * f y) (hf_pos : ∀ {y : ℝ}, 0 < y → 0 < f y)
    (hf_one : f 1 = 1) : EqOn f Gamma (Ioi (0 : ℝ)) := by
  suffices EqOn (log ∘ f) (log ∘ Gamma) (Ioi (0 : ℝ)) from
    fun x hx ↦ log_injOn_pos (hf_pos hx) (Gamma_pos_of_pos hx) (this hx)
  intro x hx
  have e1 := BohrMollerup.tendsto_logGammaSeq hf_conv ?_ hx
  · rw [Function.comp_apply (f := log) (g := f) (x := 1), hf_one, log_one, sub_zero] at e1
    exact tendsto_nhds_unique e1 (BohrMollerup.tendsto_log_gamma hx)
  · intro y hy
    rw [Function.comp_apply, Function.comp_apply, hf_feq hy, log_mul hy.ne' (hf_pos hy).ne']
    ring

end BohrMollerup

-- (section)
section StrictMono

theorem Gamma_two : Gamma 2 = 1 := by simp [Nat.factorial_one]

theorem Gamma_three_div_two_lt_one : Gamma (3 / 2) < 1 := by
  -- This can also be proved using the closed-form evaluation of `Gamma (1 / 2)` in
  -- `Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean`, but we give a
  -- self-contained proof using log-convexity to avoid unnecessary imports.
  have A : (0 : ℝ) < 3 / 2 := by simp
  have :=
    BohrMollerup.f_add_nat_le convexOn_log_Gamma (fun {y} hy => ?_) two_ne_zero one_half_pos
      (by norm_num : 1 / 2 ≤ (1 : ℝ))
  swap
  · rw [Function.comp_apply, Gamma_add_one hy.ne', log_mul hy.ne' (Gamma_pos_of_pos hy).ne',
      add_comm, Function.comp_apply]
  rw [Function.comp_apply, Function.comp_apply, Nat.cast_two, Gamma_two, log_one, zero_add,
    (by norm_num : (2 : ℝ) + 1 / 2 = 3 / 2 + 1), Gamma_add_one A.ne',
    log_mul A.ne' (Gamma_pos_of_pos A).ne', ← le_sub_iff_add_le',
    log_le_iff_le_exp (Gamma_pos_of_pos A)] at this
  refine this.trans_lt (exp_lt_one_iff.mpr ?_)
  rw [mul_comm, ← mul_div_assoc, div_sub' two_ne_zero]
  refine div_neg_of_neg_of_pos ?_ two_pos
  rw [sub_neg, mul_one, ← Nat.cast_two, ← log_pow, ← exp_lt_exp, Nat.cast_two, exp_log two_pos,
      exp_log] <;>
    norm_num

theorem Gamma_strictAntiOn_Ioc : StrictAntiOn Gamma (Ioc 0 1) :=
  convexOn_Gamma.strictAntiOn (by simp) (by norm_num) <|
    Gamma_one.symm ▸ Gamma_three_div_two_lt_one

theorem Gamma_strictMonoOn_Ici : StrictMonoOn Gamma (Ici 2) := by
  convert
    convexOn_Gamma.strictMonoOn (by simp : (0 : ℝ) < 3 / 2)
      (by norm_num : (3 / 2 : ℝ) < 2) (Gamma_two.symm ▸ Gamma_three_div_two_lt_one)
  symm
  rw [inter_eq_right]
  exact fun x hx => two_pos.trans_le <| mem_Ici.mp hx

-- TODO: prove uniqueness once the necessary material to do so makes its way into Mathlib
theorem exists_isMinOn_Gamma_Ioi : ∃ x ∈ Ioo 1 2, IsMinOn Gamma (Ioi 0) x := by
  have ⟨x, hx, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr one_le_two) <|
    differentiableOn_Gamma_Ioi.continuousOn.mono <| by grind
  have ⟨h1, h2, h3half⟩ : Γ (3 / 2) < Γ 1 ∧ Γ (3 / 2) < Γ 2 ∧ Γ x ≤ Γ (3 / 2) := by
    simpa [Gamma_three_div_two_lt_one] using hmin <| by norm_num
  refine ⟨x, by grind, fun y _ ↦ ?_⟩
  obtain hy | hy | hy : y ∈ Ioc 0 1 ∨ y ∈ Icc 1 2 ∨ y ∈ Ici 2 := by grind
  · exact h3half.trans h1.le |>.trans <| Gamma_strictAntiOn_Ioc.antitoneOn hy (by simp) hy.right
  · exact hmin hy
  · exact h3half.trans h2.le |>.trans <| Gamma_strictMonoOn_Ici.monotoneOn (by simp) hy hy

end StrictMono

section Doubling

/-!
## The Gamma doubling formula

As a fun application of the Bohr-Mollerup theorem, we prove the Gamma-function doubling formula
(for positive real `s`). The idea is that `2 ^ s * Gamma (s / 2) * Gamma (s / 2 + 1 / 2)` is
log-convex and satisfies the Gamma functional equation, so it must actually be a constant
multiple of `Gamma`, and we can compute the constant by specialising at `s = 1`. -/


/-- Auxiliary definition for the doubling formula (we'll show this is equal to `Gamma s`) -/
def doublingGamma (s : ℝ) : ℝ :=
  Gamma (s / 2) * Gamma (s / 2 + 1 / 2) * 2 ^ (s - 1) / √π

theorem doublingGamma_add_one (s : ℝ) (hs : s ≠ 0) :
    doublingGamma (s + 1) = s * doublingGamma s := by
  rw [doublingGamma, doublingGamma, (by abel : s + 1 - 1 = s - 1 + 1), add_div, add_assoc,
    add_halves (1 : ℝ), Gamma_add_one (div_ne_zero hs two_ne_zero), rpow_add two_pos, rpow_one]
  ring

theorem doublingGamma_one : doublingGamma 1 = 1 := by
  simp_rw [doublingGamma, Gamma_one_half_eq, add_halves (1 : ℝ), sub_self, Gamma_one, mul_one,
    rpow_zero, mul_one, div_self (sqrt_ne_zero'.mpr pi_pos)]

theorem log_doublingGamma_eq :
    EqOn (log ∘ doublingGamma)
      (fun s => log (Gamma (s / 2)) + log (Gamma (s / 2 + 1 / 2)) + s * log 2 - log (2 * √π))
      (Ioi 0) := by
  intro s hs
  have h1 : √π ≠ 0 := sqrt_ne_zero'.mpr pi_pos
  have h2 : Gamma (s / 2) ≠ 0 := (Gamma_pos_of_pos <| div_pos hs two_pos).ne'
  have h3 : Gamma (s / 2 + 1 / 2) ≠ 0 :=
    (Gamma_pos_of_pos <| add_pos (div_pos hs two_pos) one_half_pos).ne'
  have h4 : (2 : ℝ) ^ (s - 1) ≠ 0 := (rpow_pos_of_pos two_pos _).ne'
  rw [Function.comp_apply, doublingGamma, log_div (mul_ne_zero (mul_ne_zero h2 h3) h4) h1,
    log_mul (mul_ne_zero h2 h3) h4, log_mul h2 h3, log_rpow two_pos, log_mul two_ne_zero h1]
  ring_nf

theorem doublingGamma_log_convex_Ioi : ConvexOn ℝ (Ioi (0 : ℝ)) (log ∘ doublingGamma) := by
  refine (((ConvexOn.add ?_ ?_).add ?_).add_const _).congr log_doublingGamma_eq.symm
  · convert
      convexOn_log_Gamma.comp_affineMap (DistribSMul.toLinearMap ℝ ℝ (1 / 2 : ℝ)).toAffineMap
      using 1
    · simpa only [zero_div] using (preimage_const_mul_Ioi (0 : ℝ) one_half_pos).symm
    · ext1 x
      simp only [LinearMap.coe_toAffineMap, Function.comp_apply, DistribSMul.toLinearMap_apply]
      rw [smul_eq_mul, mul_comm, mul_one_div]
  · refine ConvexOn.subset ?_ (Ioi_subset_Ioi <| neg_one_lt_zero.le) (convex_Ioi _)
    convert
      convexOn_log_Gamma.comp_affineMap
        ((DistribSMul.toLinearMap ℝ ℝ (1 / 2 : ℝ)).toAffineMap +
          AffineMap.const ℝ ℝ (1 / 2 : ℝ)) using 1
    · change Ioi (-1 : ℝ) = ((fun x : ℝ => x + 1 / 2) ∘ fun x : ℝ => (1 / 2 : ℝ) * x) ⁻¹' Ioi 0
      rw [preimage_comp, preimage_add_const_Ioi, zero_sub,
        preimage_const_mul_Ioi (_ : ℝ) one_half_pos, neg_div, div_self (@one_half_pos ℝ _).ne']
    · ext1 x
      change log (Gamma (x / 2 + 1 / 2)) = log (Gamma ((1 / 2 : ℝ) • x + 1 / 2))
      rw [smul_eq_mul, mul_comm, mul_one_div]
  · simpa only [mul_comm _ (log _)] using
      (convexOn_id (convex_Ioi (0 : ℝ))).smul (log_pos one_lt_two).le

theorem doublingGamma_eq_Gamma {s : ℝ} (hs : 0 < s) : doublingGamma s = Gamma s := by
  refine
    eq_Gamma_of_log_convex doublingGamma_log_convex_Ioi
      (fun {y} hy => doublingGamma_add_one y hy.ne') (fun {y} hy => ?_) doublingGamma_one hs
  apply_rules [mul_pos, Gamma_pos_of_pos, add_pos, inv_pos_of_pos, rpow_pos_of_pos, two_pos,
    one_pos, sqrt_pos_of_pos pi_pos]

/-- Legendre's doubling formula for the Gamma function, for positive real arguments. Note that
we shall later prove this for all `s` as `Real.Gamma_mul_Gamma_add_half` (superseding this result)
but this result is needed as an intermediate step. -/
theorem Gamma_mul_Gamma_add_half_of_pos {s : ℝ} (hs : 0 < s) :
    Gamma s * Gamma (s + 1 / 2) = Gamma (2 * s) * 2 ^ (1 - 2 * s) * √π := by
  rw [← doublingGamma_eq_Gamma (mul_pos two_pos hs), doublingGamma,
    mul_div_cancel_left₀ _ (two_ne_zero' ℝ), (by abel : 1 - 2 * s = -(2 * s - 1)),
    rpow_neg zero_le_two]
  field

end Doubling

end Real
