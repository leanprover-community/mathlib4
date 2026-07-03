/-
Copyright (c) 2026 Ondřej Čertík. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ondřej Čertík
-/
module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Automatic continuity of measurable multiplicative maps on `ℝ`

A Borel-measurable solution of the *multiplicative* Cauchy functional equation on `ℝ`, i.e. a
measurable `f : ℝ → 𝕜` (with `RCLike 𝕜`) satisfying `f (x + y) = f x * f y`, is
automatically continuous. This is the multiplicative companion of the additive automatic-continuity
theorem `MeasureTheory.Measure.AddMonoidHom.continuous_of_measurable`.

## Main results

* `AddChar.continuous_of_measurable`: a measurable additive character `ψ : AddChar ℝ 𝕜` is
  continuous.
* `continuous_of_measurable_of_mul`: a measurable `f : ℝ → 𝕜` with `f (x + y) = f x * f y` is
  continuous (either `f` is identically zero, or it is nowhere zero).
* `continuous_of_measurable_of_mul_units`: the same for a measurable `f : ℝ → 𝕜ˣ` with
  `f (x + y) = f x * f y`.

## Implementation notes

If `f 0 = 0` then `f` vanishes identically (since `f x = f x * f 0`) and is continuous, so we may
assume `f` is nowhere zero. The modulus `‖f‖` is multiplicative, so `t ↦ Real.log ‖f t‖` is an
additive measurable map `ℝ → ℝ`, hence continuous by
`MeasureTheory.Measure.AddMonoidHom.continuous_of_measurable`; thus `‖f‖` is continuous and `f` is
locally bounded, so interval integrable. The primitive `F y = ∫ t in 0..y, f t` is continuous, and
the Lebesgue differentiation theorem (`LocallyIntegrable.ae_hasDerivAt_integral`) forces `F a ≠ 0`
for some `a` (otherwise `f = 0` almost everywhere, impossible since `f` never vanishes). The
homomorphism property gives the sliding-window identity
`f s * F a = ∫ t in s..(s + a), f t = F (s + a) - F s`, so `f s = (F (s + a) - F s) / F a` is
continuous in `s`.

These results are the `ℝ`-domain analytic special case of the classical fact that a measurable
homomorphism between locally compact, second-countable groups is continuous.

## Tags

automatic continuity, measurable, multiplicative, Cauchy functional equation
-/

public section

open MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]

/-- Nonvanishing case of `continuous_of_measurable_of_mul`: a Borel-measurable `f : ℝ → 𝕜` with
`f (x + y) = f x * f y` and `f 0 ≠ 0` (equivalently, `f` nowhere zero) is continuous. -/
private theorem continuous_of_measurable_of_mul_aux {f : ℝ → 𝕜} (hmeas : Measurable f)
    (hmul : ∀ x y, f (x + y) = f x * f y) (h0 : f 0 ≠ 0) : Continuous f := by
  -- The hypotheses force `f` to vanish nowhere.
  have hne : ∀ x, f x ≠ 0 := fun x hx ↦
    h0 <| by rw [← add_neg_cancel x, hmul, hx, zero_mul]
  have hpos : ∀ t, 0 < ‖f t‖ := fun t ↦ norm_pos_iff.mpr (hne t)
  -- The modulus is continuous, via the additive theorem applied to `t ↦ Real.log ‖f t‖`.
  have hbadd : ∀ x y, Real.log ‖f (x + y)‖ = Real.log ‖f x‖ + Real.log ‖f y‖ := fun x y ↦ by
    rw [hmul, norm_mul, Real.log_mul (hpos x).ne' (hpos y).ne']
  have hbmeas : Measurable fun t ↦ Real.log ‖f t‖ := by fun_prop
  have hbcont : Continuous fun t ↦ Real.log ‖f t‖ :=
    Measure.AddMonoidHom.continuous_of_measurable
      (AddMonoidHom.mk' (fun t ↦ Real.log ‖f t‖) hbadd) hbmeas
  have hnormcont : Continuous fun t ↦ ‖f t‖ :=
    (Real.continuous_exp.comp hbcont).congr fun t ↦ Real.exp_log (hpos t)
  -- `f` is dominated by the continuous modulus, hence locally integrable and interval integrable.
  have haesm : AEStronglyMeasurable f volume := hmeas.aestronglyMeasurable
  have hloc : LocallyIntegrable f volume :=
    hnormcont.locallyIntegrable.mono haesm (ae_of_all _ fun x ↦ (norm_norm (f x)).ge)
  have hii : ∀ a b : ℝ, IntervalIntegrable f volume a b := fun a b ↦
    (hloc.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  -- The primitive of `f` is continuous.
  set F : ℝ → 𝕜 := fun y ↦ ∫ t in (0 : ℝ)..y, f t with hFdef
  have hFcont : Continuous F := intervalIntegral.continuous_primitive hii 0
  -- Some window `[0, a]` has nonzero integral, by the Lebesgue differentiation theorem.
  have hExists : ∃ a : ℝ, F a ≠ 0 := by
    by_contra! hcon
    have hzero : ∀ᵐ x : ℝ, f x = 0 := by
      have hF0 : F = fun _ ↦ (0 : 𝕜) := funext hcon
      filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hloc] with x hx
      have hd := hx 0
      rw [← hFdef, hF0] at hd
      exact ((hasDerivAt_const x (0 : 𝕜)).unique hd).symm
    rw [ae_iff] at hzero
    have huniv : {x : ℝ | ¬ f x = 0} = Set.univ := by
      ext x; simpa using hne x
    rw [huniv, Real.volume_univ] at hzero
    exact ENNReal.top_ne_zero hzero
  -- The sliding-window identity exhibits `f` as the continuous `s ↦ (F (s + a) - F s) / F a`.
  obtain ⟨a, ha⟩ := hExists
  have hcontinuous : Continuous fun s ↦ (F (s + a) - F s) / F a := by fun_prop
  convert hcontinuous with s
  have h2 : (∫ u in (0 : ℝ)..a, f (s + u)) = f s * ∫ u in (0 : ℝ)..a, f u := by
    simp_rw [hmul s, intervalIntegral.integral_const_mul]
  have hsub : f s * F a = ∫ t in s..(s + a), f t := by
    rw [show F a = ∫ u in (0 : ℝ)..a, f u from rfl, ← h2,
      intervalIntegral.integral_comp_add_left f s, add_zero]
  have hadj : F (s + a) - F s = ∫ t in s..(s + a), f t :=
    intervalIntegral.integral_interval_sub_left (hii 0 (s + a)) (hii 0 s)
  rw [eq_div_iff ha]; exact hsub.trans hadj.symm

/-- **Automatic continuity for the multiplicative Cauchy equation.** A Borel-measurable
`f : ℝ → 𝕜` (`RCLike 𝕜`, e.g. `ℝ` or `ℂ`) with `f (x + y) = f x * f y` is continuous. No
nonvanishing hypothesis is needed: such an `f` is either identically zero or nowhere zero. This is
the multiplicative companion of `MeasureTheory.Measure.AddMonoidHom.continuous_of_measurable`. -/
theorem continuous_of_measurable_of_mul {f : ℝ → 𝕜} (hmeas : Measurable f)
    (hmul : ∀ x y, f (x + y) = f x * f y) : Continuous f := by
  rcases eq_or_ne (f 0) 0 with h0 | h0
  · have hf0 : f = fun _ ↦ (0 : 𝕜) := funext fun x ↦ by simpa [h0] using hmul x 0
    rw [hf0]; exact continuous_const
  · exact continuous_of_measurable_of_mul_aux hmeas hmul h0

/-- **Automatic continuity for measurable homomorphisms `(ℝ, +) → 𝕜ˣ`.** A Borel-measurable
`f : ℝ → 𝕜ˣ` (`RCLike 𝕜`) with `f (x + y) = f x * f y` is continuous. This specializes at `𝕜 = ℂ`
to the automatic continuity of measurable group homomorphisms `(ℝ, +) → ℂˣ`. -/
theorem continuous_of_measurable_of_mul_units {f : ℝ → 𝕜ˣ} (hmeas : Measurable f)
    (hmul : ∀ x y, f (x + y) = f x * f y) : Continuous f := by
  have hval : Measurable fun x ↦ (f x : 𝕜) := (comap_measurable Units.val).comp hmeas
  have hmulval : ∀ x y, (f (x + y) : 𝕜) = (f x : 𝕜) * (f y : 𝕜) := by
    intro x y; rw [hmul, Units.val_mul]
  have hcont : Continuous fun x ↦ (f x : 𝕜) :=
    continuous_of_measurable_of_mul hval hmulval
  rw [Units.continuous_iff]
  exact ⟨hcont, (hcont.inv₀ fun x ↦ (f x).ne_zero).congr
    fun x ↦ (Units.val_inv_eq_inv_val (f x)).symm⟩

/-- **Automatic continuity of measurable additive characters on `ℝ`.** A Borel-measurable additive
character `ψ : AddChar ℝ 𝕜` (`RCLike 𝕜`) is continuous. This is the multiplicative companion of
`MeasureTheory.Measure.AddMonoidHom.continuous_of_measurable`; at `𝕜 = ℂ` it gives the automatic
continuity of measurable characters `ℝ → ℂ`. -/
theorem AddChar.continuous_of_measurable (ψ : AddChar ℝ 𝕜) (hmeas : Measurable ψ) :
    Continuous ψ :=
  continuous_of_measurable_of_mul hmeas ψ.map_add_eq_mul
