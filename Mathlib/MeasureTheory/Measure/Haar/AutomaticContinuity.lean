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

The theorem `continuous_of_measurable_of_mul` splits on `f 0`. If `f 0 = 0` then `f` vanishes
identically (as `f x = f x * f 0`) and is continuous; otherwise `f` is nowhere zero and we appeal to
`continuous_of_measurable_of_mul_aux`, whose proof runs as follows.

1. **Nowhere zero.** From `f 0 ≠ 0` and multiplicativity, `f x ≠ 0` for every `x`.
2. **Continuous modulus** (`continuous_norm_of_measurable_of_mul`, the crucial reduction to the
   additive case). As `‖f‖` is multiplicative and positive, `t ↦ Real.log ‖f t‖` is a measurable
   *additive* map `ℝ → ℝ`, hence continuous by the additive theorem
   `MeasureTheory.Measure.AddMonoidHom.continuous_of_measurable`; exponentiating shows `‖f‖` is
   continuous.
3. **Integrability.** Being dominated by its continuous modulus, `f` is locally integrable, and so
   interval integrable on every interval.
4. **Continuous primitive.** Hence the primitive `F y = ∫ t in 0..y, f t` is continuous
   (`intervalIntegral.continuous_primitive`).
5. **A nonzero window.** `F a ≠ 0` for some `a`: were `F` identically zero, the Lebesgue
   differentiation theorem (`LocallyIntegrable.ae_hasDerivAt_integral`) would force `f = 0` almost
   everywhere, contradicting that `f` never vanishes.
6. **Sliding window.** Multiplicativity rewrites `∫ t in s..(s + a), f t` as both `f s * F a` and
   `F (s + a) - F s`, giving `f s = (F (s + a) - F s) / F a`, which is continuous in `s`.

These results are the `ℝ`-domain analytic special case of the classical fact that a measurable
homomorphism between locally compact, second-countable groups is continuous.

## Tags

automatic continuity, measurable, multiplicative, Cauchy functional equation
-/

public section

open MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]

/-- The modulus of a Borel-measurable multiplicative map `f : ℝ → 𝕜` that vanishes nowhere is
continuous. This is the key reduction to the additive case: `t ↦ Real.log ‖f t‖` is a measurable
*additive* map `ℝ → ℝ`, hence continuous by `Measure.AddMonoidHom.continuous_of_measurable`, and
`‖f t‖ = Real.exp (Real.log ‖f t‖)`. -/
private theorem continuous_norm_of_measurable_of_mul {f : ℝ → 𝕜} (hmeas : Measurable f)
    (hmul : ∀ x y, f (x + y) = f x * f y) (hne : ∀ x, f x ≠ 0) : Continuous fun t ↦ ‖f t‖ := by
  have hpos : ∀ t, 0 < ‖f t‖ := fun t ↦ norm_pos_iff.mpr (hne t)
  have hbadd : ∀ x y, Real.log ‖f (x + y)‖ = Real.log ‖f x‖ + Real.log ‖f y‖ := fun x y ↦ by
    rw [hmul, norm_mul, Real.log_mul (hpos x).ne' (hpos y).ne']
  have hbmeas : Measurable fun t ↦ Real.log ‖f t‖ := by fun_prop
  have hbcont : Continuous fun t ↦ Real.log ‖f t‖ :=
    Measure.AddMonoidHom.continuous_of_measurable
      (AddMonoidHom.mk' (fun t ↦ Real.log ‖f t‖) hbadd) hbmeas
  exact (Real.continuous_exp.comp hbcont).congr fun t ↦ Real.exp_log (hpos t)

/-- Nonvanishing case of `continuous_of_measurable_of_mul`: a Borel-measurable `f : ℝ → 𝕜` with
`f (x + y) = f x * f y` and `f 0 ≠ 0` (equivalently, `f` nowhere zero) is continuous. -/
private theorem continuous_of_measurable_of_mul_aux {f : ℝ → 𝕜} (hmeas : Measurable f)
    (hmul : ∀ x y, f (x + y) = f x * f y) (h0 : f 0 ≠ 0) : Continuous f := by
  -- The hypotheses force `f` to vanish nowhere; then its modulus is continuous.
  have hne : ∀ x, f x ≠ 0 := fun x hx ↦
    h0 <| by rw [← add_neg_cancel x, hmul, hx, zero_mul]
  have hnormcont : Continuous fun t ↦ ‖f t‖ := continuous_norm_of_measurable_of_mul hmeas hmul hne
  -- `f` is dominated by that continuous modulus, hence locally integrable and interval integrable.
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
