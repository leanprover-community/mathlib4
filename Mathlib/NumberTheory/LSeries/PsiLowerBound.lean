/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.LaplaceTransform.Landau
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
# A one-sided bound on Chebyshev's `ψ` and zeros of `ζ`

We prove that a *lower* bound on `ψ` alone excludes zeros of the Riemann zeta function. This is a
classical consequence of Landau's theorem on Laplace transforms with nonnegative integrand; compare
Ingham, *The Distribution of Prime Numbers*, Ch. V, and Montgomery–Vaughan, *Multiplicative Number
Theory I*, Ch. 15. Conversely, RH implies `ψ x = x + O(√x (log x) ^ 2)` (von Koch), so the
hypothesis of `riemannHypothesis_of_psi_lower` is equivalent to RH.

## Main results

* `riemannZeta_ne_zero_of_psi_lower`: if `0 < a` and `x - C * x ^ a ≤ ψ x` for all `x ≥ 1`, then
  `riemannZeta s ≠ 0` for `a < s.re`.
* `riemannHypothesis_of_ne_zero`: if `ζ` has no zeros with `1 / 2 < s.re`, then
  `RiemannHypothesis` (by the functional equation).
* `riemannHypothesis_of_psi_lower`: if for every `ε > 0` there is `C` with
  `x - C * x ^ (1 / 2 + ε) ≤ ψ x` for all `x ≥ 1`, then `RiemannHypothesis`.

## Proof outline

The defect `g t = ψ (exp t) - exp t + C * exp (a * t)` is nonnegative, and for `max a 1 < re z`
its Laplace transform is `L Λ z / z - 1 / (z - 1) + C / (z - a)`, from
`LSeries_eq_mul_integral_of_nonneg` and `integral_comp_exp_Ioi`. With `Z = riemannZeta₁` and
`A z = z * L z + 1 - C * z / (z - a)`, the identity `Z * A + Z' = 0` holds there, hence on the
half-plane to the right of the abscissa `σ` of the transform, where an entire solution of
`Z' = -A * Z` has no zeros. If `σ > a`, either `Z σ ≠ 0` and Landau's theorem gives a
contradiction, or `Z σ = 0` and the bound `-K ≤ re A` on `(σ, σ + 1)` (from `L s ≥ 0`) makes
`‖Z s‖ ^ 2 * exp (-2 * K * s)` nonincreasing there, which is incompatible with `Z σ = 0`.
-/

@[expose] public section

open MeasureTheory Set Complex Filter Topology Asymptotics ComplexConjugate
open scoped ArithmeticFunction.vonMangoldt Chebyshev

namespace RiemannHypothesis.OneSided

/-! ### An entire solution of `f' = −A f` has no zeros -/

/-- **A logarithmic-derivative equation forbids zeros.** If `f` is entire, not identically zero,
and near `ρ` satisfies `f' = −A f` with `A` analytic at `ρ`, then `f ρ ≠ 0`. -/
theorem ne_zero_of_deriv_eq_neg_mul {f A : ℂ → ℂ} (hf : Differentiable ℂ f) {z₀ : ℂ}
    (hz₀ : f z₀ ≠ 0) {ρ : ℂ} (hA : AnalyticAt ℂ A ρ)
    (hode : deriv f =ᶠ[𝓝 ρ] fun z => -(A z * f z)) : f ρ ≠ 0 := by
  intro hρ
  have hfa : AnalyticAt ℂ f ρ := hf.analyticAt ρ
  have hkey := hfa.analyticOrderAt_deriv_add_one
  simp only [hρ, sub_zero] at hkey
  have hord : analyticOrderAt (deriv f) ρ = analyticOrderAt A ρ + analyticOrderAt f ρ := by
    rw [analyticOrderAt_congr hode]
    rw [show (fun z => -(A z * f z)) = -(fun z => A z * f z) from rfl, analyticOrderAt_neg]
    exact analyticOrderAt_mul hA hfa
  have htop : analyticOrderAt f ρ = ⊤ := by
    rw [hord] at hkey
    by_contra hne
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hne
    rw [← hm] at hkey
    have hle : (m : ℕ∞) + 1 ≤ m := by
      calc (m : ℕ∞) + 1 ≤ analyticOrderAt A ρ + ((m : ℕ∞) + 1) := le_add_self
        _ = analyticOrderAt A ρ + m + 1 := by rw [add_assoc]
        _ = m := hkey
    have : m + 1 ≤ m := by exact_mod_cast hle
    omega
  rw [analyticOrderAt_eq_top] at htop
  have han : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  have hzero : Set.EqOn f 0 Set.univ :=
    AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero han isPreconnected_univ
      (Set.mem_univ ρ) htop
  exact hz₀ (hzero (Set.mem_univ z₀))

/-! ### A one-sided log-derivative bound on a real segment -/

/-- **A one-sided log-derivative bound keeps a function off zero at the end of a segment.**
If `Z' = −A Z` on the real segment `(σ, σ+1)` with `Re A ≥ −K` there, and `Z(σ+½) ≠ 0`, then
`Z(σ) ≠ 0`: `‖Z(s)‖² e^{−2Ks}` is nonincreasing on the segment, so it cannot tend to `0`. -/
theorem ne_zero_of_re_logDeriv_bound {Z A : ℂ → ℂ} (hZ : Differentiable ℂ Z) {σ K : ℝ}
    (hode : ∀ s : ℝ, σ < s → s < σ + 1 → deriv Z s = -(A s * Z s))
    (hA : ∀ s : ℝ, σ < s → s < σ + 1 → -K ≤ (A s).re)
    (hne : Z ((σ + 1 / 2 : ℝ) : ℂ) ≠ 0) : Z (σ : ℂ) ≠ 0 := by
  intro h0
  set φ : ℝ → ℝ := fun s => ‖Z (s : ℂ)‖ ^ 2 * Real.exp (-(2 * K) * s) with hφ
  have hcont : Continuous φ := by
    have : Continuous fun s : ℝ => Z (s : ℂ) := hZ.continuous.comp Complex.continuous_ofReal
    exact (this.norm.pow 2).mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hderiv : ∀ s : ℝ, σ < s → s < σ + 1 →
      HasDerivAt φ ((-2 * (A s).re - 2 * K) * ‖Z (s : ℂ)‖ ^ 2 *
        Real.exp (-(2 * K) * s)) s := by
    intro s h1 h2
    have hf : HasDerivAt (fun r : ℝ => Z (r : ℂ)) (deriv Z s) s :=
      (hZ (s : ℂ)).hasDerivAt.comp_ofReal
    have hq := hf.norm_sq
    rw [hode s h1 h2, Complex.inner] at hq
    have hre : (-(A s * Z s) * conj (Z s)).re = -(A s).re * ‖Z (s : ℂ)‖ ^ 2 := by
      rw [neg_mul, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq,
        Complex.neg_re, Complex.re_mul_ofReal]
      ring
    rw [hre] at hq
    have he : HasDerivAt (fun r : ℝ => Real.exp (-(2 * K) * r))
        (Real.exp (-(2 * K) * s) * (-(2 * K))) s := by
      have := ((hasDerivAt_id s).const_mul (-(2 * K))).exp
      simpa using this
    have := hq.mul he
    exact this.congr_deriv (by ring)
  have hanti : AntitoneOn φ (Ioo σ (σ + 1)) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioo _ _) hcont.continuousOn
      (f' := fun s => (-2 * (A s).re - 2 * K) * ‖Z (s : ℂ)‖ ^ 2 * Real.exp (-(2 * K) * s))
      (fun s hs => ?_) (fun s hs => ?_)
    · rw [interior_Ioo] at hs
      exact (hderiv s hs.1 hs.2).hasDerivWithinAt
    · rw [interior_Ioo] at hs
      have := hA s hs.1 hs.2
      have h1 : -2 * (A s).re - 2 * K ≤ 0 := by linarith
      exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg h1 (by positivity))
        (Real.exp_pos _).le
  have hpos : 0 < φ (σ + 1 / 2) := by
    have : 0 < ‖Z ((σ + 1 / 2 : ℝ) : ℂ)‖ := norm_pos_iff.mpr hne
    exact mul_pos (by positivity) (Real.exp_pos _)
  have hφσ : φ σ = 0 := by simp [hφ, h0]
  have hlim : Tendsto φ (𝓝[>] σ) (𝓝 0) := hφσ ▸ (hcont.tendsto σ).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ s in 𝓝[>] σ, φ (σ + 1 / 2) ≤ φ s := by
    filter_upwards [Ioo_mem_nhdsGT (show σ < σ + 1 / 2 by linarith)] with s hs
    exact hanti ⟨hs.1, by linarith [hs.2]⟩ ⟨by linarith, by linarith⟩ hs.2.le
  have := ge_of_tendsto hlim hev
  linarith

/-! ### The Laplace transform of the defect -/

lemma psi_natCast_eq (n : ℕ) : ∑ k ∈ Finset.Icc 1 n, Λ k = ψ n := by
  rw [Chebyshev.psi, Nat.floor_natCast]; rfl

lemma psi_floor_eq (y : ℝ) :
    (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, (Λ k : ℂ)) = (ψ y : ℂ) := by
  rw [Chebyshev.psi]; push_cast; rfl

lemma psi_isBigO : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, Λ k) =O[atTop] fun n ↦ (n : ℝ) ^ (1 : ℝ) := by
  refine IsBigO.of_bound (Real.log 4 + 4) (Eventually.of_forall fun n => ?_)
  rw [psi_natCast_eq, Real.rpow_one, Real.norm_of_nonneg (Chebyshev.psi_nonneg _),
    Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg _)

lemma cpow_exp_eq (x : ℝ) (w : ℂ) : ((Real.exp x : ℝ) : ℂ) ^ w = Complex.exp (x * w) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]

/-- **The Laplace transform of `ψ(eᵗ)` is `L(Λ, z)/z`** for `Re z > 1`. -/
theorem integral_psi_exp {z : ℂ} (hz : 1 < z.re) :
    ∫ t in Ioi (0 : ℝ), (ψ (Real.exp t) : ℂ) * Complex.exp (-z * t) =
      LSeries (fun n ↦ (Λ n : ℂ)) z / z := by
  have hz0 : z ≠ 0 := fun h => by rw [h, Complex.zero_re] at hz; linarith
  rw [LSeries_eq_mul_integral_of_nonneg (fun n => Λ n) zero_le_one (by simpa using hz) psi_isBigO
    (fun n => ArithmeticFunction.vonMangoldt_nonneg), mul_div_cancel_left₀ _ hz0]
  have := integral_comp_exp_Ioi
    (fun y : ℝ => (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, (Λ k : ℂ)) * (y : ℂ) ^ (-(z + 1))) 0
  rw [Real.exp_zero] at this
  rw [← this]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [psi_floor_eq, Complex.real_smul]
  rw [cpow_exp_eq, Complex.ofReal_exp, mul_left_comm, ← Complex.exp_add]
  congr 2; ring


lemma norm_psi_kernel_le {z : ℂ} (t : ℝ) :
    ‖(ψ (Real.exp t) : ℂ) * Complex.exp (-z * t)‖ ≤
      (Real.log 4 + 4) * Real.exp ((1 - z.re) * t) := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Chebyshev.psi_nonneg _),
    Complex.norm_exp]
  have h1 := Chebyshev.psi_le_const_mul_self (Real.exp_pos t).le
  have h2 : (-z * (t : ℂ)).re = -z.re * t := by simp
  rw [h2]
  calc ψ (Real.exp t) * Real.exp (-z.re * t)
      ≤ (Real.log 4 + 4) * Real.exp t * Real.exp (-z.re * t) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = (Real.log 4 + 4) * Real.exp ((1 - z.re) * t) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf

lemma integrableOn_psi_kernel {z : ℂ} (hz : 1 < z.re) :
    IntegrableOn (fun t : ℝ => (ψ (Real.exp t) : ℂ) * Complex.exp (-z * t)) (Ioi 0) := by
  refine Integrable.mono' ((integrableOn_exp_mul_Ioi (by linarith : 1 - z.re < 0) 0).const_mul
    (Real.log 4 + 4)) ?_ (Eventually.of_forall fun t => norm_psi_kernel_le t)
  exact ((Complex.measurable_ofReal.comp ((Chebyshev.psi_mono.measurable).comp
    Real.measurable_exp)).mul (Complex.continuous_exp.measurable.comp
      (measurable_const.mul Complex.measurable_ofReal))).aestronglyMeasurable

/-- The defect `g(t) = ψ(eᵗ) − eᵗ + C e^{at}` of a one-sided bound, clipped at `0`. -/
noncomputable def defect (a C : ℝ) (t : ℝ) : ℝ :=
  max 0 (ψ (Real.exp t) - Real.exp t + C * Real.exp (a * t))

lemma defect_nonneg (a C t : ℝ) : 0 ≤ defect a C t := le_max_left _ _

lemma measurable_defect (a C : ℝ) : Measurable (defect a C) :=
  measurable_const.max ((((Chebyshev.psi_mono.measurable).comp Real.measurable_exp).sub
    Real.measurable_exp).add (measurable_const.mul
      (Real.measurable_exp.comp (measurable_const.mul measurable_id))))

lemma defect_eq {a C : ℝ} (hψ : ∀ x : ℝ, 1 ≤ x → x - C * x ^ a ≤ ψ x) {t : ℝ} (ht : 0 ≤ t) :
    defect a C t = ψ (Real.exp t) - Real.exp t + C * Real.exp (a * t) := by
  refine max_eq_right ?_
  have := hψ (Real.exp t) (Real.one_le_exp ht)
  rw [← Real.exp_mul, mul_comm t a] at this
  linarith

lemma defect_le {a C : ℝ} (t : ℝ) :
    defect a C t ≤ (Real.log 4 + 4) * Real.exp t + |C| * Real.exp (a * t) := by
  have h1 := Chebyshev.psi_le_const_mul_self (Real.exp_pos t).le
  have h2 : C * Real.exp (a * t) ≤ |C| * Real.exp (a * t) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
  have h3 : 0 ≤ (Real.log 4 + 4) * Real.exp t + |C| * Real.exp (a * t) := by
    have : 0 < Real.log 4 := Real.log_pos (by norm_num)
    positivity
  refine max_le h3 ?_
  have := Real.exp_pos t
  linarith

lemma integrableOn_defect {a C s : ℝ} (hs1 : 1 < s) (hsa : a < s) :
    IntegrableOn (fun t => defect a C t * Real.exp (-s * t)) (Ioi 0) := by
  refine Integrable.mono' (((integrableOn_exp_mul_Ioi (by linarith : 1 - s < 0) 0).const_mul
    (Real.log 4 + 4)).add ((integrableOn_exp_mul_Ioi (by linarith : a - s < 0) 0).const_mul |C|))
    ((measurable_defect a C).mul (Real.continuous_exp.measurable.comp
      (measurable_const.mul measurable_id))).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (defect_nonneg a C t) (Real.exp_pos _).le)]
  calc defect a C t * Real.exp (-s * t)
      ≤ ((Real.log 4 + 4) * Real.exp t + |C| * Real.exp (a * t)) * Real.exp (-s * t) :=
        mul_le_mul_of_nonneg_right (defect_le t) (Real.exp_pos _).le
    _ = (Real.log 4 + 4) * Real.exp ((1 - s) * t) + |C| * Real.exp ((a - s) * t) := by
        rw [add_mul, mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]; ring_nf

/-- **The Laplace transform of the defect**, for `Re z > max a 1`. -/
theorem laplace_defect {a C : ℝ} (hψ : ∀ x : ℝ, 1 ≤ x → x - C * x ^ a ≤ ψ x) {z : ℂ}
    (hz1 : 1 < z.re) (hza : a < z.re) :
    laplace (fun t ↦ (defect a C t : ℂ)) z =
      LSeries (fun n ↦ (Λ n : ℂ)) z / z - 1 / (z - 1) + C / (z - a) := by
  have hI1 : IntegrableOn (fun t : ℝ => Complex.exp ((1 - z) * t)) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi (by simpa using hz1) 0
  have hIa : IntegrableOn (fun t : ℝ => Complex.exp ((a - z) * t)) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi (by simpa using hza) 0
  have hcongr : Set.EqOn (fun t : ℝ => (defect a C t : ℂ) * Complex.exp (-z * t))
      (fun t : ℝ => (ψ (Real.exp t) : ℂ) * Complex.exp (-z * t) -
        Complex.exp ((1 - z) * t) + (C : ℂ) * Complex.exp ((a - z) * t)) (Ioi 0) := by
    intro t ht
    simp only
    rw [defect_eq hψ (le_of_lt ht)]
    push_cast
    rw [add_mul, sub_mul, mul_assoc (C : ℂ), ← Complex.exp_add,
      ← Complex.exp_add]
    ring_nf
  rw [laplace_ofReal_eq, setIntegral_congr_fun measurableSet_Ioi hcongr,
    integral_add (f := fun t : ℝ => (ψ (Real.exp t) : ℂ) * Complex.exp (-z * t) -
        Complex.exp ((1 - z) * t)) (g := fun t : ℝ => (C : ℂ) * Complex.exp ((a - z) * t))
      ((integrableOn_psi_kernel hz1).sub hI1) (hIa.const_mul _),
    integral_sub (integrableOn_psi_kernel hz1) hI1, integral_const_mul,
    integral_psi_exp hz1, integral_exp_mul_complex_Ioi (by simpa using hz1),
    integral_exp_mul_complex_Ioi (by simpa using hza)]
  have h1 : (1 : ℂ) - z ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have h2 : (a : ℂ) - z ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have h1' : z - 1 ≠ 0 := fun h => h1 (by rw [← neg_sub, h, neg_zero])
  have h2' : z - a ≠ 0 := fun h => h2 (by rw [← neg_sub, h, neg_zero])
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp
  ring

/-! ### `ζ` in terms of the entire function `riemannZeta₁ = (s − 1) ζ(s)` -/

lemma riemannZeta₁_eq_mul {z : ℂ} (hz : z ≠ 1) :
    riemannZeta₁ z = (z - 1) * riemannZeta z := by
  rw [riemannZeta_eq_inv_sub_mul hz, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hz), one_mul]

lemma deriv_riemannZeta_eq {z : ℂ} (hz : z ≠ 1) :
    deriv riemannZeta z =
      -((z - 1) ^ 2)⁻¹ * riemannZeta₁ z + (z - 1)⁻¹ * deriv riemannZeta₁ z := by
  have hev : riemannZeta =ᶠ[𝓝 z] fun w => (w - 1)⁻¹ * riemannZeta₁ w := by
    filter_upwards [eventually_ne_nhds hz] with w hw using riemannZeta_eq_inv_sub_mul hw
  rw [hev.deriv_eq]
  have h1 : HasDerivAt (fun w : ℂ => (w - 1)⁻¹) (-((z - 1) ^ 2)⁻¹) z := by
    have := ((hasDerivAt_id z).sub_const 1).inv (sub_ne_zero.mpr hz)
    exact this.congr_deriv (by simp [div_eq_mul_inv])
  exact (h1.mul (differentiable_riemannZeta₁ z).hasDerivAt).deriv

lemma riemannZeta₁_two_ne_zero : riemannZeta₁ 2 ≠ 0 := by
  rw [riemannZeta₁_eq_mul (by norm_num)]
  exact mul_ne_zero (by norm_num) (riemannZeta_ne_zero_of_one_le_re (by norm_num))

/-- **The zeta identity** `Z · (L(Λ, z) − 1/(z−1)) + Z' = 0` for `Re z > 1`, where
`Z = riemannZeta₁`. -/
lemma zeta_identity {z : ℂ} (hz : 1 < z.re) :
    riemannZeta₁ z * (LSeries (fun n ↦ (Λ n : ℂ)) z - 1 / (z - 1)) +
      deriv riemannZeta₁ z = 0 := by
  have hz1 : z ≠ 1 := fun h => by rw [h, Complex.one_re] at hz; exact lt_irrefl _ hz
  have hζ : riemannZeta z ≠ 0 := riemannZeta_ne_zero_of_one_le_re hz.le
  have hs : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hz, deriv_riemannZeta_eq hz1,
    riemannZeta₁_eq_mul hz1]
  field_simp
  ring

lemma differentiable_deriv_riemannZeta₁ : Differentiable ℂ (deriv riemannZeta₁) := fun z =>
  (differentiable_riemannZeta₁.analyticAt z).deriv.differentiableAt

lemma laplace_ofReal_ofReal {g : ℝ → ℝ} (r : ℝ) :
    laplace (fun t ↦ (g t : ℂ)) (r : ℂ) =
      ((∫ t in Ioi (0 : ℝ), g t * Real.exp (-r * t) : ℝ) : ℂ) := by
  rw [laplace_ofReal_eq, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  push_cast
  rfl

/-! ### The main theorem -/

/-- **A one-sided lower bound `ψ(x) ≥ x − C x^a` excludes zeros of `(s−1)ζ(s)` with
`Re s > a`.** -/
theorem riemannZeta₁_ne_zero_of_psi_lower {a C : ℝ} (ha : 0 < a)
    (hψ : ∀ x : ℝ, 1 ≤ x → x - C * x ^ a ≤ ψ x) {s : ℂ} (hs : a < s.re) :
    riemannZeta₁ s ≠ 0 := by
  set g := defect a C with hgdef
  have hg : ∀ t, 0 ≤ g t := defect_nonneg a C
  have hgm : Measurable g := measurable_defect a C
  have hmono : ∀ r₁ r₂ : ℝ, r₁ ≤ r₂ →
      ∫⁻ t in Ioi 0, ENNReal.ofReal (g t * Real.exp (-r₁ * t)) < ⊤ →
      ∫⁻ t in Ioi 0, ENNReal.ofReal (g t * Real.exp (-r₂ * t)) < ⊤ := by
    intro r₁ r₂ hr h
    refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioi fun t ht => ?_) h
    have ht0 : (0 : ℝ) < t := ht
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith)) (hg t))
  set S : Set ℝ := {b | a ≤ b ∧ ∀ r : ℝ, b < r →
    ∫⁻ t in Ioi 0, ENNReal.ofReal (g t * Real.exp (-r * t)) < ⊤} with hS
  have hb₀ : max a 1 ∈ S := ⟨le_max_left _ _, fun r hr =>
    (integrableOn_defect (lt_of_le_of_lt (le_max_right _ _) hr)
      (lt_of_le_of_lt (le_max_left _ _) hr)).lintegral_lt_top⟩
  have hbdd : BddBelow S := ⟨a, fun b hb => hb.1⟩
  have hne : S.Nonempty := ⟨_, hb₀⟩
  set σ := sInf S with hσ
  have hσa : a ≤ σ := le_csInf hne fun b hb => hb.1
  have hσb : σ ≤ max a 1 := csInf_le hbdd hb₀
  have hconv : ∀ r : ℝ, σ < r →
      ∫⁻ t in Ioi 0, ENNReal.ofReal (g t * Real.exp (-r * t)) < ⊤ := by
    intro r hr
    obtain ⟨b, hb, hbr⟩ := exists_lt_of_csInf_lt hne hr
    exact hb.2 r hbr
  set W : Set ℂ := {z | σ < z.re} with hW
  have hWo : IsOpen W := isOpen_lt continuous_const Complex.continuous_re
  have hconv' : ∀ r : ℝ, σ < r → LaplaceConvergent (fun t ↦ (g t : ℂ)) r := fun r hr ↦
    (laplaceConvergent_ofReal_iff hg hgm r).mpr (hconv r hr)
  have hL : DifferentiableOn ℂ (laplace fun t ↦ (g t : ℂ)) W :=
    differentiableOn_laplace_ofReal_of_nonneg hg hgm hconv'
  set A : ℂ → ℂ := fun z => z * laplace (fun t ↦ (g t : ℂ)) z + 1 - C * z / (z - a)
    with hAdef
  have hza : ∀ z ∈ W, z - a ≠ 0 := fun z hz h => by
    have h' := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at h'
    have : σ < z.re := hz
    linarith
  have hA : DifferentiableOn ℂ A W := by
    intro z hz
    have hLz := hL.differentiableAt (hWo.mem_nhds hz)
    have hz' := hza z hz
    have : DifferentiableAt ℂ A z := by
      simp only [hAdef]
      fun_prop (disch := assumption)
    exact this.differentiableWithinAt
  have hZd := differentiable_riemannZeta₁
  have hZd' := differentiable_deriv_riemannZeta₁
  set H : ℂ → ℂ := fun z => riemannZeta₁ z * A z + deriv riemannZeta₁ z with hHdef
  have hH : AnalyticOnNhd ℂ H W :=
    ((hZd.differentiableOn.mul hA).add hZd'.differentiableOn).analyticOnNhd hWo
  set z₀ : ℂ := ((max a 1 + 1 : ℝ) : ℂ) with hz₀
  have hz₀W : z₀ ∈ W := by
    change σ < z₀.re
    rw [hz₀, Complex.ofReal_re]; linarith
  have hHev : H =ᶠ[𝓝 z₀] 0 := by
    have hV : IsOpen {z : ℂ | max a 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hz₀V : z₀ ∈ {z : ℂ | max a 1 < z.re} := by
      change max a 1 < z₀.re
      rw [hz₀, Complex.ofReal_re]; linarith
    filter_upwards [hV.mem_nhds hz₀V] with z hz
    have hz1 : 1 < z.re := lt_of_le_of_lt (le_max_right _ _) hz
    have hza' : a < z.re := lt_of_le_of_lt (le_max_left _ _) hz
    have hz0 : z ≠ 0 := fun h => by rw [h, Complex.zero_re] at hz1; linarith
    have hzs1 : z - 1 ≠ 0 := fun h => by
      have h' := congrArg Complex.re h
      simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at h'
      linarith
    have hzsa : z - a ≠ 0 := fun h => by
      have h' := congrArg Complex.re h
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at h'
      linarith
    have hAz : A z = LSeries (fun n ↦ (Λ n : ℂ)) z - 1 / (z - 1) := by
      simp only [hAdef]
      rw [laplace_defect hψ hz1 hza']
      field_simp
      ring
    change riemannZeta₁ z * A z + deriv riemannZeta₁ z = 0
    rw [hAz]
    exact zeta_identity hz1
  have hH0 : Set.EqOn H 0 W :=
    hH.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_halfSpace_re_gt σ).isPreconnected
      hz₀W hHev
  have hode : ∀ z ∈ W, deriv riemannZeta₁ z = -(A z * riemannZeta₁ z) := by
    intro z hz
    have := hH0 hz
    simp only [hHdef, Pi.zero_apply] at this
    linear_combination this
  have hZW : ∀ ρ ∈ W, riemannZeta₁ ρ ≠ 0 := by
    intro ρ hρ
    refine ne_zero_of_deriv_eq_neg_mul hZd riemannZeta₁_two_ne_zero
      (hA.analyticAt (hWo.mem_nhds hρ)) ?_
    filter_upwards [hWo.mem_nhds hρ] with z hz using hode z hz
  -- The abscissa is `a`.
  have hσeq : ¬ a < σ := by
    intro hlt
    by_cases hZσ : riemannZeta₁ (σ : ℂ) = 0
    · -- Real-boundary argument.
      refine ne_zero_of_re_logDeriv_bound hZd (A := A) (K := |C| * (1 + a / (σ - a)))
        (fun r h1 _ => hode (r : ℂ) (by change σ < (r : ℂ).re; simpa using h1)) (fun r h1 _ => ?_)
        (hZW _ (by change σ < ((σ + 1 / 2 : ℝ) : ℂ).re; simp)) hZσ
      have hr0 : 0 < r := by linarith
      have hra : 0 < r - a := by linarith
      have hAr : A (r : ℂ) = ((r * (∫ t in Ioi (0 : ℝ), g t * Real.exp (-r * t)) + 1 -
          C * r / (r - a) : ℝ) : ℂ) := by
        simp only [hAdef, laplace_ofReal_ofReal]
        push_cast
        ring
      rw [hAr, Complex.ofReal_re]
      have hI : 0 ≤ ∫ t in Ioi (0 : ℝ), g t * Real.exp (-r * t) :=
        setIntegral_nonneg measurableSet_Ioi fun t _ => mul_nonneg (hg t) (Real.exp_pos _).le
      have hfrac : r / (r - a) ≤ 1 + a / (σ - a) := by
        have h1 : r / (r - a) = 1 + a / (r - a) := by field_simp; ring
        rw [h1]
        have : a / (r - a) ≤ a / (σ - a) :=
          div_le_div_of_nonneg_left ha.le (by linarith) (by linarith)
        linarith
      have hC : C * r / (r - a) ≤ |C| * (1 + a / (σ - a)) := by
        rw [mul_div_assoc]
        calc C * (r / (r - a)) ≤ |C| * (r / (r - a)) :=
              mul_le_mul_of_nonneg_right (le_abs_self C) (div_pos hr0 hra).le
          _ ≤ |C| * (1 + a / (σ - a)) := mul_le_mul_of_nonneg_left hfrac (abs_nonneg C)
      have := mul_nonneg hr0.le hI
      have hK : 0 ≤ |C| * (1 + a / (σ - a)) := by
        have : 0 ≤ a / (σ - a) := div_nonneg ha.le (by linarith)
        positivity
      linarith
    · -- Landau: the transform would continue across the real point `σ`.
      have hev : ∀ᶠ z in 𝓝 (σ : ℂ), riemannZeta₁ z ≠ 0 :=
        hZd.continuous.continuousAt.eventually_ne hZσ
      obtain ⟨ε, hε, hεZ⟩ := Metric.eventually_nhds_iff.mp hev
      set ε' := min ε (σ - a) with hε'
      have hε'0 : 0 < ε' := lt_min hε (by linarith)
      have hgood : ∀ z ∈ W ∪ Metric.ball (σ : ℂ) ε', riemannZeta₁ z ≠ 0 ∧ a < z.re := by
        intro z hz
        rcases hz with hz | hz
        · exact ⟨hZW z hz, lt_of_le_of_lt hσa hz⟩
        · rw [Metric.mem_ball] at hz
          refine ⟨hεZ (lt_of_lt_of_le hz (min_le_left _ _)), ?_⟩
          have h1 : |z.re - σ| < σ - a := by
            have := Complex.abs_re_le_norm (z - σ)
            rw [Complex.sub_re, Complex.ofReal_re] at this
            rw [Complex.dist_eq] at hz
            exact lt_of_le_of_lt this (lt_of_lt_of_le hz (min_le_right _ _))
          rw [abs_lt] at h1
          linarith
      set F : ℂ → ℂ := fun z =>
        (-(deriv riemannZeta₁ z) / riemannZeta₁ z - 1 + C * z / (z - a)) / z with hFdef
      have hF : DifferentiableOn ℂ F (W ∪ Metric.ball (σ : ℂ) ε') := by
        intro z hz
        obtain ⟨hZz, hre⟩ := hgood z hz
        have hz0 : z ≠ 0 := fun h => by rw [h, Complex.zero_re] at hre; linarith
        have hzsa : z - a ≠ 0 := fun h => by
          have h' := congrArg Complex.re h
          simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at h'
          linarith
        have h1 := hZd z
        have h2 := hZd' z
        have : DifferentiableAt ℂ F z := by
          simp only [hFdef]
          fun_prop (disch := assumption)
        exact this.differentiableWithinAt
      have heq : Set.EqOn F (laplace fun t ↦ (g t : ℂ)) W := by
        intro z hz
        have hZz := hZW z hz
        have hre : σ < z.re := hz
        have hz0 : z ≠ 0 := fun h => by rw [h, Complex.zero_re] at hre; linarith
        have hzsa := hza z hz
        simp only [hFdef]
        rw [hode z hz]
        simp only [hAdef]
        field_simp
        ring
      have hdiv : ∀ r : ℝ, r < σ →
          ∫⁻ t in Ioi 0, ENNReal.ofReal (g t * Real.exp (-r * t)) = ⊤ := by
        intro r hr
        by_contra hne'
        have hc := lt_top_iff_ne_top.mpr hne'
        have hmem : max r a ∈ S := ⟨le_max_right _ _, fun r' hr' =>
          hmono r r' (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hr')) hc⟩
        have := csInf_le hbdd hmem
        have : max r a < σ := max_lt hr hlt
        linarith
      refine not_differentiableOn_laplace_ofReal_of_nonneg hg hgm hconv' (fun r hr hc ↦ ?_)
        hε'0 hF heq
      have h1 := (laplaceConvergent_ofReal_iff hg hgm r).mp hc
      rw [hdiv r hr] at h1
      exact lt_irrefl _ h1
  have hσ' : σ ≤ a := not_lt.mp hσeq
  exact hZW s (show σ < s.re by linarith)

/-- **A one-sided lower bound `ψ(x) ≥ x − C x^a` excludes zeros of `ζ` with `Re s > a`.** -/
theorem riemannZeta_ne_zero_of_psi_lower {a C : ℝ} (ha : 0 < a)
    (hψ : ∀ x : ℝ, 1 ≤ x → x - C * x ^ a ≤ ψ x) {s : ℂ} (hs : a < s.re) :
    riemannZeta s ≠ 0 := by
  by_cases hs1 : s = 1
  · exact riemannZeta_ne_zero_of_one_le_re (by rw [hs1, Complex.one_re])
  · intro h
    exact riemannZeta₁_ne_zero_of_psi_lower ha hψ hs (by rw [riemannZeta₁_eq_mul hs1, h, mul_zero])

/-- **Zero-freeness right of `½` implies `RiemannHypothesis`**, via the functional equation. -/
theorem riemannHypothesis_of_ne_zero
    (h : ∀ s : ℂ, 1 / 2 < s.re → riemannZeta s ≠ 0) : RiemannHypothesis := by
  intro s hs htriv hs1
  rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
  · exfalso
    set s' := 1 - s with hs'
    have hre : 1 / 2 < s'.re := by rw [hs', Complex.sub_re, Complex.one_re]; linarith
    have hs0 : s ≠ 0 := fun h0 => by
      rw [h0, riemannZeta_zero] at hs; norm_num at hs
    have hn : ∀ n : ℕ, s' ≠ -n := fun n hn => by
      have := congrArg Complex.re hn
      rw [Complex.neg_re, Complex.natCast_re] at this
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hs'1 : s' ≠ 1 := fun h1 => hs0 (by rw [hs'] at h1; linear_combination -h1)
    have hfe := riemannZeta_one_sub hn hs'1
    rw [hs', sub_sub_cancel, ← hs'] at hfe
    rw [hs] at hfe
    have hpi : (2 * (Real.pi : ℂ)) ≠ 0 :=
      mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
    have hcpow : (2 * (Real.pi : ℂ)) ^ (-s') ≠ 0 := by
      rw [Complex.cpow_def_of_ne_zero hpi]; exact Complex.exp_ne_zero _
    have hcos : Complex.cos (Real.pi * s' / 2) ≠ 0 := by
      rw [Ne, Complex.cos_eq_zero_iff]
      rintro ⟨k, hk⟩
      have hpi' : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have hk' : s' = 2 * k + 1 := by
        have := hk
        field_simp at this
        linear_combination this
      have hsk : s = -2 * k := by rw [hs'] at hk'; linear_combination -hk'
      rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
      · have := congrArg Complex.re hsk
        simp only [Complex.mul_re, Complex.neg_re, Complex.intCast_re, Complex.intCast_im,
          Complex.re_ofNat, mul_zero, sub_zero] at this
        have : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hk0
        linarith
      · exact hs0 (by rw [hsk, hk0]; simp)
      · apply htriv
        refine ⟨(k - 1).toNat, ?_⟩
        rw [hsk]
        have : ((k - 1).toNat : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
        have h2 : (((k - 1).toNat : ℕ) : ℂ) = ((k - 1 : ℤ) : ℂ) := by exact_mod_cast this
        rw [h2]; push_cast; ring
    have hΓ : Complex.Gamma s' ≠ 0 := Complex.Gamma_ne_zero hn
    have := h s' hre
    have hprod : 2 * (2 * (Real.pi : ℂ)) ^ (-s') * Complex.Gamma s' *
        Complex.cos (Real.pi * s' / 2) * riemannZeta s' ≠ 0 := by
      apply_rules [mul_ne_zero, two_ne_zero]
    exact hprod hfe.symm
  · exact heq
  · exact absurd hs (h s hgt)

/-- **The one-sided criterion.** If for every `ε > 0` there is `C` with
`ψ(x) ≥ x − C x^{½+ε}` for all `x ≥ 1`, then the Riemann Hypothesis holds.

This is a conditional theorem: the hypothesis is not proved here, and it is equivalent to RH. -/
theorem riemannHypothesis_of_psi_lower
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → x - C * x ^ (1 / 2 + ε) ≤ ψ x) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_ne_zero fun s hs => ?_
  obtain ⟨C, hC⟩ := h ((s.re - 1 / 2) / 2) (by linarith)
  exact riemannZeta_ne_zero_of_psi_lower (by linarith) hC (by linarith)


end RiemannHypothesis.OneSided
