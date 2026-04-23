/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Distribution.FourierMultiplier
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.ApplyFun
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.FieldSimp
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
import Mathlib.Tactic.SetLike

/-! # Sobolev spaces (Bessel potential spaces)

In this file we define Sobolev spaces on normed vector spaces via the Fourier transform.
These spaces are also known as Bessel potential spaces. The Bessel potential operator
`besselPotential` is the Fourier multiplier with the symbol `x ↦ (1 + ‖x‖ ^ 2) ^ (s / 2)` and a
tempered distribution `u` belongs to the Sobolev space `H ^ {s, p}` if
`besselPotential E F s u` can be represented by a `Lp` function, informally this is written as
`𝓕⁻ (fun x ↦ (1 + ‖x‖ ^ 2) ^ (s / 2)) 𝓕 u ∈ Lp`.

Note that the Bessel potential is the operator `(1 - (2 * π) ^ (-2) • Δ) ^ (s / 2)` and not
`(1 - Δ) ^ (s / 2)` due to the convention of the Fourier transform. This obviously does not impact
the definition of the Sobolev spaces.

## Main definitions

* `TemperedDistribution.besselPotential`: The Bessel potential operator is the Fourier multiplier
  with the function `(1 + ‖x‖ ^ 2) ^ (s / 2)`.
* `TemperedDistribution.memSobolev`: A tempered distribution lies in the Sobolev space of order `s`
  and `p` if `besselPotential E F s u ∈ Lp`.

## Main statements

* `SchwartzMap.memSobolev`: Each Schwartz function belongs to every Sobolev space
* `TemperedDistribution.memSobolev_two_iff_fourier`: The characterization of `p = 2` Sobolev
  functions
* `TemperedDistribution.MemSobolev.fourierMultiplierCLM_of_bounded`: If `u` is a Sobolev
  function, then `g • u` is a Sobolev function of the same order provided `g` is bounded.
* `TemperedDistribution.MemSobolev.lineDerivOp`: If `u` is a Sobolev function of order `s`, then
  `∂_{m} u` is a Sobolev function of order `s - 1`.
* `TemperedDistribution.MemSobolev.laplacian`: If `u` is a Sobolev function of order `s`, then
  `Δ u` is a Sobolev function of order `s - 2`.


## References
* [M. Taylor, *Partial Differential Equations 1*][taylorPDE1]
* [W. McLean, *Strongly Elliptic Systems and Boundary Integral Equations*][mclean2000]

-/

@[expose] public noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

open FourierTransform TemperedDistribution ENNReal MeasureTheory
open scoped SchwartzMap

namespace TemperedDistribution

section normed

variable [NormedSpace ℂ F]

variable (E F) in
/-- The Bessel potential operator is the Fourier multiplier with the function
`(1 + ‖x‖ ^ 2) ^ (s / 2)`.

Note that due to the convention of the Fourier transform, this is the operator
`(1 - (2 * π) ^ (-2) • Δ) ^ (s / 2)` not `(1 - Δ) ^ (s / 2)`. -/
def besselPotential (s : ℝ) : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F) :=
  fourierMultiplierCLM F (fun x ↦ ((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ))

variable (E F) in
@[simp]
theorem besselPotential_zero : besselPotential E F 0 = ContinuousLinearMap.id ℂ _ := by
  ext f
  simp [besselPotential]

@[simp]
theorem besselPotential_besselPotential_apply (s s' : ℝ) (f : 𝓢'(E, F)) :
    besselPotential E F s' (besselPotential E F s f) = besselPotential E F (s + s') f := by
  simp only [besselPotential]
  rw [fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) (by fun_prop)]
  congr
  ext x
  simp only [Pi.mul_apply]
  norm_cast
  calc
    _ = (1 + ‖x‖ ^ 2) ^ (s / 2 + s' / 2) := by
      rw [← Real.rpow_add (by positivity)]
    _ = _ := by congr; ring

theorem besselPotential_compL_besselPotential (s s' : ℝ) :
    besselPotential E F s' ∘L besselPotential E F s = besselPotential E F (s + s') := by
  ext f : 1
  exact besselPotential_besselPotential_apply s s' f

theorem besselPotential_neg_apply_eq_iff (s : ℝ) (f g : 𝓢'(E, F)) :
    besselPotential E F (-s) f = g ↔ besselPotential E F s g = f := by
  constructor <;>
  intro h <;> simp [← h]

open scoped Real Laplacian LineDeriv

theorem besselPotential_neg_one_lineDerivOp_eq {m : E} (f : 𝓢'(E, F)) :
    (besselPotential E F (-1)) (∂_{m} f) =
      (2 * π * Complex.I) • fourierMultiplierCLM F (fun x ↦ Complex.ofReal <|
      inner ℝ x m * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ)) f := by
  rw [lineDeriv_eq_fourierMultiplierCLM, besselPotential,
    ContinuousLinearMap.map_smul_of_tower,
    fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) (by fun_prop)]
  congr
  ext x
  simp

set_option backward.isDefEq.respectTransparency false in
theorem besselPotential_neg_two_laplacian_eq (f : 𝓢'(E, F)) :
    (besselPotential E F (-2)) (Δ f) = -(2 * π) ^ 2 •
      fourierMultiplierCLM F (fun x ↦ Complex.ofReal <| ‖x‖ ^ 2 * (1 + ‖x‖ ^ 2) ^ (-1 : ℝ)) f := by
  rw [laplacian_eq_fourierMultiplierCLM, besselPotential,
    ContinuousLinearMap.map_smul_of_tower,
    fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) (by fun_prop)]
  congr
  ext x
  simp

end normed

section inner

variable [InnerProductSpace ℂ F]

open FourierTransform

@[simp]
theorem fourier_besselPotential_eq_smulLeftCLM_fourier_apply (s : ℝ) (f : 𝓢'(E, F)) :
    𝓕 (besselPotential E F s f) =
      smulLeftCLM F (fun x ↦ ((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ)) (𝓕 f) := by
  simp [besselPotential, fourierMultiplierCLM]

end inner

section normed

variable [NormedSpace ℂ F] [CompleteSpace F]

/-- A tempered distribution `f` is a Sobolev function of order `s` if there exists an `Lp` function
`f'` such that `𝓕⁻ (1 + ‖x‖ ^ 2) ^ (s / 2) 𝓕 f = f'`. -/
def MemSobolev (s : ℝ) (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] (f : 𝓢'(E, F)) : Prop :=
  ∃ (f' : Lp F p (volume : Measure E)),
    besselPotential E F s f = f'

theorem memSobolev_zero_iff {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] {f : 𝓢'(E, F)} : MemSobolev 0 p f ↔
    ∃ (f' : Lp F p (volume : Measure E)), f = f' := by
  simp [MemSobolev]

theorem MemSobolev.add {s : ℝ} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] {f g : 𝓢'(E, F)}
    (hf : MemSobolev s p f) (hg : MemSobolev s p g) : MemSobolev s p (f + g) := by
  obtain ⟨f', hf⟩ := hf
  obtain ⟨g', hg⟩ := hg
  use f' + g'
  rw [← Lp.toTemperedDistributionCLM_apply]
  simp [map_add, hf, hg]

theorem MemSobolev.sub {s : ℝ} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] {f g : 𝓢'(E, F)}
    (hf : MemSobolev s p f) (hg : MemSobolev s p g) : MemSobolev s p (f - g) := by
  obtain ⟨f', hf⟩ := hf
  obtain ⟨g', hg⟩ := hg
  use f' - g'
  rw [← Lp.toTemperedDistributionCLM_apply]
  simp [map_sub, hf, hg]

theorem MemSobolev.neg {s : ℝ} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] {f : 𝓢'(E, F)}
    (hf : MemSobolev s p f) : MemSobolev s p (-f) := by
  obtain ⟨f', hf⟩ := hf
  use -f'
  rw [← Lp.toTemperedDistributionCLM_apply]
  simp [map_neg, hf]

theorem MemSobolev.smul {s : ℝ} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] (c : ℂ) {f : 𝓢'(E, F)}
    (hf : MemSobolev s p f) : MemSobolev s p (c • f) := by
  obtain ⟨f', hf⟩ := hf
  use c • f'
  rw [← Lp.toTemperedDistributionCLM_apply]
  simp [hf]

variable (E F) in
@[simp]
theorem memSobolev_fun_zero (s : ℝ) (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] :
    MemSobolev s p (0 : 𝓢'(E, F)) := by
  use 0
  rw [← Lp.toTemperedDistributionCLM_apply]
  simp only [map_zero]

@[simp]
theorem memSobolev_besselPotential_iff {s r : ℝ} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] {f : 𝓢'(E, F)} :
    MemSobolev s p (besselPotential E F r f) ↔ MemSobolev (r + s) p f := by
  simp [MemSobolev]

set_option backward.isDefEq.respectTransparency false in
/-- Schwartz functions are in every Sobolev space. -/
theorem _root_.SchwartzMap.memSobolev {s : ℝ} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] (f : 𝓢(E, F)) :
    MemSobolev s p (f : 𝓢'(E, F)) := by
  use (SchwartzMap.fourierMultiplierCLM F (fun x ↦ ((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ)) f).toLp p
  rw [besselPotential, Lp.toTemperedDistribution_toLp_eq,
    fourierMultiplierCLM_toTemperedDistributionCLM_eq (by fun_prop)]
  congr 1
  apply SchwartzMap.fourierMultiplierCLM_ofReal ℂ
    (Function.hasTemperateGrowth_one_add_norm_sq_rpow E (s / 2))

end normed

section inner

variable [InnerProductSpace ℂ F] [CompleteSpace F]

/-- A tempered distribution belongs to the Sobolev space of order `s` and `p = 2` if and only if
its Fourier transform multiplied by `(1 + ‖x‖ ^ 2) ^ (s / 2)` is in `Lp`. -/
theorem memSobolev_iff_exists_smulLeftCLM_fourier {s : ℝ} {f : 𝓢'(E, F)} :
    MemSobolev s 2 f ↔ ∃ (f' : Lp F 2 (volume : Measure E)),
    smulLeftCLM F (fun x ↦ ((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ)) (𝓕 f) = f' := by
  constructor
  · intro ⟨f', hf'⟩
    use 𝓕 f'
    apply_fun 𝓕 at hf'
    rw [fourier_besselPotential_eq_smulLeftCLM_fourier_apply] at hf'
    rw [hf', Lp.fourier_toTemperedDistribution_eq f']
  · intro ⟨f', hf'⟩
    use 𝓕⁻ f'
    rw [besselPotential, TemperedDistribution.fourierMultiplierCLM_apply]
    apply_fun 𝓕⁻ at hf'
    rw [hf', Lp.fourierInv_toTemperedDistribution_eq f']

theorem memSobolev_zero_iff_exists_fourier {f : 𝓢'(E, F)} :
    MemSobolev 0 2 f ↔ ∃ (f' : Lp F 2 (volume : Measure E)), 𝓕 f = f' := by
  simp [memSobolev_iff_exists_smulLeftCLM_fourier]

/-- The Fourier transform of a Sobolev function of order `s` with `s > d / 2` can be represented by
a `L1` function.

This is the main calculation of the Sobolev embedding theorem. -/
theorem MemSobolev.fourier_memL1 {s : ℝ} (hs : Module.finrank ℝ E < 2 * s) {f : 𝓢'(E, F)}
    (hf : MemSobolev s 2 f) :
    ∃ (v : Lp F 1 (volume : Measure E)), 𝓕 f = (v : 𝓢'(E, F)) := by
  obtain ⟨u, hu⟩ := memSobolev_iff_exists_smulLeftCLM_fourier.mp hf
  have : MemLp (fun x : E ↦ (1 + ‖x‖ ^ 2) ^ (-s / 2)) 2 := by
    constructor
    · have : (fun x : E ↦ (1 + ‖x‖ ^ 2) ^ (-s / 2)).HasTemperateGrowth := by
        fun_prop
      exact this.1.continuous.aestronglyMeasurable
    · rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
      suffices h : ∫⁻ a : E, ENNReal.ofReal ‖(1 + ‖a‖ ^ 2) ^ (-s)‖ < ⊤ from by
        norm_cast
        simp_rw [ofReal_norm] at h
        simp_rw [← enorm_pow]
        convert h using 4
        rw [← Real.rpow_mul_natCast (by positivity)]
        simp
      apply ((integrable_rpow_neg_one_add_norm_sq hs).congr _).lintegral_lt_top
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_eq_self.mpr (by positivity)]
      congr
      ring
  have : MemLp (fun x : E ↦ Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-s / 2) : ℝ)) 2 := this.ofReal
  use this.toLp • u
  rw [MeasureTheory.Lp.toTemperedDistribution_smul_eq]
  · rw [← hu, smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop)]
    convert (smulLeftCLM_const 1 (𝓕 f)).symm using 1
    · simp
    · congr
      ext x
      rw [Pi.mul_apply]
      norm_cast
      rw [← Real.rpow_add (by positivity)]
      ring_nf
      simp
  · fun_prop

open scoped BoundedContinuousFunction

/-- The Fourier multiplier with a bounded function maps `H ^ s` to `H ^ s`. -/
theorem MemSobolev.fourierMultiplierCLM_of_bounded {s : ℝ} {f : 𝓢'(E, F)}
    (hf : MemSobolev s 2 f) {g : E → ℂ} (hg₁ : g.HasTemperateGrowth) (hg₂ : ∃ C, ∀ x, ‖g x‖ ≤ C) :
    MemSobolev s 2 (fourierMultiplierCLM F g f) := by
  rw [memSobolev_iff_exists_smulLeftCLM_fourier] at hf ⊢
  obtain ⟨f', hf⟩ := hf
  obtain ⟨C, hC⟩ := hg₂
  set g' : E →ᵇ ℂ := BoundedContinuousFunction.ofNormedAddCommGroup g hg₁.1.continuous C hC
  use (g'.memLp_top.toLp _ (μ := volume)) • f'
  rw [MeasureTheory.Lp.toTemperedDistribution_smul_eq (by apply hg₁), ← hf,
    fourierMultiplierCLM_apply, fourier_fourierInv_eq,
    smulLeftCLM_smulLeftCLM_apply hg₁ (by fun_prop),
    smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by apply hg₁)]
  congr 2
  ext x
  rw [mul_comm]
  congr

theorem MemSobolev.mono {s s' : ℝ} (h : s' ≤ s) {f : 𝓢'(E, F)} (hf : MemSobolev s 2 f) :
    MemSobolev s' 2 f := by
  have h' : (s' - s) / 2 ≤ 0 := by
    rw [div_le_iff₀ (by norm_num)]
    simp [h]
  have hs : s' = (s' - s) + s := by ring
  rw [hs, ← memSobolev_besselPotential_iff]
  apply hf.fourierMultiplierCLM_of_bounded (by fun_prop)
  use 1
  intro x
  rw [Complex.norm_real, Real.norm_eq_abs, abs_eq_self.mpr (by positivity)]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by simp) h'

section LineDeriv

open scoped LineDeriv Laplacian Real

/-- The directional derivative maps `H ^ s` to `H ^ {s - 1}`. -/
theorem MemSobolev.lineDerivOp {s : ℝ} {f : 𝓢'(E, F)} (hf : MemSobolev s 2 f) {m : E} :
    MemSobolev (s - 1) 2 (∂_{m} f) := by
  rw [SubNegMonoid.sub_eq_add_neg s 1, add_comm, ← memSobolev_besselPotential_iff,
    besselPotential_neg_one_lineDerivOp_eq f]
  apply (hf.fourierMultiplierCLM_of_bounded (by fun_prop) ?_).smul
  use ‖m‖
  intro x
  apply le_of_sq_le_sq _ (by positivity)
  simp only [Complex.ofReal_mul, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
  have h₁ : |(1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ)| ^ 2 = (1 + ‖x‖ ^ 2)⁻¹ := by
    field_simp
    norm_cast
    rw [Real.rpow_neg (by positivity), sq_abs, inv_pow]
    field_simp
    calc
      _ = ((1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
        rw [← Real.rpow_mul (by positivity)]; simp
      _ = _ := by simp
  have h₂ : |inner ℝ x m| ^ 2 ≤ ‖m‖ ^ 2 * (1 + ‖x‖ ^ 2) := by
    grw [abs_real_inner_le_norm]
    rw [mul_pow, mul_comm]
    gcongr
    simp
  grw [h₁, h₂]
  apply le_of_eq
  field_simp

/-- The Laplacian maps `H ^ s` to `H ^ {s - 2}`. -/
theorem MemSobolev.laplacian {s : ℝ} {f : 𝓢'(E, F)} (hf : MemSobolev s 2 f) :
    MemSobolev (s - 2) 2 (Δ f) := by
  rw [SubNegMonoid.sub_eq_add_neg s 2, add_comm, ← memSobolev_besselPotential_iff,
    besselPotential_neg_two_laplacian_eq f]
  apply (hf.fourierMultiplierCLM_of_bounded (by fun_prop) ?_).smul
  use 1
  intro x
  rw [Real.rpow_neg (by positivity)]
  norm_cast
  simp only [norm_mul, norm_pow, abs_norm, norm_inv, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity), mul_inv_le_iff₀ (by positivity)]
  grind

end LineDeriv

end inner

end TemperedDistribution
