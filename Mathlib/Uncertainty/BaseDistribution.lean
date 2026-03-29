/-
Copyright (c) 2026 Prof. Dr. Fei Gao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prof. Dr. Fei Gao <gaof@whut.edu.cn>
-/

module

public import Mathlib.Uncertainty.BaseCore

/-! # Uncertainty Distribution -/

@[expose] public section

open Filter
open scoped Topology
open scoped BigOperators

noncomputable section

namespace Uncertainty

/-- Parameters for a linear uncertain distribution. -/
structure LinearParams where
  /-- Lower bound. -/
  a : ℝ
  /-- Upper bound. -/
  b : ℝ
  /-- Lower bound is less than upper bound. -/
  h_lt : a < b

/-- Linear uncertain distribution function. -/
noncomputable def linearDistribution (params : LinearParams) (x : ℝ) : ℝ :=
  if x < params.a then 0
  else if x > params.b then 1
  else (x - params.a) / (params.b - params.a)

/-- Inverse function for linear uncertain distribution (quantile function). -/
noncomputable def linearInverse (params : LinearParams) (α : ℝ) : ℝ :=
  if α = 0 then params.a
  else if α = 1 then params.b
  else params.a + α * (params.b - params.a)
@[simp] theorem linearDistribution_of_lt (params : LinearParams) {x : ℝ}
    (hx : x < params.a) : linearDistribution params x = 0 := by
  simp [linearDistribution, hx]

@[simp] theorem linearDistribution_of_gt (params : LinearParams) {x : ℝ}
    (hx : x > params.b) : linearDistribution params x = 1 := by
  have hxa : ¬ x < params.a := not_lt_of_gt (lt_trans params.h_lt hx)
  simp [linearDistribution, hxa, hx]

theorem linearDistribution_of_mem_Icc (params : LinearParams) {x : ℝ}
    (hx : x ∈ Set.Icc params.a params.b) :
    linearDistribution params x = (x - params.a) / (params.b - params.a) := by
  rcases hx with ⟨hxa, hxb⟩
  have hnot_lt_a : ¬ x < params.a := not_lt_of_ge hxa
  have hnot_gt_b : ¬ x > params.b := not_lt_of_ge hxb
  simp [linearDistribution, hnot_lt_a, hnot_gt_b]

/-- Auxiliary lemma: when x ∈ [a,b], the distribution value is in [0,1]. -/
lemma linearDistribution_mem_Icc (params : LinearParams) {x : ℝ}
    (hx : x ∈ Set.Icc params.a params.b) :
    linearDistribution params x ∈ Set.Icc 0 1 := by
  -- The linear distribution maps [a,b] to [0,1] by construction
  rw [linearDistribution_of_mem_Icc params hx]
  let r := (x - params.a) / (params.b - params.a)
  have hr : r ∈ Set.Icc 0 1 := by
    constructor
    · apply div_nonneg
      · linarith [hx.1]
      · linarith [params.h_lt]
    · apply div_le_one_of_le₀
      · linarith [hx.2]
      · linarith [params.h_lt]
  exact hr

/-- Theorem: linear distribution satisfies the properties of an uncertain distribution. -/
theorem linearDistribution_is_uncertain (params : LinearParams) :
    let Φ := linearDistribution params
    (∀ x, x < params.a → Φ x = 0) ∧
    (∀ x, x > params.b → Φ x = 1) ∧
    (∀ x ∈ Set.Icc params.a params.b, Φ x ∈ Set.Icc 0 1) := by
  let Φ := linearDistribution params
  constructor
  · intro x hx
    exact linearDistribution_of_lt params hx
  · constructor
    · intro x hx
      exact linearDistribution_of_gt params hx
    · intro x hx
      exact linearDistribution_mem_Icc params hx

@[simp] theorem linearInverse_zero (params : LinearParams) :
    linearInverse params 0 = params.a := by
  simp [linearInverse]

@[simp] theorem linearInverse_one (params : LinearParams) :
    linearInverse params 1 = params.b := by
  simp [linearInverse]

lemma linearInverse_eq_affine (params : LinearParams) {α : ℝ}
    (hα : α ∈ Set.Icc 0 1) :
    linearInverse params α = params.a + α * (params.b - params.a) := by
  rcases hα with ⟨h0, h1⟩
  rcases lt_or_eq_of_le h0 with hlt0 | rfl
  · rcases lt_or_eq_of_le h1 with hlt1 | rfl
    · simp [linearInverse, ne_of_gt hlt0, ne_of_lt hlt1]
    · -- α = 1
      simp [linearInverse, ne_of_gt hlt0]
  · -- α = 0
    simp [linearInverse]

/-- The expected value of an uncertain variable with linear distribution. -/
noncomputable def uncertainExpectedValue (params : LinearParams) : ℝ :=
  ∫ α in (0 : ℝ)..1, if α ∈ Set.Icc 0 1 then linearInverse params α else 0

/-- Integral of the affine form on [0,1]. -/
lemma integral_affine (params : LinearParams) :
    (∫ α in (0 : ℝ)..1, params.a + α * (params.b - params.a)) = (params.a + params.b) / 2 := by
  have h_const : ∫ α in (0 : ℝ)..1, (params.a : ℝ) = params.a := by
    norm_num [intervalIntegral.integral_const]
  have h_id : ∫ α in (0 : ℝ)..1, α = (1 : ℝ) / (2 : ℝ) := by
    norm_num [integral_id]
  have h_lin : ∫ α in (0 : ℝ)..1, α * (params.b - params.a)
      = (params.b - params.a) * ((1 : ℝ) / (2 : ℝ)) := by
    have hmul : ∫ α in (0 : ℝ)..1, α * (params.b - params.a)
        = (∫ α in (0 : ℝ)..1, α) * (params.b - params.a) := by
      exact (intervalIntegral.integral_mul_const
        (a := (0 : ℝ)) (b := 1) (r := (params.b - params.a)) (f := fun α => α))
    calc
      ∫ α in (0 : ℝ)..1, α * (params.b - params.a)
          = (∫ α in (0 : ℝ)..1, α) * (params.b - params.a) := hmul
      _ = ((1 : ℝ) / (2 : ℝ)) * (params.b - params.a) := by rw [h_id]
      _ = (params.b - params.a) * ((1 : ℝ) / (2 : ℝ)) := by ring
  calc
    (∫ α in (0 : ℝ)..1, params.a + α * (params.b - params.a))
        = (∫ α in (0 : ℝ)..1, (params.a : ℝ)) + ∫ α in (0 : ℝ)..1, α * (params.b - params.a) := by
          have h_add := intervalIntegral.integral_add
            (μ := MeasureTheory.volume)
            (f := fun α => (params.a : ℝ)) (g := fun α => α * (params.b - params.a))
            (a := (0 : ℝ)) (b := 1)
            (hf := intervalIntegral.intervalIntegrable_const (μ := MeasureTheory.volume))
            (hg := (intervalIntegral.intervalIntegrable_id (μ := MeasureTheory.volume)).mul_const
              (params.b - params.a))
          exact h_add
    _ = params.a + (params.b - params.a) * ((1 : ℝ) / (2 : ℝ)) := by
          simp [h_const, h_lin]
    _ = (params.a + params.b) / 2 := by ring

/-- For linear uncertain distributions, the expected value has a simple formula. -/
theorem linearExpectedValue (params : LinearParams) :
    uncertainExpectedValue params = (params.a + params.b) / 2 := by
  unfold uncertainExpectedValue
  -- ∫_0^1 linearInverse params α dα = ∫_0^1 (params.a + α * (params.b - params.a)) dα
  have h_eq : ∀ α ∈ Set.Icc (0 : ℝ) 1,
      (if α ∈ Set.Icc 0 1 then linearInverse params α else 0)
        = params.a + α * (params.b - params.a) := by
    intro α hα
    simp [hα]
    simpa using linearInverse_eq_affine params hα
  -- Therefore, the integral equals ∫_0^1 (params.a + α * (params.b - params.a)) dα
  have h_int :
      ∫ α in (0 : ℝ)..1, (if α ∈ Set.Icc 0 1 then linearInverse params α else 0)
        = ∫ α in (0 : ℝ)..1, params.a + α * (params.b - params.a) := by
    apply intervalIntegral.integral_congr
    intro α hα
    have hIcc : α ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hα
    simpa using h_eq α hIcc
  -- Which equals (params.a + params.b) / 2 by integral_affine
  rw [h_int]
  exact integral_affine params

/-- Stage A+B: normal uncertain distribution parameters. -/
structure NormalParams where
  /-- Location parameter. -/
  e : ℝ
  /-- Positive scale parameter. -/
  σ : ℝ
  hσ : 0 < σ

/-- Logistic-form normal uncertain distribution used in uncertainty theory. -/
noncomputable def normalUncertainDistribution (params : NormalParams) (x : ℝ) : ℝ :=
  1 / (1 + Real.exp ((params.e - x) / params.σ))

theorem normalUncertainDistribution_nonneg (params : NormalParams) (x : ℝ) :
    0 ≤ normalUncertainDistribution params x := by
  unfold normalUncertainDistribution
  positivity

theorem normalUncertainDistribution_le_one (params : NormalParams) (x : ℝ) :
    normalUncertainDistribution params x ≤ 1 := by
  unfold normalUncertainDistribution
  refine (div_le_one ?_).2 ?_
  · positivity
  · nlinarith [Real.exp_pos ((params.e - x) / params.σ)]

theorem normalUncertainDistribution_mem_Icc (params : NormalParams) (x : ℝ) :
    normalUncertainDistribution params x ∈ Set.Icc 0 1 := by
  exact ⟨normalUncertainDistribution_nonneg params x, normalUncertainDistribution_le_one params x⟩

/-- Book-scaled normal uncertain distribution (with `π/(√3 σ)` factor). -/
noncomputable def normalUncertainDistributionBook (params : NormalParams) (x : ℝ) : ℝ :=
  1 / (1 + Real.exp ((Real.pi * (params.e - x)) / (Real.sqrt 3 * params.σ)))

theorem normalUncertainDistributionBook_nonneg (params : NormalParams) (x : ℝ) :
    0 ≤ normalUncertainDistributionBook params x := by
  unfold normalUncertainDistributionBook
  positivity

theorem normalUncertainDistributionBook_le_one (params : NormalParams) (x : ℝ) :
    normalUncertainDistributionBook params x ≤ 1 := by
  unfold normalUncertainDistributionBook
  refine (div_le_one ?_).2 ?_
  · positivity
  · nlinarith [Real.exp_pos ((Real.pi * (params.e - x)) / (Real.sqrt 3 * params.σ))]

theorem normalUncertainDistributionBook_mem_Icc (params : NormalParams) (x : ℝ) :
    normalUncertainDistributionBook params x ∈ Set.Icc 0 1 := by
  exact ⟨normalUncertainDistributionBook_nonneg params x,
    normalUncertainDistributionBook_le_one params x⟩

/-- Inverse of book-scaled normal uncertain distribution. -/
noncomputable def normalInverseBook (params : NormalParams) (α : ℝ) : ℝ :=
  params.e + (Real.sqrt 3 * params.σ / Real.pi) * Real.log (α / (1 - α))

/-- Bridge parameters: represent book-normal CDF as legacy-normal CDF with scaled `σ`. -/
noncomputable def normalBookToLegacyParams (params : NormalParams) : NormalParams where
  e := params.e
  σ := (Real.sqrt 3 * params.σ) / Real.pi
  hσ := by
    have hsqrt3 : (0 : ℝ) < Real.sqrt 3 := by
      have h3 : (0 : ℝ) < 3 := by norm_num
      exact Real.sqrt_pos.2 h3
    exact div_pos (mul_pos hsqrt3 params.hσ) Real.pi_pos

/-- Bridge parameters: represent legacy-normal CDF as book-normal CDF with scaled `σ`. -/
noncomputable def normalLegacyToBookParams (params : NormalParams) : NormalParams where
  e := params.e
  σ := (Real.pi / Real.sqrt 3) * params.σ
  hσ := by
    have hsqrt3 : (0 : ℝ) < Real.sqrt 3 := by
      have h3 : (0 : ℝ) < 3 := by norm_num
      exact Real.sqrt_pos.2 h3
    exact mul_pos (div_pos Real.pi_pos hsqrt3) params.hσ

theorem normalUncertainDistributionBook_eq_normalUncertainDistribution_scaled
    (params : NormalParams) (x : ℝ) :
    normalUncertainDistributionBook params x
      = normalUncertainDistribution (normalBookToLegacyParams params) x := by
  have hsqrt3_pos : (0 : ℝ) < Real.sqrt 3 := by
    have h3 : (0 : ℝ) < 3 := by norm_num
    exact Real.sqrt_pos.2 h3
  have hsqrt3_ne : (Real.sqrt 3 : ℝ) ≠ 0 := ne_of_gt hsqrt3_pos
  have hσ_ne : params.σ ≠ 0 := ne_of_gt params.hσ
  have hscale :
      (params.e - x) / ((Real.sqrt 3 * params.σ) / Real.pi)
        = (Real.pi * (params.e - x)) / (Real.sqrt 3 * params.σ) := by
    field_simp [Real.pi_ne_zero, hsqrt3_ne, hσ_ne]
  simp [normalUncertainDistributionBook, normalUncertainDistribution,
    normalBookToLegacyParams, hscale]

theorem normalUncertainDistribution_eq_normalUncertainDistributionBook_scaled
    (params : NormalParams) (x : ℝ) :
    normalUncertainDistribution params x
      = normalUncertainDistributionBook (normalLegacyToBookParams params) x := by
  have hsqrt3_pos : (0 : ℝ) < Real.sqrt 3 := by
    have h3 : (0 : ℝ) < 3 := by norm_num
    exact Real.sqrt_pos.2 h3
  have hsqrt3_ne : (Real.sqrt 3 : ℝ) ≠ 0 := ne_of_gt hsqrt3_pos
  have hσ_ne : params.σ ≠ 0 := ne_of_gt params.hσ
  have hscale :
      (Real.pi * (params.e - x)) / (Real.sqrt 3 * ((Real.pi / Real.sqrt 3) * params.σ))
        = (params.e - x) / params.σ := by
    field_simp [Real.pi_ne_zero, hsqrt3_ne, hσ_ne]
  simp [normalUncertainDistributionBook, normalUncertainDistribution,
    normalLegacyToBookParams, hscale]

/-- Unified entry for the two normal-CDF conventions. -/
inductive NormalDistributionForm
  | legacy
  | book

/-- Evaluate normal uncertain distribution in either legacy or book convention. -/
noncomputable def normalDistributionUnified
    (form : NormalDistributionForm) (params : NormalParams) (x : ℝ) : ℝ :=
  match form with
  | .legacy => normalUncertainDistribution params x
  | .book => normalUncertainDistributionBook params x

@[simp] theorem normalDistributionUnified_legacy (params : NormalParams) (x : ℝ) :
    normalDistributionUnified .legacy params x = normalUncertainDistribution params x := rfl

@[simp] theorem normalDistributionUnified_book (params : NormalParams) (x : ℝ) :
    normalDistributionUnified .book params x = normalUncertainDistributionBook params x := rfl

theorem normalDistributionUnified_book_as_legacy_scaled (params : NormalParams) (x : ℝ) :
    normalDistributionUnified .book params x
      = normalDistributionUnified .legacy (normalBookToLegacyParams params) x := by
  simpa [normalDistributionUnified] using
    normalUncertainDistributionBook_eq_normalUncertainDistribution_scaled params x

theorem normalDistributionUnified_legacy_as_book_scaled (params : NormalParams) (x : ℝ) :
    normalDistributionUnified .legacy params x
      = normalDistributionUnified .book (normalLegacyToBookParams params) x := by
  simpa [normalDistributionUnified] using
    normalUncertainDistribution_eq_normalUncertainDistributionBook_scaled params x

/-- Stage A+B: zigzag uncertain distribution parameters. -/
structure ZigzagParams where
  /-- Left endpoint. -/
  a : ℝ
  /-- Peak location. -/
  b : ℝ
  /-- Right endpoint. -/
  c : ℝ
  h_ab : a < b
  h_bc : b < c

/-- Zigzag uncertain distribution. -/
noncomputable def zigzagDistribution (params : ZigzagParams) (x : ℝ) : ℝ :=
  if x ≤ params.a then 0
  else if x ≥ params.c then 1
  else if x ≤ params.b then (x - params.a) / (2 * (params.b - params.a))
  else 1 - (params.c - x) / (2 * (params.c - params.b))

@[simp] theorem zigzag_left (params : ZigzagParams) {x : ℝ} (hx : x ≤ params.a) :
    zigzagDistribution params x = 0 := by
  simp [zigzagDistribution, hx]

@[simp] theorem zigzag_right (params : ZigzagParams) {x : ℝ} (hx : params.c ≤ x) :
    zigzagDistribution params x = 1 := by
  have hxa : ¬ x ≤ params.a := by linarith [params.h_ab, params.h_bc, hx]
  simp [zigzagDistribution, hxa, hx]

theorem zigzagDistribution_nonneg (params : ZigzagParams) (x : ℝ) :
    0 ≤ zigzagDistribution params x := by
  unfold zigzagDistribution
  split_ifs with hxa hxc hxb
  · simp
  · simp
  · have hxa' : params.a < x := lt_of_not_ge hxa
    apply div_nonneg
    · linarith
    · nlinarith [params.h_ab]
  · have hxb' : params.b < x := lt_of_not_ge hxb
    have hxc' : x < params.c := lt_of_not_ge hxc
    have hT_le_one : (params.c - x) / (2 * (params.c - params.b)) ≤ 1 := by
      have hden_pos : 0 < 2 * (params.c - params.b) := by nlinarith [params.h_bc]
      refine (div_le_one hden_pos).2 ?_
      linarith
    linarith

theorem zigzagDistribution_le_one (params : ZigzagParams) (x : ℝ) :
    zigzagDistribution params x ≤ 1 := by
  unfold zigzagDistribution
  split_ifs with hxa hxc hxb
  · simp
  · simp
  · have hden_pos : 0 < 2 * (params.b - params.a) := by nlinarith [params.h_ab]
    exact (div_le_one hden_pos).2 (by linarith)
  · have hxb' : params.b < x := lt_of_not_ge hxb
    have hxc' : x < params.c := lt_of_not_ge hxc
    have hT_nonneg : 0 ≤ (params.c - x) / (2 * (params.c - params.b)) := by
      apply div_nonneg
      · linarith
      · nlinarith [params.h_bc]
    linarith

theorem zigzagDistribution_mem_Icc (params : ZigzagParams) (x : ℝ) :
    zigzagDistribution params x ∈ Set.Icc 0 1 := by
  exact ⟨zigzagDistribution_nonneg params x, zigzagDistribution_le_one params x⟩

/-- Inverse of zigzag uncertain distribution. -/
noncomputable def zigzagInverse (params : ZigzagParams) (α : ℝ) : ℝ :=
  if α < (1 / 2 : ℝ) then
    (1 - 2 * α) * params.a + (2 * α) * params.b
  else
    (2 - 2 * α) * params.b + (2 * α - 1) * params.c

/-- Lognormal uncertain distribution in book form. -/
noncomputable def lognormalUncertainDistribution (params : NormalParams) (x : ℝ) : ℝ :=
  if x ≤ 0 then 0
  else normalUncertainDistributionBook params (Real.log x)

/-- Inverse of lognormal uncertain distribution in book form. -/
noncomputable def lognormalInverseBook (params : NormalParams) (α : ℝ) : ℝ :=
  Real.exp (normalInverseBook params α)

/-- Stage B: weak distribution interface for reusable CDF-style families. -/
class UncertainDistributionLike (D : Type _) where
  /-- Distribution function of an element of `D`. -/
  cdf : D → ℝ → ℝ
  cdf_nonneg : ∀ d x, 0 ≤ cdf d x
  cdf_le_one : ∀ d x, cdf d x ≤ 1

/-- Regular-distribution interface aligned with book Def 3.3/3.4. -/
class RegularDistributionLike (D : Type _) [UncertainDistributionLike D] where
  cdf_continuous : ∀ d, Continuous (UncertainDistributionLike.cdf (D := D) d)
  cdf_strictMonoOn : ∀ d,
    StrictMonoOn (UncertainDistributionLike.cdf (D := D) d)
      {x : ℝ | 0 < UncertainDistributionLike.cdf (D := D) d x
        ∧ UncertainDistributionLike.cdf (D := D) d x < 1}
  cdf_tendsto_atBot : ∀ d, Tendsto (UncertainDistributionLike.cdf (D := D) d) atBot (𝓝 0)
  cdf_tendsto_atTop : ∀ d, Tendsto (UncertainDistributionLike.cdf (D := D) d) atTop (𝓝 1)
  /-- Inverse distribution/quantile map. -/
  inverse : D → ℝ → ℝ

/-- Totalized linear inverse used by `RegularDistributionLike`. -/
noncomputable def linearInverseTotal (params : LinearParams) (α : ℝ) : ℝ :=
  if _hα : α ∈ Set.Icc (0 : ℝ) 1 then linearInverse params α
  else if α < 0 then params.a else params.b

-- [ENGINEERING_AXIOM] Regularity assumptions (replace progressively by proved lemmas).
/-- Regularity assumptions for linear uncertain distributions. -/
class LinearDistributionRegularityStructure where
  continuous : ∀ params : LinearParams, Continuous (linearDistribution params)
  tendsto_atBot : ∀ params : LinearParams, Tendsto (linearDistribution params) atBot (𝓝 0)
  tendsto_atTop : ∀ params : LinearParams, Tendsto (linearDistribution params) atTop (𝓝 1)

theorem linearDistribution_continuous (params : LinearParams)
    [LinearDistributionRegularityStructure] :
    Continuous (linearDistribution params) :=
  LinearDistributionRegularityStructure.continuous params

theorem linearDistribution_strictMonoOn_core (params : LinearParams) :
  StrictMonoOn (linearDistribution params)
    {x : ℝ | 0 < linearDistribution params x ∧ linearDistribution params x < 1} := by
  intro x hx y hy hxy
  have hxIcc : x ∈ Set.Icc params.a params.b := by
    constructor
    · by_contra hxa
      have hlt : x < params.a := lt_of_not_ge hxa
      have hx0 : linearDistribution params x = 0 := linearDistribution_of_lt params hlt
      linarith [hx.1, hx0]
    · by_contra hxb
      have hgt : x > params.b := lt_of_not_ge hxb
      have hx1 : linearDistribution params x = 1 := linearDistribution_of_gt params hgt
      linarith [hx.2, hx1]
  have hyIcc : y ∈ Set.Icc params.a params.b := by
    constructor
    · by_contra hya
      have hlt : y < params.a := lt_of_not_ge hya
      have hy0 : linearDistribution params y = 0 := linearDistribution_of_lt params hlt
      linarith [hy.1, hy0]
    · by_contra hyb
      have hgt : y > params.b := lt_of_not_ge hyb
      have hy1 : linearDistribution params y = 1 := linearDistribution_of_gt params hgt
      linarith [hy.2, hy1]
  rw [linearDistribution_of_mem_Icc params hxIcc, linearDistribution_of_mem_Icc params hyIcc]
  have hden : 0 < params.b - params.a := sub_pos.mpr params.h_lt
  have hnum : x - params.a < y - params.a := by linarith
  exact div_lt_div_of_pos_right hnum hden

theorem linearDistribution_tendsto_atBot (params : LinearParams)
    [LinearDistributionRegularityStructure] :
    Tendsto (linearDistribution params) atBot (𝓝 0) :=
  LinearDistributionRegularityStructure.tendsto_atBot params

theorem linearDistribution_tendsto_atTop (params : LinearParams)
    [LinearDistributionRegularityStructure] :
    Tendsto (linearDistribution params) atTop (𝓝 1) :=
  LinearDistributionRegularityStructure.tendsto_atTop params

theorem normalUncertainDistribution_continuous (params : NormalParams) :
  Continuous (normalUncertainDistribution params) := by
  unfold normalUncertainDistribution
  have hden_cont : Continuous (fun x : ℝ => 1 + Real.exp ((params.e - x) / params.σ)) := by
    continuity
  refine Continuous.div continuous_const hden_cont ?_
  intro x
  have hpos : 0 < 1 + Real.exp ((params.e - x) / params.σ) := by
    nlinarith [Real.exp_pos ((params.e - x) / params.σ)]
  exact ne_of_gt hpos
/-- Regularity assumptions for normal uncertain distributions. -/
class NormalDistributionRegularityStructure where
  strictMonoOn_core : ∀ params : NormalParams,
    StrictMonoOn (normalUncertainDistribution params)
      {x : ℝ | 0 < normalUncertainDistribution params x ∧ normalUncertainDistribution params x < 1}

theorem normalUncertainDistribution_strictMonoOn_core (params : NormalParams)
    [NormalDistributionRegularityStructure] :
  StrictMonoOn (normalUncertainDistribution params)
    {x : ℝ | 0 < normalUncertainDistribution params x ∧ normalUncertainDistribution params x < 1} :=
  NormalDistributionRegularityStructure.strictMonoOn_core params
theorem normalUncertainDistribution_tendsto_atBot (params : NormalParams) :
  Tendsto (normalUncertainDistribution params) atBot (𝓝 0) := by
  have hlin : Tendsto (fun x : ℝ => (params.e - x) / params.σ) atBot atTop := by
    have hneg : Tendsto (fun x : ℝ => -x) atBot atTop :=
      Filter.tendsto_neg_atBot_atTop.comp Filter.tendsto_id
    have hsub : Tendsto (fun x : ℝ => -x + params.e) atBot atTop :=
      hneg.atTop_add tendsto_const_nhds
    have hσinv : 0 < params.σ⁻¹ := by
      simpa [one_div] using (inv_pos.mpr params.hσ)
    have hmul : Tendsto (fun x : ℝ => (-x + params.e) * (params.σ⁻¹)) atBot atTop :=
      hsub.atTop_mul_const hσinv
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, div_eq_mul_inv] using hmul
  have hexp : Tendsto (fun x : ℝ => Real.exp ((params.e - x) / params.σ)) atBot atTop :=
    Real.tendsto_exp_atTop.comp hlin
  have hden : Tendsto (fun x : ℝ => 1 + Real.exp ((params.e - x) / params.σ)) atBot atTop :=
    tendsto_const_nhds.add_atTop hexp
  have hinv : Tendsto (fun x : ℝ => (1 + Real.exp ((params.e - x) / params.σ))⁻¹) atBot (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hden
  have hrepr :
      normalUncertainDistribution params
        = (fun x : ℝ => (1 + Real.exp ((params.e - x) / params.σ))⁻¹) := by
    funext x
    simp [normalUncertainDistribution, one_div]
  simpa [hrepr] using hinv

theorem normalUncertainDistribution_tendsto_atTop (params : NormalParams) :
  Tendsto (normalUncertainDistribution params) atTop (𝓝 1) := by
  have hlin : Tendsto (fun x : ℝ => (params.e - x) / params.σ) atTop atBot := by
    have hneg : Tendsto (fun x : ℝ => -x) atTop atBot :=
      Filter.tendsto_neg_atTop_atBot.comp Filter.tendsto_id
    have hsub : Tendsto (fun x : ℝ => -x + params.e) atTop atBot :=
      hneg.atBot_add tendsto_const_nhds
    have hσinv : 0 < params.σ⁻¹ := by
      simpa [one_div] using (inv_pos.mpr params.hσ)
    have hmul : Tendsto (fun x : ℝ => (-x + params.e) * (params.σ⁻¹)) atTop atBot :=
      hsub.atBot_mul_const hσinv
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, div_eq_mul_inv] using hmul
  have hexp0 : Tendsto (fun x : ℝ => Real.exp ((params.e - x) / params.σ)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hlin
  have hden1 :
      Tendsto (fun x : ℝ => 1 + Real.exp ((params.e - x) / params.σ))
        atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add hexp0
  have hinv1 :
      Tendsto (fun x : ℝ => (1 + Real.exp ((params.e - x) / params.σ))⁻¹)
        atTop (𝓝 ((1 + 0)⁻¹)) := by
    refine Tendsto.inv₀ hden1 ?_
    norm_num
  have hrepr :
      normalUncertainDistribution params
        = (fun x : ℝ => (1 + Real.exp ((params.e - x) / params.σ))⁻¹) := by
    funext x
    simp [normalUncertainDistribution, one_div]
  simpa [hrepr] using hinv1

/-- Regularity assumptions for zigzag uncertain distributions. -/
class ZigzagDistributionRegularityStructure where
  continuous : ∀ params : ZigzagParams, Continuous (zigzagDistribution params)
  strictMonoOn_core : ∀ params : ZigzagParams,
    StrictMonoOn (zigzagDistribution params)
      {x : ℝ | 0 < zigzagDistribution params x ∧ zigzagDistribution params x < 1}
  tendsto_atBot : ∀ params : ZigzagParams, Tendsto (zigzagDistribution params) atBot (𝓝 0)
  tendsto_atTop : ∀ params : ZigzagParams, Tendsto (zigzagDistribution params) atTop (𝓝 1)

theorem zigzagDistribution_continuous (params : ZigzagParams)
    [ZigzagDistributionRegularityStructure] :
    Continuous (zigzagDistribution params) :=
  ZigzagDistributionRegularityStructure.continuous params

theorem zigzagDistribution_strictMonoOn_core (params : ZigzagParams)
    [ZigzagDistributionRegularityStructure] :
    StrictMonoOn (zigzagDistribution params)
      {x : ℝ | 0 < zigzagDistribution params x ∧ zigzagDistribution params x < 1} :=
  ZigzagDistributionRegularityStructure.strictMonoOn_core params

theorem zigzagDistribution_tendsto_atBot (params : ZigzagParams)
    [ZigzagDistributionRegularityStructure] :
    Tendsto (zigzagDistribution params) atBot (𝓝 0) :=
  ZigzagDistributionRegularityStructure.tendsto_atBot params

theorem zigzagDistribution_tendsto_atTop (params : ZigzagParams)
    [ZigzagDistributionRegularityStructure] :
    Tendsto (zigzagDistribution params) atTop (𝓝 1) :=
  ZigzagDistributionRegularityStructure.tendsto_atTop params

theorem linearDistribution_nonneg (params : LinearParams) (x : ℝ) :
    0 ≤ linearDistribution params x := by
  by_cases hxa : x < params.a
  · simp [linearDistribution, hxa]
  · by_cases hxb : x > params.b
    · simp [linearDistribution, hxa, hxb]
    · have hax : params.a ≤ x := le_of_not_gt hxa
      have hxb' : x ≤ params.b := le_of_not_gt hxb
      rw [linearDistribution_of_mem_Icc params ⟨hax, hxb'⟩]
      apply div_nonneg
      · linarith
      · linarith [params.h_lt]

theorem linearDistribution_le_one (params : LinearParams) (x : ℝ) :
    linearDistribution params x ≤ 1 := by
  by_cases hxa : x < params.a
  · simp [linearDistribution, hxa]
  · by_cases hxb : x > params.b
    · simp [linearDistribution, hxa, hxb]
    · have hax : params.a ≤ x := le_of_not_gt hxa
      have hxb' : x ≤ params.b := le_of_not_gt hxb
      rw [linearDistribution_of_mem_Icc params ⟨hax, hxb'⟩]
      have hden_pos : 0 < params.b - params.a := by linarith [params.h_lt]
      have hnum_le : x - params.a ≤ params.b - params.a := by linarith
      have hfrac_le : (x - params.a) / (params.b - params.a)
          ≤ (params.b - params.a) / (params.b - params.a) :=
        div_le_div_of_nonneg_right hnum_le (le_of_lt hden_pos)
      have hden_ne : params.b - params.a ≠ 0 := by
        exact sub_ne_zero.mpr (ne_of_gt params.h_lt)
      calc
        (x - params.a) / (params.b - params.a)
            ≤ (params.b - params.a) / (params.b - params.a) := hfrac_le
        _ = 1 := by field_simp [hden_ne]

instance : UncertainDistributionLike LinearParams where
  cdf := linearDistribution
  cdf_nonneg := linearDistribution_nonneg
  cdf_le_one := linearDistribution_le_one

/-- Operational-law interface for transformed inverse distributions (book Thm 3.2 style). -/
class OperationalLawStructure (U : UncertainSpace) where
  inverse_transform_formula :
    ∀ (invX invY invZ : ℝ → ℝ)
      (f : ℝ → ℝ → ℝ),
      ∀ α, invZ α = f (invX α) (invY α)

theorem operational_inverse_transform_formula (U : UncertainSpace)
    [OperationalLawStructure U]
    (invX invY invZ : ℝ → ℝ) (f : ℝ → ℝ → ℝ) :
    ∀ α, invZ α = f (invX α) (invY α) :=
  OperationalLawStructure.inverse_transform_formula (U := U) invX invY invZ f

instance : UncertainDistributionLike NormalParams where
  cdf := normalUncertainDistribution
  cdf_nonneg := normalUncertainDistribution_nonneg
  cdf_le_one := normalUncertainDistribution_le_one

instance : UncertainDistributionLike ZigzagParams where
  cdf := zigzagDistribution
  cdf_nonneg := zigzagDistribution_nonneg
  cdf_le_one := zigzagDistribution_le_one

instance [LinearDistributionRegularityStructure] : RegularDistributionLike LinearParams where
  cdf_continuous := fun d => linearDistribution_continuous d
  cdf_strictMonoOn := linearDistribution_strictMonoOn_core
  cdf_tendsto_atBot := fun d => linearDistribution_tendsto_atBot d
  cdf_tendsto_atTop := fun d => linearDistribution_tendsto_atTop d
  inverse := linearInverseTotal

instance [NormalDistributionRegularityStructure] :
    RegularDistributionLike NormalParams where
  cdf_continuous := normalUncertainDistribution_continuous
  cdf_strictMonoOn := fun d => normalUncertainDistribution_strictMonoOn_core d
  cdf_tendsto_atBot := normalUncertainDistribution_tendsto_atBot
  cdf_tendsto_atTop := normalUncertainDistribution_tendsto_atTop
  inverse := normalInverseBook

instance [ZigzagDistributionRegularityStructure] : RegularDistributionLike ZigzagParams where
  cdf_continuous := fun d => zigzagDistribution_continuous d
  cdf_strictMonoOn := fun d => zigzagDistribution_strictMonoOn_core d
  cdf_tendsto_atBot := fun d => zigzagDistribution_tendsto_atBot d
  cdf_tendsto_atTop := fun d => zigzagDistribution_tendsto_atTop d
  inverse := zigzagInverse

/-- Special-distribution statistics interface (book examples/theorems). -/
noncomputable def linearVarianceClosedForm (params : LinearParams) : ℝ :=
  (params.b - params.a) ^ 2 / 12

/-- Closed-form variance for the normal uncertain distribution. -/
noncomputable def normalVarianceClosedForm (params : NormalParams) : ℝ :=
  params.σ ^ 2

theorem linearVarianceClosedForm_nonneg (params : LinearParams) :
    0 ≤ linearVarianceClosedForm params := by
  unfold linearVarianceClosedForm
  positivity

theorem normalVarianceClosedForm_pos (params : NormalParams) :
    0 < normalVarianceClosedForm params := by
  unfold normalVarianceClosedForm
  nlinarith [params.hσ]

theorem normalInverseBook_median (params : NormalParams) :
    normalInverseBook params (1 / 2 : ℝ) = params.e := by
  unfold normalInverseBook
  have hfrac : ((1 / 2 : ℝ) / (1 - (1 / 2 : ℝ))) = 1 := by norm_num
  rw [hfrac]
  simp

/-- Interface collecting closed-form statistics for special uncertain distributions. -/
class SpecialDistributionStatsStructure where
  linear_expectation : ∀ params : LinearParams,
    uncertainExpectedValue params = (params.a + params.b) / 2
  linear_variance_nonneg : ∀ params : LinearParams,
    0 ≤ linearVarianceClosedForm params
  normal_inverse_median : ∀ params : NormalParams,
    normalInverseBook params (1 / 2 : ℝ) = params.e
  normal_variance_positive : ∀ params : NormalParams,
    0 < normalVarianceClosedForm params

instance : SpecialDistributionStatsStructure where
  linear_expectation := linearExpectedValue
  linear_variance_nonneg := linearVarianceClosedForm_nonneg
  normal_inverse_median := normalInverseBook_median
  normal_variance_positive := normalVarianceClosedForm_pos

theorem linear_expectation_interface [SpecialDistributionStatsStructure]
    (params : LinearParams) :
    uncertainExpectedValue params = (params.a + params.b) / 2 :=
  SpecialDistributionStatsStructure.linear_expectation params

theorem linear_variance_nonneg_interface [SpecialDistributionStatsStructure]
    (params : LinearParams) :
    0 ≤ linearVarianceClosedForm params :=
  SpecialDistributionStatsStructure.linear_variance_nonneg params

theorem normal_inverse_median_interface [SpecialDistributionStatsStructure]
    (params : NormalParams) :
    normalInverseBook params (1 / 2 : ℝ) = params.e :=
  SpecialDistributionStatsStructure.normal_inverse_median params

theorem normal_variance_positive_interface [SpecialDistributionStatsStructure]
    (params : NormalParams) :
    0 < normalVarianceClosedForm params :=
  SpecialDistributionStatsStructure.normal_variance_positive params

/--
An engineering cutoff used to truncate improper integrals over `ℝ`.

In particular, `engineeringCutoff` is used in `expectedValue_via_cdf` to
approximate the mathematically natural improper integral over the whole real
line by integrating only over `[-engineeringCutoff, engineeringCutoff]`.
This is an engineering/approximation choice, not an exact theorem about the
underlying distributions.
-/
def engineeringCutoff : ℝ := Real.exp 20

/-- Formula layer for expectation/variance/moments from distribution-side expressions. -/
class DistributionFormulaStructure (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] [SecondMomentStructure U] where
  expectedValue_via_cdf : ∀ X : UncertainVariable U,
    E U X =
      (∫ x in (0 : ℝ)..engineeringCutoff, (1 - uncertainDistribution U X x)) -
      (∫ x in (-engineeringCutoff : ℝ)..0, uncertainDistribution U X x)
  expectedValue_via_inverse : ∀ (X : UncertainVariable U) (invX : ℝ → ℝ),
    E U X = ∫ α in (0 : ℝ)..1, invX α
  variance_via_inverse : ∀ (X : UncertainVariable U) (invX : ℝ → ℝ),
    Var U X = ∫ α in (0 : ℝ)..1, (invX α - E U X) ^ 2
  odd_moment_formula : ∀ (invX : ℝ → ℝ) (k : ℕ),
    k % 2 = 1 →
      (∫ α in (0 : ℝ)..1, (invX α) ^ k)
        = - (∫ α in (0 : ℝ)..1, (-invX α) ^ k)
  even_moment_formula : ∀ (invX : ℝ → ℝ) (k : ℕ),
    k % 2 = 0 →
      (∫ α in (0 : ℝ)..1, (invX α) ^ k)
        = (∫ α in (0 : ℝ)..1, (-invX α) ^ k)

theorem expectedValue_via_inverse_interface (U : UncertainSpace)
    [AlgebraicUncertainSpace U] [ExpectationStructure U] [SecondMomentStructure U]
    [DistributionFormulaStructure U]
    (X : UncertainVariable U) (invX : ℝ → ℝ) :
    E U X = ∫ α in (0 : ℝ)..1, invX α :=
  DistributionFormulaStructure.expectedValue_via_inverse X invX

theorem variance_via_inverse_interface (U : UncertainSpace)
    [AlgebraicUncertainSpace U] [ExpectationStructure U] [SecondMomentStructure U]
    [DistributionFormulaStructure U]
    (X : UncertainVariable U) (invX : ℝ → ℝ) :
    Var U X = ∫ α in (0 : ℝ)..1, (invX α - E U X) ^ 2 :=
  DistributionFormulaStructure.variance_via_inverse X invX

theorem odd_moment_formula_interface (U : UncertainSpace)
    [AlgebraicUncertainSpace U] [ExpectationStructure U] [SecondMomentStructure U]
    [DistributionFormulaStructure U]
    (invX : ℝ → ℝ) (k : ℕ) (hk : k % 2 = 1) :
    (∫ α in (0 : ℝ)..1, (invX α) ^ k)
      = - (∫ α in (0 : ℝ)..1, (-invX α) ^ k) :=
  DistributionFormulaStructure.odd_moment_formula (U := U) invX k hk

theorem even_moment_formula_interface (U : UncertainSpace)
    [AlgebraicUncertainSpace U] [ExpectationStructure U] [SecondMomentStructure U]
    [DistributionFormulaStructure U]
    (invX : ℝ → ℝ) (k : ℕ) (hk : k % 2 = 0) :
    (∫ α in (0 : ℝ)..1, (invX α) ^ k)
      = (∫ α in (0 : ℝ)..1, (-invX α) ^ k) :=
  DistributionFormulaStructure.even_moment_formula (U := U) invX k hk

/-- Stage 2 helper: interval mass of `(-∞, x] ∩ [a,b]`. -/
noncomputable def intervalMassLE (params : LinearParams) (x : ℝ) : ℝ :=
  max 0 (min (x - params.a) (params.b - params.a))

/-- Stage 2 helper theorem: linear distribution equals normalized interval mass. -/
theorem linearDistribution_eq_intervalMassLE (params : LinearParams) (x : ℝ) :
    linearDistribution params x = intervalMassLE params x / (params.b - params.a) := by
  by_cases hxa : x < params.a
  · have hmin : min (x - params.a) (params.b - params.a) = x - params.a := by
      apply min_eq_left
      linarith [params.h_lt]
    have hmax : max 0 (x - params.a) = 0 := by
      apply max_eq_left
      linarith
    simp [linearDistribution, hxa, intervalMassLE, hmin, hmax]
  · by_cases hxb : x > params.b
    · have hmin : min (x - params.a) (params.b - params.a) = (params.b - params.a) := by
        apply min_eq_right
        linarith
      have hmax : max 0 (params.b - params.a) = (params.b - params.a) := by
        apply max_eq_right
        linarith [params.h_lt]
      have hden : params.b - params.a ≠ 0 := sub_ne_zero.mpr (ne_of_gt params.h_lt)
      simp [linearDistribution, hxa, hxb, intervalMassLE, hmin, hmax, hden]
    · have hmin : min (x - params.a) (params.b - params.a) = x - params.a := by
        apply min_eq_left
        linarith
      have hmax : max 0 (x - params.a) = x - params.a := by
        apply max_eq_right
        linarith
      simp [linearDistribution, hxa, hxb, intervalMassLE, hmin, hmax]

/-- Stage 2: packaged linear variable constructor with distribution/quantile specs. -/
structure CreatedLinearVariable where
  /-- Parameters defining the underlying linear uncertain distribution. -/
  params : LinearParams
  /-- CDF representation of the constructed variable. -/
  cdf : ℝ → ℝ
  /-- Quantile representation on `[0,1]`. -/
  quantile : ∀ α, α ∈ Set.Icc (0 : ℝ) 1 → ℝ
  cdf_spec : cdf = linearDistribution params
  quantile_spec : ∀ α hα, quantile α hα = linearInverse params α

/-- Refactored Stage 2 constructor. -/
noncomputable def createLinearVariable (params : LinearParams) : CreatedLinearVariable where
  params := params
  cdf := linearDistribution params
  quantile := fun α _hα => linearInverse params α
  cdf_spec := rfl
  quantile_spec := by
    intro α hα
    rfl

@[simp] theorem createLinearVariable_cdf (params : LinearParams) :
    (createLinearVariable params).cdf = linearDistribution params := by
  rfl

@[simp] theorem createLinearVariable_quantile (params : LinearParams) (α : ℝ)
  (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    (createLinearVariable params).quantile α hα = linearInverse params α := by
  rfl

/-- Stage 2 check: constructed variable has the target linear distribution. -/
theorem createLinearVariable_has_linear_distribution (params : LinearParams) (x : ℝ) :
    (createLinearVariable params).cdf x = linearDistribution params x := by
  rfl

/-- Stage 2 example parameters. -/
def exampleLinearParams : LinearParams where
  a := 1
  b := 3
  h_lt := by norm_num

/-- Stage 2 example linear constructor instance. -/
noncomputable def exampleLinear : CreatedLinearVariable :=
  createLinearVariable exampleLinearParams

/-- Stage 2 example expectation check. -/
theorem exampleExpectation : uncertainExpectedValue exampleLinearParams = 2 := by
  have h := linearExpectedValue exampleLinearParams
  norm_num [exampleLinearParams] at h ⊢
  exact h

end Uncertainty
