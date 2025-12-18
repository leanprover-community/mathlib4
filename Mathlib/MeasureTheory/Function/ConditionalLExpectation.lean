import Mathlib

open MeasureTheory ProbabilityTheory Measure

open scoped ENNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ₀ mΩ : MeasurableSpace Ω} {P : Measure[mΩ₀] Ω} {X : Ω → ℝ≥0∞}

open Classical in
noncomputable irreducible_def condLExp (mΩ : MeasurableSpace Ω) (P : Measure[mΩ₀] Ω)
    (X : Ω → ℝ≥0∞) : Ω → ℝ≥0∞ :=
  if hm : mΩ ≤ mΩ₀ then
    if _ : SigmaFinite (P.trim hm) then
      if _ : Measurable[mΩ] X then X else
      ∂((P.withDensity X).trim hm)/∂(P.trim hm)
    else 0
  else 0

@[inherit_doc MeasureTheory.condLExp]
scoped macro:max μ:term noWs "⁻[" f:term "|" m:term "]" : term =>
  `(MeasureTheory.condLExp $m $μ $f)

/-- Unexpander for `μ⁻[f|m]` notation. -/
@[app_unexpander MeasureTheory.condLExp]
meta def condLExpUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $m $μ $f) => `($μ⁻[$f|$m])
  | _ => throw ()

/-- info: P⁻[X|mΩ] : Ω → ℝ≥0∞ -/
#guard_msgs in
#check P⁻[X|mΩ]
/-- info: P⁻[X|mΩ] sorry : ℝ≥0∞ -/
#guard_msgs in
#check P⁻[X|mΩ] (sorry : Ω)

theorem condLExp_of_not_le (hm_not : ¬mΩ ≤ mΩ₀) : P⁻[X|mΩ] = 0 := by
    rw [condLExp, dif_neg hm_not]

theorem condLExp_of_not_sigmaFinite (hm : mΩ ≤ mΩ₀) (hμm_not : ¬SigmaFinite (P.trim hm)) :
    P⁻[X|mΩ] = 0 := by rwa [condLExp, dif_pos hm, dif_neg]

theorem condLExp_eq_self (hm : mΩ ≤ mΩ₀) (P : Measure[mΩ₀] Ω) [hσ : SigmaFinite (P.trim hm)]
    {X : Ω → ℝ≥0∞} (hX : Measurable[mΩ] X) : P⁻[X|mΩ] = X := by
  simp [condLExp, hm, hσ, hX]

theorem condLExp_of_not_sub_sigma_measurable (hm : mΩ ≤ mΩ₀) (P : Measure[mΩ₀] Ω)
    [hσ : SigmaFinite (P.trim hm)] {X : Ω → ℝ≥0∞} (hX : ¬Measurable[mΩ] X) :
    P⁻[X|mΩ] = ∂((P.withDensity X).trim hm)/∂(P.trim hm) := by
  simp [condLExp, hm, hσ, hX]

theorem measurable_condLExp (mΩ : MeasurableSpace Ω) (P : Measure[mΩ₀] Ω) (X : Ω → ℝ≥0∞) :
    Measurable[mΩ] P⁻[X|mΩ] := by
  by_cases hm : mΩ ≤ mΩ₀
  · by_cases hσ : SigmaFinite (P.trim hm)
    · by_cases hX : Measurable[mΩ] X
      · simp [condLExp_eq_self hm, hX]
      simp [condLExp_of_not_sub_sigma_measurable hm _ hX, measurable_rnDeriv]
    simp [condLExp_of_not_sigmaFinite hm hσ, measurable_zero]
  simp [condLExp_of_not_le hm, measurable_zero]

variable (hm : mΩ ≤ mΩ₀)

theorem setLIntegral_condLExp (P : Measure[mΩ₀] Ω) [hσ : SigmaFinite (P.trim hm)]
    (X : Ω → ℝ≥0∞) {s : Set Ω} (hs : MeasurableSet[mΩ] s) :
    ∫⁻ ω in s, P⁻[X|mΩ] ω ∂P = ∫⁻ ω in s, X ω ∂P := by
  by_cases hX : Measurable[mΩ] X
  · simp [condLExp_eq_self hm _ hX]
  have h := AbsolutelyContinuous.trim (withDensity_absolutelyContinuous P X) hm
  have : SFinite ((P.withDensity X).trim hm) := sFinite_of_absolutelyContinuous h
  rw [condLExp_of_not_sub_sigma_measurable hm _ hX, ← lintegral_indicator (hm s hs),
    ← lintegral_trim hm (by measurability), lintegral_indicator hs, setLIntegral_rnDeriv' h hs,
    trim_measurableSet_eq hm hs, withDensity_apply _ (hm s hs)]

theorem lintegral_condLExp (P : Measure[mΩ₀] Ω) [hσ : SigmaFinite (P.trim hm)] (X : Ω → ℝ≥0∞) :
    ∫⁻ ω, P⁻[X|mΩ] ω ∂P = ∫⁻ ω, X ω ∂P := by
  simpa [← setLIntegral_univ] using setLIntegral_condLExp _ _ _ .univ

theorem eq_condLExp_ae (P : Measure[mΩ₀] Ω) [hσ : SigmaFinite (P.trim hm)]
    (X : Ω → ℝ≥0∞) {Y : Ω → ℝ≥0∞} (hY : Measurable[mΩ] Y)
    (hXY : ∀ s, MeasurableSet[mΩ] s → ∫⁻ ω in s, P⁻[X|mΩ] ω ∂P = ∫⁻ ω in s, Y ω ∂P) :
    Y =ᵐ[P] P⁻[X|mΩ] := by
  --change P {ω | Y ω ≠ P⁻[X|mΩ] ω} = 0
  have h₁ : MeasurableSet[mΩ] {ω | Y ω > P⁻[X|mΩ] ω} := by sorry
  have h₂ : MeasurableSet[mΩ] {ω | Y ω < P⁻[X|mΩ] ω} := by sorry
  --have h₃ := lintegral_condLExp hm P X h₁
  --have h₄ := lintegral_condLExp hm P X h₂
  sorry

theorem condLExp_const (P : Measure[mΩ₀] Ω) [hσ : SigmaFinite (P.trim hm)] (c : ℝ≥0∞) :
    P⁻[fun _ : Ω ↦ c|mΩ] = fun _ ↦ c := condLExp_eq_self _ _ (measurable_const)

@[gcongr]
theorem condLExp_congr_ae (P : Measure[mΩ₀] Ω)
    {X Y : Ω → ℝ≥0∞} (hXY : X =ᵐ[P] Y) : P⁻[X|mΩ] =ᵐ[P] P⁻[Y|mΩ] := by
  by_cases hm : mΩ ≤ mΩ₀
  · by_cases hσ : SigmaFinite (P.trim hm)
    · refine eq_condLExp_ae _ _ _ (measurable_condLExp _ _ _) (fun s hs ↦ ?_)
      repeat rw [setLIntegral_condLExp _ _ _ hs]
      apply setLIntegral_congr_fun_ae (hm s hs)
      filter_upwards [hXY] using (fun _ h _ ↦ h.symm)
    simp [condLExp_of_not_sigmaFinite hm hσ]
  simp [condLExp_of_not_le hm]

@[gcongr]
theorem condLExp_congr_ae_trim (P : Measure[mΩ₀] Ω)
    {X Y : Ω → ℝ≥0∞} (hXY : X =ᵐ[P] Y) : P⁻[X|mΩ] =ᵐ[P.trim hm] P⁻[Y|mΩ] := by
  apply ae_eq_trim_of_measurable hm (measurable_condLExp _ _ X) (measurable_condLExp _ _ Y)
  exact condLExp_congr_ae P hXY

-- we need `measurable_bot_iff`
#check MeasurableSpace.SeparatesPoints
-- similar proof should work where we rule out the not `FiniteMeasure` case
theorem condLExp_bot' (X : Ω → ℝ≥0∞) :
    P⁻[X|⊥] = fun _ => (P .univ)⁻¹ • ∫⁻ ω, X ω ∂P := by sorry

theorem condLExp_bot [IsProbabilityMeasure P] (X : Ω → ℝ≥0∞) :
    P⁻[X|⊥] = fun _ => ∫⁻ ω, X ω ∂P := by sorry

-- condLExp_mono (test)

-- condLExp_add

-- condLExp_finset_sum

-- condLExp_smul

-- Add docs

-- Good for first PR?

end MeasureTheory
