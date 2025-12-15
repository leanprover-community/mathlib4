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

theorem measurable_condLExp (mΩ : MeasurableSpace Ω) (P : Measure[mΩ₀] Ω) (X : Ω → ℝ≥0∞) :
    Measurable[mΩ] P⁻[X|mΩ] := by
  by_cases hm : mΩ ≤ mΩ₀
  · by_cases h : SigmaFinite (P.trim hm) <;> simpa [condLExp, hm, h] using (by fun_prop)
  · simpa [condLExp, hm] using (by fun_prop)

theorem lintegral_condLExp {mΩ : MeasurableSpace Ω} (hm : mΩ ≤ mΩ₀) (P : Measure[mΩ₀] Ω)
     [hσ : SigmaFinite (P.trim hm)] (X : Ω → ℝ≥0∞) (s : Set Ω) (hs : MeasurableSet[mΩ] s) :
    ∫⁻ ω in s, P⁻[X|mΩ] ω ∂P = ∫⁻ ω in s, X ω ∂P := by
  have h := AbsolutelyContinuous.trim (withDensity_absolutelyContinuous P X) hm
  have : SFinite ((P.withDensity X).trim hm) := sFinite_of_absolutelyContinuous h
  simp only [condLExp, hm, hσ, ↓reduceDIte,]
  rw [ ← lintegral_indicator (hm s hs), ← lintegral_trim hm (by measurability),
    lintegral_indicator hs, setLIntegral_rnDeriv' h hs, trim_measurableSet_eq hm hs,
    withDensity_apply _ (hm s hs)]

end MeasureTheory
