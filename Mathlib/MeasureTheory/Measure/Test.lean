import Mathlib.MeasureTheory.Measure.Prod

open ENNReal MeasureTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {f : α → ℝ≥0∞} {g : β → ℝ≥0∞}

-- Works!
example (hf : Measurable f) (hg : Measurable g) : Measurable (fun (x,y) ↦ f x * g y) := by
  fun_prop

variable {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]

-- My use case doesn't work!
example (hf : AEMeasurable f μ) (hg : AEMeasurable g ν) :
    AEMeasurable (fun (x,y) ↦ f x * g y) (μ.prod ν) := by
  fun_prop (disch:= intro _ _; simp)

-- Intermediate case doesn't Work!
example (hf : AEMeasurable f μ) (hg : AEMeasurable g ν) :
    AEMeasurable (fun (x,y) ↦ (f x, g y)) (μ.prod ν) := by
  fun_prop (disch:= intro _ _; simp)
