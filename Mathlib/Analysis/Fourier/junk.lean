import Mathlib

open MeasureTheory

example (E : Type*) (F : Type*) [inst : NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [inst_6 : NormedSpace ℂ F] [inst_7 : CompleteSpace F] {f : E → F}
  (hf_AE : AEStronglyMeasurable f volume) :
  AEStronglyMeasurable
    (fun w ↦ ContinuousLinearMap.comp (ContinuousLinearMap.toSpanSingleton ℝ (f w)) ((innerSL ℝ) w)) volume := sorry
