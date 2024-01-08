import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.L1Space

open MeasureTheory

example (E : Type*) (F : Type*) [inst : NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [inst_6 : NormedSpace ℂ F] [inst_7 : CompleteSpace F] {f : E → F}
  (hf_AE : AEStronglyMeasurable f volume) :
  AEStronglyMeasurable
    (fun w ↦ ContinuousLinearMap.comp (ContinuousLinearMap.toSpanSingleton ℝ (f w))
    ((innerSL ℝ) w)) volume := by
  sorry
