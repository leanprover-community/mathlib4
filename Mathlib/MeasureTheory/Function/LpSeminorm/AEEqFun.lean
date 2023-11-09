import Mathlib.MeasureTheory.Function.AEEqFun
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleIneq
import Mathlib.MeasureTheory.Function.LpSeminorm.MeasureOps

open scoped ENNReal

namespace MeasureTheory

variable {α β E : Type*} {_ : MeasurableSpace α} {_ : MeasurableSpace β} [NormedAddCommGroup E]
  {μ : Measure α} {ν : Measure β} {p : ℝ≥0∞}

namespace AEEqFun

@[simp]
lemma snorm_compMeasurePreserving {f : α → β} (g : β →ₘ[ν] E) (hf : MeasurePreserving f μ ν) :
    snorm (g.compMeasurePreserving f hf) p μ = snorm g p ν := by
  rw [snorm_congr_ae (g.coeFn_compMeasurePreserving _)]
  exact snorm_comp_measurePreserving g.aestronglyMeasurable hf

protected lemma snorm_add_le (f g : α →ₘ[μ] E) : snorm (⇑(f + g)) p μ ≤ snorm f p μ + snorm g p μ :=
  (snorm_congr_ae <| coeFn_add f g).trans_le
    (snorm_add_le f.aestronglyMeasurable g.aestronglyMeasurable)
