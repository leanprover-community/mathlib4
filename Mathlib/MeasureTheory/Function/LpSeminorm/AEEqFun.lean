
theorem AEEqFun.snorm_compMeasurePreserving {ν : MeasureTheory.Measure β} (g : β →ₘ[ν] E)
    (hf : MeasurePreserving f μ ν) :
    snorm (g.compMeasurePreserving f hf) p μ = snorm g p ν := by
  rw [snorm_congr_ae (g.coeFn_compMeasurePreserving _)]
  exact snorm_comp_measurePreserving g.aestronglyMeasurable hf
