/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

/-!
# Finitely strongly measurable functions in `Lp`

Functions in `Lp` for `0 < p < ∞` are finitely strongly measurable.

## Main statements

* `MemLp.aefinStronglyMeasurable`: if `MemLp f p μ` with `0 < p < ∞`, then
  `AEFinStronglyMeasurable f μ`.
* `Lp.finStronglyMeasurable`: for `0 < p < ∞`, `Lp` functions are finitely strongly measurable.

## References

* [Hytönen, Tuomas, Jan Van Neerven, Mark Veraar, and Lutz Weis. Analysis in Banach spaces.
  Springer, 2016.][Hytonen_VanNeerven_Veraar_Wies_2016]

-/


open MeasureTheory Filter TopologicalSpace Function

open scoped ENNReal Topology MeasureTheory

namespace MeasureTheory

local infixr:25 " →ₛ " => SimpleFunc

variable {α G : Type*} {p : ℝ≥0∞} {m m0 : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup G]
  {f : α → G}

theorem MemLp.finStronglyMeasurable_of_stronglyMeasurable (hf : MemLp f p μ)
    (hf_meas : StronglyMeasurable f) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    FinStronglyMeasurable f μ := by
  borelize G
  haveI : SeparableSpace (Set.range f ∪ {0} : Set G) :=
    hf_meas.separableSpace_range_union_singleton
  let fs := SimpleFunc.approxOn f hf_meas.measurable (Set.range f ∪ {0}) 0 (by simp)
  refine ⟨fs, ?_, ?_⟩
  · have h_fs_Lp : ∀ n, MemLp (fs n) p μ :=
      SimpleFunc.memLp_approxOn_range hf_meas.measurable hf
    exact fun n => (fs n).measure_support_lt_top_of_memLp (h_fs_Lp n) hp_ne_zero hp_ne_top
  · intro x
    apply SimpleFunc.tendsto_approxOn
    apply subset_closure
    simp

theorem MemLp.aefinStronglyMeasurable (hf : MemLp f p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    AEFinStronglyMeasurable f μ :=
  ⟨hf.aestronglyMeasurable.mk f,
    ((memLp_congr_ae hf.aestronglyMeasurable.ae_eq_mk).mp
          hf).finStronglyMeasurable_of_stronglyMeasurable
      hf.aestronglyMeasurable.stronglyMeasurable_mk hp_ne_zero hp_ne_top,
    hf.aestronglyMeasurable.ae_eq_mk⟩

theorem Integrable.aefinStronglyMeasurable (hf : Integrable f μ) : AEFinStronglyMeasurable f μ :=
  (memLp_one_iff_integrable.mpr hf).aefinStronglyMeasurable one_ne_zero ENNReal.coe_ne_top

theorem Lp.finStronglyMeasurable (f : Lp G p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    FinStronglyMeasurable f μ :=
  (Lp.memLp f).finStronglyMeasurable_of_stronglyMeasurable (Lp.stronglyMeasurable f) hp_ne_zero
    hp_ne_top

end MeasureTheory
