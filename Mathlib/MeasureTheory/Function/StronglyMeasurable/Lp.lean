/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne

! This file was ported from Lean 3 source module measure_theory.function.strongly_measurable.lp
! leanprover-community/mathlib commit f2ce6086713c78a7f880485f7917ea547a215982
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Function.SimpleFuncDenseLp
import Mathbin.MeasureTheory.Function.StronglyMeasurable.Basic

/-!
# Finitely strongly measurable functions in `Lp`

Functions in `Lp` for `0 < p < ∞` are finitely strongly measurable.

## Main statements

* `mem_ℒp.ae_fin_strongly_measurable`: if `mem_ℒp f p μ` with `0 < p < ∞`, then
  `ae_fin_strongly_measurable f μ`.
* `Lp.fin_strongly_measurable`: for `0 < p < ∞`, `Lp` functions are finitely strongly measurable.

## References

* Hytönen, Tuomas, Jan Van Neerven, Mark Veraar, and Lutz Weis. Analysis in Banach spaces.
Springer, 2016.
-/


open MeasureTheory Filter TopologicalSpace Function

open scoped ENNReal Topology MeasureTheory

namespace MeasureTheory

-- mathport name: «expr →ₛ »
local infixr:25 " →ₛ " => SimpleFunc

variable {α G : Type _} {p : ℝ≥0∞} {m m0 : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup G]
  {f : α → G}

theorem Memℒp.finStronglyMeasurable_of_stronglyMeasurable (hf : Memℒp f p μ)
    (hf_meas : StronglyMeasurable f) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    FinStronglyMeasurable f μ := by
  borelize G
  haveI : separable_space (Set.range f ∪ {0} : Set G) :=
    hf_meas.separable_space_range_union_singleton
  let fs := simple_func.approx_on f hf_meas.measurable (Set.range f ∪ {0}) 0 (by simp)
  refine' ⟨fs, _, _⟩
  · have h_fs_Lp : ∀ n, mem_ℒp (fs n) p μ :=
      simple_func.mem_ℒp_approx_on_range hf_meas.measurable hf
    exact fun n => (fs n).measure_support_lt_top_of_memℒp (h_fs_Lp n) hp_ne_zero hp_ne_top
  · intro x
    apply simple_func.tendsto_approx_on
    apply subset_closure
    simp
#align measure_theory.mem_ℒp.fin_strongly_measurable_of_strongly_measurable MeasureTheory.Memℒp.finStronglyMeasurable_of_stronglyMeasurable

theorem Memℒp.aEFinStronglyMeasurable (hf : Memℒp f p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    AEFinStronglyMeasurable f μ :=
  ⟨hf.AEStronglyMeasurable.mk f,
    ((memℒp_congr_ae hf.AEStronglyMeasurable.ae_eq_mk).mp
          hf).finStronglyMeasurable_of_stronglyMeasurable
      hf.AEStronglyMeasurable.stronglyMeasurable_mk hp_ne_zero hp_ne_top,
    hf.AEStronglyMeasurable.ae_eq_mk⟩
#align measure_theory.mem_ℒp.ae_fin_strongly_measurable MeasureTheory.Memℒp.aEFinStronglyMeasurable

theorem Integrable.aEFinStronglyMeasurable (hf : Integrable f μ) : AEFinStronglyMeasurable f μ :=
  (memℒp_one_iff_integrable.mpr hf).AEFinStronglyMeasurable one_ne_zero ENNReal.coe_ne_top
#align measure_theory.integrable.ae_fin_strongly_measurable MeasureTheory.Integrable.aEFinStronglyMeasurable

theorem Lp.finStronglyMeasurable (f : Lp G p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    FinStronglyMeasurable f μ :=
  (Lp.memℒp f).finStronglyMeasurable_of_stronglyMeasurable (Lp.stronglyMeasurable f) hp_ne_zero
    hp_ne_top
#align measure_theory.Lp.fin_strongly_measurable MeasureTheory.Lp.finStronglyMeasurable

end MeasureTheory

