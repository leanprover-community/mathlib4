/-
Copyright (c) 2024 Lawrence Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lawrence Wu
-/
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Bounding of integrals by asymptotics

We establish integrability of `f` from `f = O(g)`.

## Main results

* `Asymptotics.IsBigO.integrableAtFilter`: Given `f = O[l] g` on measurably generated `l`,
  `IntegrableAtFilter g l μ`, and `f` `AEStronglyMeasurable` at `l`, `IntegrableAtFilter f l μ`.
-/

open Asymptotics MeasureTheory Set Filter

variable {α E F : Type*} [MeasurableSpace α] [NormedDivisionRing E] [NormedSpace ℝ E]
  [NormedDivisionRing F] [NormedSpace ℝ F] {f : α → E} {g : α → F} {a b : α} {μ : Measure α}
  {l : Filter α}

/-- Given `f = O[l] g` on measurably generated `l`,
`IntegrableAtFilter g l μ`, and `f` `AEStronglyMeasurable` at `l`, `IntegrableAtFilter f l μ`. -/
theorem _root_.Asymptotics.IsBigO.integrableAtFilter [IsMeasurablyGenerated l]
    (hfm : ∃ s ∈ l, AEStronglyMeasurable f (μ.restrict s))
    (hf : f =O[l] g) (hg : IntegrableAtFilter g l μ) : IntegrableAtFilter f l μ := by
  obtain ⟨C, hC⟩ := hf.bound
  obtain ⟨C', hC'⟩ := exists_norm_eq F <| le_max_right C 0
  obtain ⟨s, hsl, hs⟩ := hC.exists_mem
  obtain ⟨t, htl, ht⟩ := hg
  obtain ⟨u, hul, hu⟩ := hfm
  obtain ⟨S, hS, hs_meas, hs_le⟩ :=
    IsMeasurablyGenerated.exists_measurable_subset <| inter_mem (inter_mem hsl htl) hul
  use S, hS, hu.mono_measure <| Measure.restrict_mono (fun _ hx ↦ (hs_le hx).2) le_rfl
  refine ht.mono_set (fun _ hx ↦ (hs_le hx).1.2) |>.const_mul C' |>.2.mono ?_
  refine (ae_restrict_iff' hs_meas).mpr <| ae_of_all _ fun x hx => (hs x (hs_le hx).1.1).trans ?_
  rewrite [norm_mul, hC']
  gcongr
  apply le_max_left

/-- Variant of `MeasureTheory.Integrable.mono` taking `f =O[⊤] (g)` instead of `‖f(x)‖ ≤ ‖g(x)‖` -/
theorem _root_.Asymptotics.IsBigO.integrable (hfm : AEStronglyMeasurable f μ)
    (hf : f =O[⊤] g) (hg : Integrable g μ) : Integrable f μ := by
  rewrite [← IntegrableAtFilter.top] at *
  exact hf.integrableAtFilter ⟨univ, univ_mem, hfm.restrict⟩ hg
