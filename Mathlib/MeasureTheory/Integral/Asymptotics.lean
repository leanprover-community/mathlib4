/-
Copyright (c) 2024 Lawrence Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lawrence Wu
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Normed.Field.Basic

/-!
# Bounding of integrals by asymptotics

We establish integrability of `f` from `f = O(g)`.

## Main results

* `integrable_Ioi_of_isBigO_integrable_Ioi`: If `f` is continuous on `[a, ∞)`, for some `a ∈ ℝ`,
  `g` is integrable on `(b, ∞)` for some `b ∈ ℝ`, and `f(x) = O(g(x))`, then
  `f` is integrable on `(a, ∞)`.
* `integrable_of_isBigO_integrable`: If `f` is continuous, `‖f(x)‖ = ‖f(-x)‖`,
  `g` is integrable on `(b, ∞)` for some `b ∈ ℝ`, and `f(x) = O(g(x))`, then
  `f` is integrable.
-/

noncomputable section

open Asymptotics MeasureTheory Set Filter

variable {α E : Type*} [MeasurableSpace α] {f g : α → E} {a b : α} {μ : Measure α} {l : Filter α}

theorem __root__.Asymptotics.IsBigO.integrableAtFilter [NormedDivisionRing E] [NormedSpace ℝ E]
    (hf : f =O[l] g) (hmeas : ∃ s ∈ l, AEStronglyMeasurable f (μ.restrict s))
    (hg : IntegrableAtFilter g l μ) : IntegrableAtFilter f l μ := by
  obtain ⟨C, hC⟩ := hf.bound
  obtain ⟨C', hC'⟩ := exists_norm_eq E <| le_max_right C 0
  obtain ⟨s, hsl, hs⟩ := hC.exists_mem
  obtain ⟨t, htl, ht⟩ := hg
  obtain ⟨u, hul, hu⟩ := hmeas
  let S := s ∩ t ∩ u
  use S, inter_mem (inter_mem hsl htl) hul
  use hu.mono_measure <| Measure.restrict_mono (inter_subset_right _ u) le_rfl
  have : S ⊆ t := fun _ h ↦ inter_subset_right s t <| inter_subset_left (s ∩ t) u h
  apply ht.mono_set this |>.const_mul C' |>.2.mono
  refine (ae_restrict_iff ?_).mpr ?_
  · sorry -- ⊢ MeasurableSet {x | ‖f x‖ ≤ ‖C' * g x‖}
  · refine (ae_of_all _ fun x hx => (hs x hx.1.1).trans ?_)
    rewrite [norm_mul, hC']
    gcongr
    apply le_max_left

variable [NormedAddCommGroup E] [TopologicalSpace α]

theorem integrable_iff_integrableAtFilter_cocompact :
    (IntegrableAtFilter f (cocompact α) μ ∧ LocallyIntegrable f μ) ↔ Integrable f μ := by
  refine ⟨fun ⟨⟨s, hsc, hs⟩, h0⟩ ↦ ?_, fun hf ↦ ⟨hf.integrableAtFilter _, hf.locallyIntegrable⟩⟩
  obtain ⟨t, htc, ht⟩ := mem_cocompact'.mp hsc
  rewrite [← integrableOn_univ, ← compl_union_self s, integrableOn_union]
  exact ⟨(h0.integrableOn_isCompact htc).mono ht le_rfl, hs⟩

end
