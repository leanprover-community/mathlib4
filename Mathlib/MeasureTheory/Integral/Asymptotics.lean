/-
Copyright (c) 2024 Lawrence Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lawrence Wu
-/
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Bounding of integrals by asymptotics

We establish integrability of `f` from `f = O(g)`.
-/

noncomputable section

open Asymptotics MeasureTheory Set Filter

variable {α E : Type*} [MeasurableSpace α] {f g : α → E} {a b : α} {μ : Measure α} {l : Filter α}

theorem __root__.Asymptotics.IsBigO.integrableAtFilter [NormedDivisionRing E] [NormedSpace ℝ E]
    [MeasurableSpace E] [OpensMeasurableSpace E] [SecondCountableTopology E]
    (hfm : Measurable f) (hgm : Measurable g) (hf : f =O[l] g) (hg : IntegrableAtFilter g l μ) :
    IntegrableAtFilter f l μ := by
  obtain ⟨C, hC⟩ := hf.bound
  obtain ⟨C', hC'⟩ := exists_norm_eq E <| le_max_right C 0
  obtain ⟨s, hsl, hs⟩ := hC.exists_mem
  obtain ⟨t, htl, ht⟩ := hg
  use s ∩ t, inter_mem hsl htl, hfm.aestronglyMeasurable.restrict
  refine ht.mono_set (inter_subset_right s t) |>.const_mul C' |>.2.mono
    <| (ae_restrict_iff (measurableSet_le hfm.norm ?_)).mpr ?_
  · convert hgm.norm.const_mul ‖C'‖
    exact norm_mul C' _
  · refine (ae_of_all _ fun x hx => (hs x hx.1).trans ?_)
    rewrite [norm_mul, hC']
    gcongr
    apply le_max_left

end
