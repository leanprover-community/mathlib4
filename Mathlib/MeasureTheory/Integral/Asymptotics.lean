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

noncomputable section

open Asymptotics MeasureTheory Set Filter

variable {E : Type*} [NormedDivisionRing E] [NormedSpace ℝ E] [Nontrivial E] {f g : ℝ → E} {a b : ℝ}
  {μ : Measure ℝ} [IsLocallyFiniteMeasure μ]

/-- If `f` is continuous on `[a, ∞)`, for some `a ∈ ℝ`,
`g` is integrable on `(b, ∞)` for some `b ∈ ℝ`, and `f(x) = O(g(x))`, then
`f` is integrable on `(a, ∞)`. -/
theorem integrable_Ioi_of_isBigO_integrable_Ioi (hf : ContinuousOn f (Ici a))
    (hg : IntegrableOn g (Ioi b) μ) (ho : f =O[atTop] g) : IntegrableOn f (Ioi a) μ := by
  obtain ⟨C, hC⟩ := ho.bound
  obtain ⟨C', hC'⟩ := exists_norm_eq E <| le_max_right C 0
  rewrite [eventually_atTop] at hC
  obtain ⟨x', hx'⟩ := hC
  let x := max a (max b x')
  obtain ⟨h_ax, h_bx, h_x'x⟩ := show a ≤ x ∧ b ≤ x ∧ x' ≤ x by simp
  rewrite [← Ioc_union_Ioi_eq_Ioi h_ax]
  refine integrableOn_union.mpr ⟨?_, ?_, ?_⟩
  -- show integrable on `(a, x]` from continuity
  · exact intervalIntegrable_iff_integrableOn_Ioc_of_le h_ax |>.mp
      <| (hf.mono Icc_subset_Ici_self).intervalIntegrable_of_Icc h_ax
  -- now show integrable on `(x, ∞)` from asymptotic
  · exact (hf.mono <| Ioi_subset_Ici <| h_ax).aestronglyMeasurable measurableSet_Ioi
  · refine hg.mono (Ioi_subset_Ioi h_bx) le_rfl |>.2.const_mul C' |>.mono
      <| (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x'' hx'' => ?_)
    apply hx' x'' (h_x'x.trans_lt hx'').le |>.trans
    rewrite [norm_mul, hC']
    gcongr
    apply le_max_left

/-- If `f` is continuous on `(∞, a]`, for some `a ∈ ℝ`,
`g` is integrable on `(b, ∞)` for some `b ∈ ℝ`, and `f(-x) = O(g(x))`, then
`f` is integrable on `(∞, a]`. -/
theorem integrable_Iic_of_isBigO_integrable_Iic (hf : ContinuousOn f (Iic a))
    (hg : IntegrableOn g (Ioi b) μ) (ho : (f ∘ Neg.neg) =O[atTop] g) :
    IntegrableOn f (Iic a) μ := by
  obtain ⟨C, hC⟩ := ho.bound
  obtain ⟨C', hC'⟩ := exists_norm_eq E <| le_max_right C 0
  rewrite [eventually_atTop] at hC
  obtain ⟨x', hx'⟩ := hC
  let x := min a (min (-b) (-x'))
  obtain ⟨h_ax, h_bx, h_x'x⟩ := show a ≥ x ∧ (-b) ≥ x ∧ (-x') ≥ x by simp
  rewrite [← Iic_union_Ioc_eq_Iic h_ax]
  refine integrableOn_union.mpr ⟨⟨?_, ?_⟩, ?_⟩
  -- show integrable on `(x, ∞)` from asymptotic
  · exact (hf.mono <| Iic_subset_Iic.mpr <| h_ax).aestronglyMeasurable measurableSet_Iic
  · stop
    refine hg.mono (Ioi_subset_Ioi h_bx) le_rfl |>.2.const_mul C' |>.mono
      <| (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x'' hx'' => ?_)
    apply hx' x'' (h_x'x.trans_lt hx'').le |>.trans
    rewrite [norm_mul, hC']
    gcongr
    apply le_max_left
  -- now show integrable on `(a, x]` from continuity
  · exact intervalIntegrable_iff_integrableOn_Ioc_of_le h_ax |>.mp
      <| (hf.mono Icc_subset_Iic_self).intervalIntegrable_of_Icc h_ax

/-- If `f` is continuous, `‖f(x)‖ = ‖f(-x)‖`, `g` is integrable on `(b, ∞)` for some `b ∈ ℝ`,
and `f(x) = O(g(x))`, then `f` is integrable. -/
theorem integrable_of_isBigO_integrable (hf : Continuous f) (hsymm : ∀ x, ‖f x‖ = ‖f (-x)‖)
   (hg : IntegrableOn g (Ioi b) μ) (ho : f =O[atTop] g) : Integrable f μ := by
  rewrite [← integrableOn_univ, ← Iic_union_Ioi (a := 0), integrableOn_union]
  refine ⟨?_, integrable_Ioi_of_isBigO_integrable_Ioi hf.continuousOn hg ho⟩
  refine integrable_Iic_of_isBigO_integrable_Iic hf.continuousOn hg ?_
  rw [isBigO_iff] at *
  simpa only [fun x ↦ show ‖(f ∘ Neg.neg) x‖ = ‖f x‖ from (hsymm x).symm] using ho

end
