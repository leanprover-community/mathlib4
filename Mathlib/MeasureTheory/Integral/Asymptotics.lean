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

* `Asymptotics.IsBigO.integrableAtFilter`: Given measurable functions `f`, `g` with `f = O[l] g`,
  `IntegrableAtFilter g l μ` implies `IntegrableAtFilter f l μ`.
-/

open Asymptotics MeasureTheory Set Filter

variable {α E : Type*} [MeasurableSpace α] [NormedDivisionRing E] [NormedSpace ℝ E]
 {f g : α → E} {a b : α} {μ : Measure α} {l : Filter α}

private theorem _root_.Asymptotics.IsBigO.integrableAtFilter_aux
    (hfm : AEStronglyMeasurable f μ)
    (hae_restrict_iff : ∀ C' : E, ∀ s ∈ l, ∀ t ∈ l,
      (∀ᵐ (x : α) ∂μ.restrict (s ∩ t), ‖f x‖ ≤ ‖C' * g x‖) ↔
      ∀ᵐ (x : α) ∂μ, x ∈ (s ∩ t) → ‖f x‖ ≤ ‖C' * g x‖)
    (hf : f =O[l] g) (hg : IntegrableAtFilter g l μ) : IntegrableAtFilter f l μ := by
  obtain ⟨C, hC⟩ := hf.bound
  obtain ⟨C', hC'⟩ := exists_norm_eq E <| le_max_right C 0
  obtain ⟨s, hsl, hs⟩ := hC.exists_mem
  obtain ⟨t, htl, ht⟩ := hg
  use s ∩ t, inter_mem hsl htl, hfm.restrict
  refine ht.mono_set (inter_subset_right s t) |>.const_mul C' |>.2.mono
    <| (hae_restrict_iff C' s hsl t htl).mpr <| ae_of_all _ fun x hx => (hs x hx.1).trans ?_
  rewrite [norm_mul, hC']
  gcongr
  apply le_max_left

/-- `Asymptotics.IsBigO.integrableAtFilter` with measurability hypothesis on `l` instead of `g`. -/
theorem _root_.Asymptotics.IsBigO.integrableAtFilter'
    (hfm : AEStronglyMeasurable f μ) (hgm : ∀ s ∈ l, MeasurableSet s)
    (hf : f =O[l] g) (hg : IntegrableAtFilter g l μ) : IntegrableAtFilter f l μ := by
  refine hf.integrableAtFilter_aux hfm (fun _ s hs t ht ↦ ?_) hg
  exact ae_restrict_iff' <| (hgm s hs).inter (hgm t ht)

variable [MeasurableSpace E] [OpensMeasurableSpace E] [SecondCountableTopology E]

/-- Given measurable functions `f`, `g` with `f = O[l] g`,
`IntegrableAtFilter g l μ` implies `IntegrableAtFilter f l μ`. -/
theorem _root_.Asymptotics.IsBigO.integrableAtFilter (hfm : Measurable f) (hgm : Measurable g)
    (hf : f =O[l] g) (hg : IntegrableAtFilter g l μ) : IntegrableAtFilter f l μ := by
  refine hf.integrableAtFilter_aux hfm.aestronglyMeasurable (fun C' _ _ _ _ ↦ ?_) hg
  refine ae_restrict_iff (measurableSet_le hfm.norm ?_)
  convert hgm.norm.const_mul ‖C'‖
  exact norm_mul C' _
