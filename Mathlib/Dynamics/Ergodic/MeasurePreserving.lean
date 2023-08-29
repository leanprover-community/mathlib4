/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.MeasureTheory.Measure.AEMeasurable

#align_import dynamics.ergodic.measure_preserving from "leanprover-community/mathlib"@"92ca63f0fb391a9ca5f22d2409a6080e786d99f7"

/-!
# Measure preserving maps

We say that `f : α → β` is a measure preserving map w.r.t. measures `μ : Measure α` and
`ν : Measure β` if `f` is measurable and `map f μ = ν`. In this file we define the predicate
`MeasureTheory.MeasurePreserving` and prove its basic properties.

We use the term "measure preserving" because in many applications `α = β` and `μ = ν`.

## References

Partially based on
[this](https://www.isa-afp.org/browser_info/current/AFP/Ergodic_Theory/Measure_Preserving_Transformations.html)
Isabelle formalization.

## Tags

measure preserving map, measure
-/


variable {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSpace δ]

namespace MeasureTheory

open Measure Function Set

variable {μa : Measure α} {μb : Measure β} {μc : Measure γ} {μd : Measure δ}

/-- `f` is a measure preserving map w.r.t. measures `μa` and `μb` if `f` is measurable
and `map f μa = μb`. -/
structure MeasurePreserving (f : α → β)
  (μa : Measure α := by volume_tac) (μb : Measure β := by volume_tac) : Prop where
  protected measurable : Measurable f
  protected map_eq : map f μa = μb
#align measure_theory.measure_preserving MeasureTheory.MeasurePreserving
#align measure_theory.measure_preserving.measurable MeasureTheory.MeasurePreserving.measurable
#align measure_theory.measure_preserving.map_eq MeasureTheory.MeasurePreserving.map_eq

protected theorem _root_.Measurable.measurePreserving
    {f : α → β} (h : Measurable f) (μa : Measure α) : MeasurePreserving f μa (map f μa) :=
  ⟨h, rfl⟩
#align measurable.measure_preserving Measurable.measurePreserving

namespace MeasurePreserving

protected theorem id (μ : Measure α) : MeasurePreserving id μ μ :=
  ⟨measurable_id, map_id⟩
#align measure_theory.measure_preserving.id MeasureTheory.MeasurePreserving.id

protected theorem aemeasurable {f : α → β} (hf : MeasurePreserving f μa μb) : AEMeasurable f μa :=
  hf.1.aemeasurable
#align measure_theory.measure_preserving.ae_measurable MeasureTheory.MeasurePreserving.aemeasurable

theorem symm (e : α ≃ᵐ β) {μa : Measure α} {μb : Measure β} (h : MeasurePreserving e μa μb) :
    MeasurePreserving e.symm μb μa :=
  ⟨e.symm.measurable, by
    rw [← h.map_eq, map_map e.symm.measurable e.measurable, e.symm_comp_self, map_id]⟩
    -- 🎉 no goals
#align measure_theory.measure_preserving.symm MeasureTheory.MeasurePreserving.symm

theorem restrict_preimage {f : α → β} (hf : MeasurePreserving f μa μb) {s : Set β}
    (hs : MeasurableSet s) : MeasurePreserving f (μa.restrict (f ⁻¹' s)) (μb.restrict s) :=
  ⟨hf.measurable, by rw [← hf.map_eq, restrict_map hf.measurable hs]⟩
                     -- 🎉 no goals
#align measure_theory.measure_preserving.restrict_preimage MeasureTheory.MeasurePreserving.restrict_preimage

theorem restrict_preimage_emb {f : α → β} (hf : MeasurePreserving f μa μb)
    (h₂ : MeasurableEmbedding f) (s : Set β) :
    MeasurePreserving f (μa.restrict (f ⁻¹' s)) (μb.restrict s) :=
  ⟨hf.measurable, by rw [← hf.map_eq, h₂.restrict_map]⟩
                     -- 🎉 no goals
#align measure_theory.measure_preserving.restrict_preimage_emb MeasureTheory.MeasurePreserving.restrict_preimage_emb

theorem restrict_image_emb {f : α → β} (hf : MeasurePreserving f μa μb) (h₂ : MeasurableEmbedding f)
    (s : Set α) : MeasurePreserving f (μa.restrict s) (μb.restrict (f '' s)) := by
  simpa only [Set.preimage_image_eq _ h₂.injective] using hf.restrict_preimage_emb h₂ (f '' s)
  -- 🎉 no goals
#align measure_theory.measure_preserving.restrict_image_emb MeasureTheory.MeasurePreserving.restrict_image_emb

theorem aemeasurable_comp_iff {f : α → β} (hf : MeasurePreserving f μa μb)
    (h₂ : MeasurableEmbedding f) {g : β → γ} : AEMeasurable (g ∘ f) μa ↔ AEMeasurable g μb := by
  rw [← hf.map_eq, h₂.aemeasurable_map_iff]
  -- 🎉 no goals
#align measure_theory.measure_preserving.ae_measurable_comp_iff MeasureTheory.MeasurePreserving.aemeasurable_comp_iff

protected theorem quasiMeasurePreserving {f : α → β} (hf : MeasurePreserving f μa μb) :
    QuasiMeasurePreserving f μa μb :=
  ⟨hf.1, hf.2.absolutelyContinuous⟩
#align measure_theory.measure_preserving.quasi_measure_preserving MeasureTheory.MeasurePreserving.quasiMeasurePreserving

protected theorem comp {g : β → γ} {f : α → β} (hg : MeasurePreserving g μb μc)
    (hf : MeasurePreserving f μa μb) : MeasurePreserving (g ∘ f) μa μc :=
  ⟨hg.1.comp hf.1, by rw [← map_map hg.1 hf.1, hf.2, hg.2]⟩
                      -- 🎉 no goals
#align measure_theory.measure_preserving.comp MeasureTheory.MeasurePreserving.comp

protected theorem comp_left_iff {g : α → β} {e : β ≃ᵐ γ} (h : MeasurePreserving e μb μc) :
    MeasurePreserving (e ∘ g) μa μc ↔ MeasurePreserving g μa μb := by
  refine' ⟨fun hg => _, fun hg => h.comp hg⟩
  -- ⊢ MeasurePreserving g
  convert (MeasurePreserving.symm e h).comp hg
  -- ⊢ g = ↑(MeasurableEquiv.symm e) ∘ ↑e ∘ g
  simp [← Function.comp.assoc e.symm e g]
  -- 🎉 no goals
#align measure_theory.measure_preserving.comp_left_iff MeasureTheory.MeasurePreserving.comp_left_iff

protected theorem comp_right_iff {g : α → β} {e : γ ≃ᵐ α} (h : MeasurePreserving e μc μa) :
    MeasurePreserving (g ∘ e) μc μb ↔ MeasurePreserving g μa μb := by
  refine' ⟨fun hg => _, fun hg => hg.comp h⟩
  -- ⊢ MeasurePreserving g
  convert hg.comp (MeasurePreserving.symm e h)
  -- ⊢ g = (g ∘ ↑e) ∘ ↑(MeasurableEquiv.symm e)
  simp [Function.comp.assoc g e e.symm]
  -- 🎉 no goals
#align measure_theory.measure_preserving.comp_right_iff MeasureTheory.MeasurePreserving.comp_right_iff

protected theorem sigmaFinite {f : α → β} (hf : MeasurePreserving f μa μb) [SigmaFinite μb] :
    SigmaFinite μa :=
  SigmaFinite.of_map μa hf.aemeasurable (by rwa [hf.map_eq])
                                            -- 🎉 no goals
#align measure_theory.measure_preserving.sigma_finite MeasureTheory.MeasurePreserving.sigmaFinite

theorem measure_preimage {f : α → β} (hf : MeasurePreserving f μa μb) {s : Set β}
    (hs : MeasurableSet s) : μa (f ⁻¹' s) = μb s := by rw [← hf.map_eq, map_apply hf.1 hs]
                                                       -- 🎉 no goals
#align measure_theory.measure_preserving.measure_preimage MeasureTheory.MeasurePreserving.measure_preimage

theorem measure_preimage_emb {f : α → β} (hf : MeasurePreserving f μa μb)
    (hfe : MeasurableEmbedding f) (s : Set β) : μa (f ⁻¹' s) = μb s := by
  rw [← hf.map_eq, hfe.map_apply]
  -- 🎉 no goals
#align measure_theory.measure_preserving.measure_preimage_emb MeasureTheory.MeasurePreserving.measure_preimage_emb

protected theorem iterate {f : α → α} (hf : MeasurePreserving f μa μa) :
    ∀ n, MeasurePreserving f^[n] μa μa
  | 0 => MeasurePreserving.id μa
  | n + 1 => (MeasurePreserving.iterate hf n).comp hf
#align measure_theory.measure_preserving.iterate MeasureTheory.MeasurePreserving.iterate

variable {μ : Measure α} {f : α → α} {s : Set α}

lemma measure_symmDiff_preimage_iterate_le
    (hf : MeasurePreserving f μ μ) (hs : MeasurableSet s) (n : ℕ) :
    μ (s ∆ (f^[n] ⁻¹' s)) ≤ n • μ (s ∆ (f ⁻¹' s)) := by
  induction' n with n ih; simp
  -- ⊢ ↑↑μ (s ∆ (f^[Nat.zero] ⁻¹' s)) ≤ Nat.zero • ↑↑μ (s ∆ (f ⁻¹' s))
                          -- ⊢ ↑↑μ (s ∆ (f^[Nat.succ n] ⁻¹' s)) ≤ Nat.succ n • ↑↑μ (s ∆ (f ⁻¹' s))
  simp only [add_smul, one_smul, ← n.add_one]
  -- ⊢ ↑↑μ (s ∆ (f^[n + 1] ⁻¹' s)) ≤ n • ↑↑μ (s ∆ (f ⁻¹' s)) + ↑↑μ (s ∆ (f ⁻¹' s))
  refine' le_trans (measure_symmDiff_le s (f^[n] ⁻¹' s) (f^[n+1] ⁻¹' s)) (add_le_add ih _)
  -- ⊢ ↑↑μ ((f^[n] ⁻¹' s) ∆ (f^[n + 1] ⁻¹' s)) ≤ ↑↑μ (s ∆ (f ⁻¹' s))
  replace hs : MeasurableSet (s ∆ (f ⁻¹' s)) := hs.symmDiff $ hf.measurable hs
  -- ⊢ ↑↑μ ((f^[n] ⁻¹' s) ∆ (f^[n + 1] ⁻¹' s)) ≤ ↑↑μ (s ∆ (f ⁻¹' s))
  rw [iterate_succ', preimage_comp, ← preimage_symmDiff, (hf.iterate n).measure_preimage hs]
  -- 🎉 no goals

/-- If `μ univ < n * μ s` and `f` is a map preserving measure `μ`,
then for some `x ∈ s` and `0 < m < n`, `f^[m] x ∈ s`. -/
theorem exists_mem_image_mem_of_volume_lt_mul_volume (hf : MeasurePreserving f μ μ)
    (hs : MeasurableSet s) {n : ℕ} (hvol : μ (Set.univ : Set α) < n * μ s) :
    ∃ x ∈ s, ∃ m ∈ Set.Ioo 0 n, f^[m] x ∈ s := by
  have A : ∀ m, MeasurableSet (f^[m] ⁻¹' s) := fun m => (hf.iterate m).measurable hs
  -- ⊢ ∃ x, x ∈ s ∧ ∃ m, m ∈ Ioo 0 n ∧ f^[m] x ∈ s
  have B : ∀ m, μ (f^[m] ⁻¹' s) = μ s := fun m => (hf.iterate m).measure_preimage hs
  -- ⊢ ∃ x, x ∈ s ∧ ∃ m, m ∈ Ioo 0 n ∧ f^[m] x ∈ s
  have : μ (Set.univ : Set α) < (Finset.range n).sum fun m => μ (f^[m] ⁻¹' s) := by
    simpa only [B, nsmul_eq_mul, Finset.sum_const, Finset.card_range]
  rcases exists_nonempty_inter_of_measure_univ_lt_sum_measure μ (fun m _ => A m) this with
    ⟨i, hi, j, hj, hij, x, hxi, hxj⟩
  wlog hlt : i < j generalizing i j
  -- ⊢ ∃ x, x ∈ s ∧ ∃ m, m ∈ Ioo 0 n ∧ f^[m] x ∈ s
  · exact this j hj i hi hij.symm hxj hxi (hij.lt_or_lt.resolve_left hlt)
    -- 🎉 no goals
  simp only [Set.mem_preimage, Finset.mem_range] at hi hj hxi hxj
  -- ⊢ ∃ x, x ∈ s ∧ ∃ m, m ∈ Ioo 0 n ∧ f^[m] x ∈ s
  refine' ⟨f^[i] x, hxi, j - i, ⟨tsub_pos_of_lt hlt, lt_of_le_of_lt (j.sub_le i) hj⟩, _⟩
  -- ⊢ f^[j - i] (f^[i] x) ∈ s
  rwa [← iterate_add_apply, tsub_add_cancel_of_le hlt.le]
  -- 🎉 no goals
#align measure_theory.measure_preserving.exists_mem_image_mem_of_volume_lt_mul_volume MeasureTheory.MeasurePreserving.exists_mem_image_mem_of_volume_lt_mul_volume

/-- A self-map preserving a finite measure is conservative: if `μ s ≠ 0`, then at least one point
`x ∈ s` comes back to `s` under iterations of `f`. Actually, a.e. point of `s` comes back to `s`
infinitely many times, see `MeasureTheory.MeasurePreserving.conservative` and theorems about
`MeasureTheory.Conservative`. -/
theorem exists_mem_image_mem [IsFiniteMeasure μ] (hf : MeasurePreserving f μ μ)
    (hs : MeasurableSet s) (hs' : μ s ≠ 0) : ∃ x ∈ s, ∃ (m : _) (_ : m ≠ 0), f^[m] x ∈ s := by
  rcases ENNReal.exists_nat_mul_gt hs' (measure_ne_top μ (Set.univ : Set α)) with ⟨N, hN⟩
  -- ⊢ ∃ x, x ∈ s ∧ ∃ m x_1, f^[m] x ∈ s
  rcases hf.exists_mem_image_mem_of_volume_lt_mul_volume hs hN with ⟨x, hx, m, hm, hmx⟩
  -- ⊢ ∃ x, x ∈ s ∧ ∃ m x_1, f^[m] x ∈ s
  exact ⟨x, hx, m, hm.1.ne', hmx⟩
  -- 🎉 no goals
#align measure_theory.measure_preserving.exists_mem_image_mem MeasureTheory.MeasurePreserving.exists_mem_image_mem

end MeasurePreserving

namespace MeasurableEquiv

theorem measurePreserving_symm (μ : Measure α) (e : α ≃ᵐ β) :
    MeasurePreserving e.symm (map e μ) μ :=
  (e.measurable.measurePreserving μ).symm _
#align measure_theory.measurable_equiv.measure_preserving_symm MeasureTheory.MeasurableEquiv.measurePreserving_symm

end MeasurableEquiv

end MeasureTheory
