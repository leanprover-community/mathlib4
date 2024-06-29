/-
Copyright (c) 2023 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
import Mathlib.MeasureTheory.Integral.Marginal

/-!
# An example application of the marginal operation

Compute the volume of a set using slices.
-/


open scoped Classical ENNReal
open Set Function Equiv Finset

noncomputable section

namespace MeasureTheory

section

/-! Compute some measures using marginal. -/

variable {n : ℕ} {α : Fin (n+1) → Type*} [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
variable [∀ i, SigmaFinite (μ i)]

open Fin

@[simp]
theorem insertNth_dcomp_succAbove (i : Fin (n + 1)) (x : α i) (p : ∀ j, α (i.succAbove j)) :
    insertNth i x p ∘' i.succAbove = p :=
  funext (insertNth_apply_succAbove i x p)

@[simp]
theorem insertNth_apply_dcomp_succAbove (i : Fin (n + 1)) (x : α i) (z : ∀ i, α i) :
    insertNth i x (z ∘' i.succAbove) = update z i x := by
  ext j
  rcases eq_or_ne i j with rfl|hij
  · simp
  obtain ⟨j', rfl⟩ := exists_succAbove_eq_iff.mpr hij.symm
  simp [dcomp, hij.symm]

theorem insertNth_comp_dcomp_succAbove (i : Fin (n + 1)) (x : α i) :
    insertNth i x ∘ (· ∘' i.succAbove) = (update · i x) := by
  simp [comp]

theorem insertNth_eq_of_ne {i j : Fin (n + 1)} (h : i ≠ j) (x x' : α i)
    (p : ∀ j, α (i.succAbove j)) : insertNth i x p j = insertNth i x' p j := by
  obtain ⟨j', rfl⟩ := exists_succAbove_eq_iff.mpr h.symm
  simp

@[simp]
theorem update_insertNth {i : Fin (n + 1)} (x x' : α i) (p : ∀ j, α (i.succAbove j)) :
    update (insertNth i x p) i x' = insertNth i x' p := by
  ext j
  rcases eq_or_ne i j with rfl|hij
  · simp
  simp [hij.symm, insertNth_eq_of_ne hij x x']

theorem measurable_insertNth {i : Fin (n+1)} (x : α i) :
    Measurable (insertNth i x) := by
  refine measurable_pi_iff.mpr fun j ↦ ?_
  rcases eq_or_ne i j with rfl|hij
  · simp
  obtain ⟨j', rfl⟩ := exists_succAbove_eq_iff.mpr hij.symm
  simp [measurable_pi_apply]

/-- An example of a computation we can do with `lmarginal`. Working with `lmarginal` directly is
  probably easier than using this lemma, though. This is roughly `FUBINI_SIMPLE` from HOL Light,
  though this has weaker assumptions (HOL Light assumes that `s` is bounded in `ℝⁿ`).
  Note: we could generalize `i.succAbove : Fin n → Fin (n+1)` to an arbitrary injective map `ι → ι'`
  whose range misses one point. -/
theorem lintegral_measure_insertNth {s : Set (∀ i, α i)} (hs : MeasurableSet s) (i : Fin (n+1)) :
    ∫⁻ x, Measure.pi (μ ∘' i.succAbove) (insertNth i x ⁻¹' s) ∂μ i =
    Measure.pi μ s := by
  rcases isEmpty_or_nonempty (α i) with h|⟨⟨x⟩⟩
  · have : IsEmpty (∀ i, α i) := ⟨λ x ↦ h.elim <| x i⟩
    simp [lintegral_of_isEmpty, Measure.eq_zero_of_isEmpty]
  rcases isEmpty_or_nonempty (∀ j, α (i.succAbove j)) with h|⟨⟨y⟩⟩
  · have : IsEmpty (∀ i, α i) := ⟨λ x ↦ h.elim <| λ j ↦ x _⟩
    simp [Measure.eq_zero_of_isEmpty]
  have hi : i ∉ ({i}ᶜ : Finset _) := not_mem_compl.mpr <| mem_singleton_self i
  let z := insertNth i x y
  calc ∫⁻ x : α i, Measure.pi (μ ∘' succAbove i) (insertNth i x ⁻¹' s) ∂μ i
      = ∫⁻ x : α i, (∫⋯∫⁻_.univ, indicator (insertNth i x ⁻¹' s) 1 ∂μ ∘' succAbove i) y ∂μ i := by
        simp_rw [← lintegral_indicator_one (measurable_insertNth _ hs),
          lintegral_eq_lmarginal_univ y]
    _ = ∫⁻ x : α i, (∫⋯∫⁻_.univ, indicator (insertNth i x ⁻¹' s) 1 ∂μ ∘' succAbove i)
          (z ∘' i.succAbove) ∂μ i := by
        rw [← insertNth_dcomp_succAbove i x y]
    _ = ∫⁻ x : α i, (∫⋯∫⁻_{i}ᶜ,
          indicator (insertNth i x ⁻¹' s) 1 ∘ (· ∘' succAbove i) ∂μ) z ∂μ i := by
        simp_rw [← λ x ↦ lmarginal_image succAbove_right_injective (μ := μ) .univ
          (f := indicator (insertNth i x ⁻¹' s) (1 : ((j : Fin n) → α (succAbove i j)) → ℝ≥0∞))
          (measurable_one.indicator (measurable_insertNth _ hs)) z, Fin.image_succAbove_univ]
    _ = ∫⁻ x : α i, (∫⋯∫⁻_{i}ᶜ,
          indicator (insertNth i x ∘ (· ∘' succAbove i) ⁻¹' s) 1 ∂μ) z ∂μ i := by
        rfl
    _ = ∫⁻ x : α i, (∫⋯∫⁻_{i}ᶜ,
          indicator ((Function.update · i x) ⁻¹' s) 1 ∂μ) z ∂μ i := by
        simp [comp]
    _ = (∫⋯∫⁻_insert i {i}ᶜ, indicator s 1 ∂μ) z := by
        simp_rw [lmarginal_insert _ (measurable_one.indicator hs) hi,
          lmarginal_update_of_not_mem (measurable_one.indicator hs) hi]
        rfl
    _ = (∫⋯∫⁻_.univ, indicator s 1 ∂μ) z := by simp
    _ = Measure.pi μ s := by rw [← lintegral_indicator_one hs, lintegral_eq_lmarginal_univ z]

end

section MeasureSpace

/-! Compute some measures using marginal. -/

variable {n : ℕ} {α : Fin (n+1) → Type*}
variable [∀ i, MeasureSpace (α i)] [∀ i, SigmaFinite (volume (α := α i))]

open Fin

theorem lintegral_volume_insertNth {s : Set (∀ i, α i)} (hs : MeasurableSet s) (i : Fin (n+1)) :
    ∫⁻ x, volume (insertNth i x ⁻¹' s) = volume s :=
  lintegral_measure_insertNth (fun _ ↦ volume) hs i

end MeasureSpace

end MeasureTheory
