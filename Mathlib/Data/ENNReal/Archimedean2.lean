/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.Data.ENNReal.Archimedean
import Mathlib.Data.ENNReal.Real

/-!
# Maps between real and extended non-negative real numbers

This file focuses on the functions `ENNReal.toReal : ℝ≥0∞ → ℝ` and `ENNReal.ofReal : ℝ → ℝ≥0∞` which
were defined in `Data.ENNReal.Basic`. It collects all the basic results of the interactions between
these functions and the algebraic and lattice operations, although a few may appear in earlier
files.

This file provides a `positivity` extension for `ENNReal.ofReal`.

# Main theorems

  - `trichotomy (p : ℝ≥0∞) : p = 0 ∨ p = ∞ ∨ 0 < p.toReal`: often used for `WithLp` and `lp`
  - `dichotomy (p : ℝ≥0∞) [Fact (1 ≤ p)] : p = ∞ ∨ 1 ≤ p.toReal`: often used for `WithLp` and `lp`
  - `toNNReal_iInf` through `toReal_sSup`: these declarations allow for easy conversions between
    indexed or set infima and suprema in `ℝ`, `ℝ≥0` and `ℝ≥0∞`. This is especially useful because
    `ℝ≥0∞` is a complete lattice.
-/

assert_not_exists Finset

open Set NNReal ENNReal

namespace ENNReal

section iInf

variable {ι : Sort*} {f g : ι → ℝ≥0∞}
variable {a b c d : ℝ≥0∞} {r p q : ℝ≥0}

theorem toNNReal_iInf (hf : ∀ i, f i ≠ ∞) : (iInf f).toNNReal = ⨅ i, (f i).toNNReal := by
  cases isEmpty_or_nonempty ι
  · rw [iInf_of_empty, toNNReal_top, NNReal.iInf_empty]
  · lift f to ι → ℝ≥0 using hf
    simp_rw [← coe_iInf, toNNReal_coe]

theorem toNNReal_sInf (s : Set ℝ≥0∞) (hs : ∀ r ∈ s, r ≠ ∞) :
    (sInf s).toNNReal = sInf (ENNReal.toNNReal '' s) := by
  have hf : ∀ i, ((↑) : s → ℝ≥0∞) i ≠ ∞ := fun ⟨r, rs⟩ => hs r rs
  simpa only [← sInf_range, ← image_eq_range, Subtype.range_coe_subtype] using (toNNReal_iInf hf)

theorem toNNReal_iSup (hf : ∀ i, f i ≠ ∞) : (iSup f).toNNReal = ⨆ i, (f i).toNNReal := by
  lift f to ι → ℝ≥0 using hf
  simp_rw [toNNReal_coe]
  by_cases h : BddAbove (range f)
  · rw [← coe_iSup h, toNNReal_coe]
  · rw [NNReal.iSup_of_not_bddAbove h, iSup_coe_eq_top.2 h, toNNReal_top]

theorem toNNReal_sSup (s : Set ℝ≥0∞) (hs : ∀ r ∈ s, r ≠ ∞) :
    (sSup s).toNNReal = sSup (ENNReal.toNNReal '' s) := by
  have hf : ∀ i, ((↑) : s → ℝ≥0∞) i ≠ ∞ := fun ⟨r, rs⟩ => hs r rs
  simpa only [← sSup_range, ← image_eq_range, Subtype.range_coe_subtype] using (toNNReal_iSup hf)

theorem toReal_iInf (hf : ∀ i, f i ≠ ∞) : (iInf f).toReal = ⨅ i, (f i).toReal := by
  simp only [ENNReal.toReal, toNNReal_iInf hf, NNReal.coe_iInf]

theorem toReal_sInf (s : Set ℝ≥0∞) (hf : ∀ r ∈ s, r ≠ ∞) :
    (sInf s).toReal = sInf (ENNReal.toReal '' s) := by
  simp only [ENNReal.toReal, toNNReal_sInf s hf, NNReal.coe_sInf, Set.image_image]

theorem toReal_iSup (hf : ∀ i, f i ≠ ∞) : (iSup f).toReal = ⨆ i, (f i).toReal := by
  simp only [ENNReal.toReal, toNNReal_iSup hf, NNReal.coe_iSup]

theorem toReal_sSup (s : Set ℝ≥0∞) (hf : ∀ r ∈ s, r ≠ ∞) :
    (sSup s).toReal = sSup (ENNReal.toReal '' s) := by
  simp only [ENNReal.toReal, toNNReal_sSup s hf, NNReal.coe_sSup, Set.image_image]

@[simp] lemma ofReal_iInf [Nonempty ι] (f : ι → ℝ) :
    ENNReal.ofReal (⨅ i, f i) = ⨅ i, ENNReal.ofReal (f i) := by
  obtain ⟨i, hi⟩ | h := em (∃ i, f i ≤ 0)
  · rw [(iInf_eq_bot _).2 fun _ _ ↦ ⟨i, by simpa [ofReal_of_nonpos hi]⟩]
    simp [Real.iInf_nonpos' ⟨i, hi⟩]
  replace h i : 0 ≤ f i := le_of_not_le fun hi ↦ h ⟨i, hi⟩
  refine eq_of_forall_le_iff fun a ↦ ?_
  obtain rfl | ha := eq_or_ne a ∞
  · simp
  rw [le_iInf_iff, le_ofReal_iff_toReal_le ha, le_ciInf_iff ⟨0, by simpa [mem_lowerBounds]⟩]
  · exact forall_congr' fun i ↦ (le_ofReal_iff_toReal_le ha (h _)).symm
  · exact Real.iInf_nonneg h

theorem iInf_add : iInf f + a = ⨅ i, f i + a :=
  le_antisymm (le_iInf fun _ => add_le_add (iInf_le _ _) <| le_rfl)
    (tsub_le_iff_right.1 <| le_iInf fun _ => tsub_le_iff_right.2 <| iInf_le _ _)

theorem iSup_sub : (⨆ i, f i) - a = ⨆ i, f i - a :=
  le_antisymm (tsub_le_iff_right.2 <| iSup_le fun i => tsub_le_iff_right.1 <| le_iSup (f · - a) i)
    (iSup_le fun _ => tsub_le_tsub (le_iSup _ _) (le_refl a))

theorem sub_iInf : (a - ⨅ i, f i) = ⨆ i, a - f i := by
  refine eq_of_forall_ge_iff fun c => ?_
  rw [tsub_le_iff_right, add_comm, iInf_add]
  simp [tsub_le_iff_right, sub_eq_add_neg, add_comm]

theorem sInf_add {s : Set ℝ≥0∞} : sInf s + a = ⨅ b ∈ s, b + a := by simp [sInf_eq_iInf, iInf_add]

theorem add_iInf {a : ℝ≥0∞} : a + iInf f = ⨅ b, a + f b := by
  rw [add_comm, iInf_add]; simp [add_comm]

theorem iInf_add_iInf (h : ∀ i j, ∃ k, f k + g k ≤ f i + g j) : iInf f + iInf g = ⨅ a, f a + g a :=
  suffices ⨅ a, f a + g a ≤ iInf f + iInf g from
    le_antisymm (le_iInf fun _ => add_le_add (iInf_le _ _) (iInf_le _ _)) this
  calc
    ⨅ a, f a + g a ≤ ⨅ (a) (a'), f a + g a' :=
      le_iInf₂ fun a a' => let ⟨k, h⟩ := h a a'; iInf_le_of_le k h
    _ = iInf f + iInf g := by simp_rw [iInf_add, add_iInf]

end iInf

end ENNReal
