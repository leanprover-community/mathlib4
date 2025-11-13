/-
Copyright (c) 2021 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Tactic.ContinuousFunctionalCalculus

/-!
# Some lemmas on the spectrum and quasispectrum of elements and positivity

-/

namespace SpectrumRestricts

open NNReal ENNReal

variable {A : Type*} [Ring A] [Algebra ℝ A]

lemma nnreal_iff {a : A} :
    SpectrumRestricts a ContinuousMap.realToNNReal ↔ ∀ x ∈ spectrum ℝ a, 0 ≤ x := by
  refine ⟨fun h x hx ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨x, -, rfl⟩ := h.algebraMap_image.symm ▸ hx
    exact coe_nonneg x
  · exact .of_subset_range_algebraMap (fun _ ↦ Real.toNNReal_coe) fun x hx ↦ ⟨⟨x, h x hx⟩, rfl⟩

lemma nnreal_of_nonneg [PartialOrder A] [NonnegSpectrumClass ℝ A] {a : A} (ha : 0 ≤ a) :
    SpectrumRestricts a ContinuousMap.realToNNReal :=
  nnreal_iff.mpr <| spectrum_nonneg_of_nonneg ha

lemma nnreal_le_iff {a : A}
    (ha : SpectrumRestricts a ContinuousMap.realToNNReal) {r : ℝ≥0} :
    (∀ x ∈ spectrum ℝ≥0 a, r ≤ x) ↔ ∀ x ∈ spectrum ℝ a, r ≤ x := by
  simp [← ha.algebraMap_image]

lemma nnreal_lt_iff {a : A}
    (ha : SpectrumRestricts a ContinuousMap.realToNNReal) {r : ℝ≥0} :
    (∀ x ∈ spectrum ℝ≥0 a, r < x) ↔ ∀ x ∈ spectrum ℝ a, r < x := by
  simp [← ha.algebraMap_image]

lemma le_nnreal_iff {a : A}
    (ha : SpectrumRestricts a ContinuousMap.realToNNReal) {r : ℝ≥0} :
    (∀ x ∈ spectrum ℝ≥0 a, x ≤ r) ↔ ∀ x ∈ spectrum ℝ a, x ≤ r := by
  simp [← ha.algebraMap_image]

lemma lt_nnreal_iff {a : A}
    (ha : SpectrumRestricts a ContinuousMap.realToNNReal) {r : ℝ≥0} :
    (∀ x ∈ spectrum ℝ≥0 a, x < r) ↔ ∀ x ∈ spectrum ℝ a, x < r := by
  simp [← ha.algebraMap_image]

end SpectrumRestricts

namespace QuasispectrumRestricts

open NNReal ENNReal
local notation "σₙ" => quasispectrum

variable {A : Type*} [NonUnitalRing A]

lemma nnreal_iff [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] {a : A} :
    QuasispectrumRestricts a ContinuousMap.realToNNReal ↔ ∀ x ∈ σₙ ℝ a, 0 ≤ x := by
  rw [quasispectrumRestricts_iff_spectrumRestricts_inr,
    Unitization.quasispectrum_eq_spectrum_inr' _ ℝ, SpectrumRestricts.nnreal_iff]

lemma nnreal_of_nonneg [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [PartialOrder A]
    [NonnegSpectrumClass ℝ A] {a : A} (ha : 0 ≤ a) :
    QuasispectrumRestricts a ContinuousMap.realToNNReal :=
  nnreal_iff.mpr <| quasispectrum_nonneg_of_nonneg _ ha

lemma le_nnreal_iff [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] {a : A}
    (ha : QuasispectrumRestricts a ContinuousMap.realToNNReal) {r : ℝ≥0} :
    (∀ x ∈ quasispectrum ℝ≥0 a, x ≤ r) ↔ ∀ x ∈ quasispectrum ℝ a, x ≤ r := by
  simp [← ha.algebraMap_image]

lemma lt_nnreal_iff [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] {a : A}
    (ha : QuasispectrumRestricts a ContinuousMap.realToNNReal) {r : ℝ≥0} :
    (∀ x ∈ quasispectrum ℝ≥0 a, x < r) ↔ ∀ x ∈ quasispectrum ℝ a, x < r := by
  simp [← ha.algebraMap_image]

end QuasispectrumRestricts

variable {A : Type*} [Ring A] [PartialOrder A]

open scoped NNReal

lemma coe_mem_spectrum_real_of_nonneg [Algebra ℝ A] [NonnegSpectrumClass ℝ A] {a : A} {x : ℝ≥0}
    (ha : 0 ≤ a := by cfc_tac) :
    (x : ℝ) ∈ spectrum ℝ a ↔ x ∈ spectrum ℝ≥0 a := by
  simp [← (SpectrumRestricts.nnreal_of_nonneg ha).algebraMap_image, Set.mem_image,
    NNReal.algebraMap_eq_coe]
