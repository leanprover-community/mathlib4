/-
Copyright (c) 2021 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
public import Mathlib.Topology.Instances.NNReal.Lemmas

import Mathlib.Tactic.ContinuousFunctionalCalculus

/-!
# Some lemmas on the spectrum and quasispectrum of elements and positivity

-/

public section

namespace SpectrumRestricts

open NNReal

variable {A : Type*} [Ring A] [Algebra ℝ A]

lemma nnReal_iff {a : A} :
    SpectrumRestricts a ContinuousMap.realToNNReal ↔ ∀ x ∈ spectrum ℝ a, 0 ≤ x := by
  refine ⟨fun h x hx ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨x, -, rfl⟩ := h.algebraMap_image.symm ▸ hx
    exact coe_nonneg x
  · exact .of_subset_range_algebraMap (fun _ ↦ Real.toNNReal_coe) fun x hx ↦ ⟨⟨x, h x hx⟩, rfl⟩

@[deprecated (since := "2026-10-27")] alias nnreal_iff := nnReal_iff

lemma nnReal_of_nonneg [PartialOrder A] [NonnegSpectrumClass ℝ A] {a : A} (ha : 0 ≤ a) :
    SpectrumRestricts a ContinuousMap.realToNNReal :=
  nnReal_iff.mpr <| spectrum_nonneg_of_nonneg ha

@[deprecated (since := "2026-10-27")] alias nnreal_of_nonneg := nnReal_of_nonneg

lemma nnReal_le_iff {a : A}
    (ha : SpectrumRestricts a ContinuousMap.realToNNReal) {r : ℝ≥0} :
    (∀ x ∈ spectrum ℝ≥0 a, r ≤ x) ↔ ∀ x ∈ spectrum ℝ a, r ≤ x := by
  simp [← ha.algebraMap_image]

@[deprecated (since := "2026-10-27")] alias nnreal_le_iff := nnReal_le_iff

lemma nnReal_lt_iff {a : A}
    (ha : SpectrumRestricts a ContinuousMap.realToNNReal) {r : ℝ≥0} :
    (∀ x ∈ spectrum ℝ≥0 a, r < x) ↔ ∀ x ∈ spectrum ℝ a, r < x := by
  simp [← ha.algebraMap_image]

@[deprecated (since := "2026-10-27")] alias nnreal_lt_iff := nnReal_lt_iff

lemma le_nnReal_iff {a : A}
    (ha : SpectrumRestricts a ContinuousMap.realToNNReal) {r : ℝ≥0} :
    (∀ x ∈ spectrum ℝ≥0 a, x ≤ r) ↔ ∀ x ∈ spectrum ℝ a, x ≤ r := by
  simp [← ha.algebraMap_image]

@[deprecated (since := "2026-10-27")] alias le_nnreal_iff := le_nnReal_iff

lemma lt_nnReal_iff {a : A}
    (ha : SpectrumRestricts a ContinuousMap.realToNNReal) {r : ℝ≥0} :
    (∀ x ∈ spectrum ℝ≥0 a, x < r) ↔ ∀ x ∈ spectrum ℝ a, x < r := by
  simp [← ha.algebraMap_image]

@[deprecated (since := "2026-10-27")] alias lt_nnreal_iff := lt_nnReal_iff

end SpectrumRestricts

namespace QuasispectrumRestricts

open NNReal
local notation "σₙ" => quasispectrum

variable {A : Type*} [NonUnitalRing A]

lemma nnReal_iff [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] {a : A} :
    QuasispectrumRestricts a ContinuousMap.realToNNReal ↔ ∀ x ∈ σₙ ℝ a, 0 ≤ x := by
  rw [quasispectrumRestricts_iff_spectrumRestricts_inr,
    Unitization.quasispectrum_eq_spectrum_inr' _ ℝ, SpectrumRestricts.nnReal_iff]

@[deprecated (since := "2026-10-27")] alias nnreal_iff := nnReal_iff

lemma nnReal_of_nonneg [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [PartialOrder A]
    [NonnegSpectrumClass ℝ A] {a : A} (ha : 0 ≤ a) :
    QuasispectrumRestricts a ContinuousMap.realToNNReal :=
  nnReal_iff.mpr <| quasispectrum_nonneg_of_nonneg _ ha

@[deprecated (since := "2026-10-27")] alias nnreal_of_nonneg := nnReal_of_nonneg

lemma le_nnReal_iff [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] {a : A}
    (ha : QuasispectrumRestricts a ContinuousMap.realToNNReal) {r : ℝ≥0} :
    (∀ x ∈ quasispectrum ℝ≥0 a, x ≤ r) ↔ ∀ x ∈ quasispectrum ℝ a, x ≤ r := by
  simp [← ha.algebraMap_image]

@[deprecated (since := "2026-10-27")] alias le_nnreal_iff := le_nnReal_iff

lemma lt_nnReal_iff [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] {a : A}
    (ha : QuasispectrumRestricts a ContinuousMap.realToNNReal) {r : ℝ≥0} :
    (∀ x ∈ quasispectrum ℝ≥0 a, x < r) ↔ ∀ x ∈ quasispectrum ℝ a, x < r := by
  simp [← ha.algebraMap_image]

@[deprecated (since := "2026-10-27")] alias lt_nnreal_iff := lt_nnReal_iff

end QuasispectrumRestricts

open scoped NNReal in
@[deprecated spectrum.algebraMap_mem_iff +typeChanged (since := "2026-09-22")]
lemma coe_mem_spectrum_real_of_nonneg {A : Type*} [Ring A] [PartialOrder A] [Algebra ℝ A]
    {a : A} {x : ℝ≥0} (_ha : 0 ≤ a := by cfc_tac) :
    (x : ℝ) ∈ spectrum ℝ a ↔ x ∈ spectrum ℝ≥0 a :=
  spectrum.algebraMap_mem_iff ℝ (R := ℝ≥0)
