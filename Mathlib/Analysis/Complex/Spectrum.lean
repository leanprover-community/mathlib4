/-
Copyright (c) 2021 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
import Mathlib.Analysis.Complex.Basic

/-!
# Some lemmas on the spectrum and quasispectrum of elements and positivity on `ℂ`
-/

namespace SpectrumRestricts
variable {A : Type*} [Ring A]

lemma real_iff [Algebra ℂ A] {a : A} :
    SpectrumRestricts a Complex.reCLM ↔ ∀ x ∈ spectrum ℂ a, x = x.re := by
  refine ⟨fun h x hx ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨x, -, rfl⟩ := h.algebraMap_image.symm ▸ hx
    simp
  · exact .of_subset_range_algebraMap Complex.ofReal_re fun x hx ↦ ⟨x.re, (h x hx).symm⟩

end SpectrumRestricts

namespace QuasispectrumRestricts
local notation "σₙ" => quasispectrum
variable {A : Type*} [NonUnitalRing A]

lemma real_iff [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] {a : A} :
    QuasispectrumRestricts a Complex.reCLM ↔ ∀ x ∈ σₙ ℂ a, x = x.re := by
  rw [quasispectrumRestricts_iff_spectrumRestricts_inr,
    Unitization.quasispectrum_eq_spectrum_inr' _ ℂ, SpectrumRestricts.real_iff]

end QuasispectrumRestricts
