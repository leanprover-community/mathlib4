/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
/-!
# Birkhoff sum for measure preserving maps

This file contains some lemmas about the `birkhoffSum` and `birkhoffAverage` of a map which is
`QuasiMeasurePreserving`.
-/

section MeasurePreserving

open MeasureTheory Measure Filter

variable {α M : Type*} [AddCommMonoid M] [MeasurableSpace α]
variable {R : Type*} [DivisionSemiring R] [Module R M]
variable {f : α → α} {μ : Measure α} {φ φ' : α → M}

/-- If `φ` and `φ'` are `ae μ` equal then the corresponding `birkhoffSum` are `=ᵐ[μ]` equal. -/
theorem birkhoffSum_ae_eq_of_ae_eq (hf : QuasiMeasurePreserving f μ μ) (hφ : φ =ᵐ[μ] φ') n :
    birkhoffSum f φ n =ᵐ[μ] birkhoffSum f φ' n := by
  obtain ⟨s, hs, hs'⟩ := eventuallyEq_iff_exists_mem.mp hφ
  let t := {x | ∀ n, f^[n] x ∈ s}
  have ht : t ∈ ae μ := by
    refine mem_ae_iff.mpr ?_
    rw [show tᶜ = ⋃ n, (f^[n])⁻¹' sᶜ by ext x; simp [t]]
    exact measure_iUnion_null_iff.mpr fun n ↦ (hf.iterate n).preimage_null hs
  filter_upwards [ht] with x hx
  exact Finset.sum_congr rfl fun x _ => hs' (hx x)

/-- If `φ` and `φ'` are `ae μ` equal then the corresponding `birkhoffAverage` are `=ᵐ[μ]` equal. -/
theorem birkhoffAverage_ae_eq_of_ae_eq (hf : QuasiMeasurePreserving f μ μ) (hφ : φ =ᵐ[μ] φ') n :
    birkhoffAverage R f φ n =ᵐ[μ] birkhoffAverage R f φ' n :=
  EventuallyEq.const_smul (birkhoffSum_ae_eq_of_ae_eq hf hφ n) (n : R)⁻¹

end MeasurePreserving
