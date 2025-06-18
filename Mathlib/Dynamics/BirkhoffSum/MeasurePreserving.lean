/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

/-!
# Birkhoff sum for measure preserving maps

This file contains some lemmas about the Birkhoff sum (`birkhoffSum`) and Birkhoff average
(`birkhoffAverage`) of a function which preserves a measure.
-/

section MeasurePreserving

open MeasureTheory Filter

variable {α M : Type*} [AddCommMonoid M] [MeasurableSpace α]
variable {R : Type*} [DivisionSemiring R] [Module R M]
variable {f : α → α} {μ : Measure α} {φ : α → M} {φ' : α → M}

/-- If `φ` and `φ'` are `ae μ` equal then the corresponding `birkhoffSum` are `ae μ` equal. -/
theorem birkhoffSum_ae_eq_of_ae_eq (hf : MeasurePreserving f μ μ) (hφ : φ =ᶠ[ae μ] φ') (n : ℕ) :
    birkhoffSum f φ n =ᶠ[ae μ] birkhoffSum f φ' n := by
  obtain ⟨s, hs, hs'⟩ := eventuallyEq_iff_exists_mem.mp hφ
  let t := {x | ∀ n, f^[n] x ∈ s}
  have ht : t ∈ ae μ := by
    refine mem_ae_iff.mpr ?_
    rw [show tᶜ = ⋃ n, (f^[n])⁻¹' sᶜ by ext x; simp [t]]
    refine measure_iUnion_null_iff.mpr fun m ↦ nonpos_iff_eq_zero.mp ?_
    exact le_of_le_of_eq ((hf.iterate m).measure_preimage_le sᶜ) hs
  refine EventuallyEq.eventually <| eventuallyEq_iff_exists_mem.mpr ⟨t, ht, fun x hx  ↦ ?_⟩
  exact Finset.sum_congr rfl fun x _ => hs' (hx x)

/-- If `φ` and `φ'` are `ae μ` equal then the corresponding `birkhoffAverage` are `ae μ` equal. -/
theorem birkhoffAverage_ae_eq_of_ae_eq (hf : MeasurePreserving f μ μ) (hφ : φ =ᶠ[ae μ] φ') (n : ℕ) :
    birkhoffAverage R f φ n =ᶠ[ae μ] birkhoffAverage R f φ' n :=
  EventuallyEq.const_smul (birkhoffSum_ae_eq_of_ae_eq hf hφ n) (n : R)⁻¹

variable [TopologicalSpace M]

/-- If `φ` is `AEStronglyMeasurable` then the `birkhoffSum` is `ae μ` equal to the `birkhoffSum` of
its measurable version. -/
theorem birkhoffSum_eq_of_AEStronglyMeasurable (hf : MeasurePreserving f μ μ)
    (hφ : AEStronglyMeasurable φ μ) n : birkhoffSum f φ n =ᶠ[ae μ] birkhoffSum f hφ.mk n :=
  birkhoffSum_ae_eq_of_ae_eq hf hφ.ae_eq_mk n

/-- If `φ` is `AEStronglyMeasurable` then the `birkhoffAverage` is equal to the `birkhoffAverage` of
its measurable version. -/
theorem birkhoffAverage_eq_of_AEStronglyMeasurable (hf : MeasurePreserving f μ μ)
    (hφ : AEStronglyMeasurable φ μ) n :
    birkhoffAverage R f φ n =ᶠ[ae μ] birkhoffAverage R f hφ.mk n :=
  birkhoffAverage_ae_eq_of_ae_eq hf hφ.ae_eq_mk n

end MeasurePreserving
