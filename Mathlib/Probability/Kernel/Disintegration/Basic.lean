/-
Copyright (c) 2024 Yaël Dillies, Kin Yau James Wong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Kin Yau James Wong
-/
import Mathlib.Probability.Kernel.MeasureCompProd

/-!
# Disintegration of measures and kernels

This file defines predicates for a kernel to "disintegrate" a measure or a kernel. This kernel is
also called the "conditional kernel" of the measure or kernel.

A measure `ρ : Measure (α × Ω)` is disintegrated by a kernel `ρCond : Kernel α Ω` if
`ρ.fst ⊗ₘ ρCond = ρ`.

A kernel `ρ : Kernel α (β × Ω)` is disintegrated by a kernel `κCond : Kernel (α × β) Ω` if
`κ.fst ⊗ₖ κCond = κ`.

## Main definitions

* `MeasureTheory.Measure.IsCondKernel ρ ρCond`: Predicate for the kernel `ρCond` to disintegrate the
  measure `ρ`.
* `ProbabilityTheory.Kernel.IsCondKernel κ κCond`: Predicate for the kernel `κ Cond` to disintegrate
  the kernel `κ`.

Further, if `κ` is a semifinite kernel from a countable `α` such that each measure `κ a` is
disintegrated by some kernel, then `κ` itself is disintegrated by a kernel, namely
`ProbabilityTheory.Kernel.condKernelCountable`.

## See also

`Mathlib.Probability.Kernel.Disintegration.Basic` for a **construction** of disintegrating kernels.
-/

open MeasureTheory Set Filter MeasurableSpace ProbabilityTheory
open scoped ENNReal MeasureTheory Topology

variable {α β Ω : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} [MeasurableSpace Ω]

/-!
### Disintegration of measures

This section provides a predicate for a kernel to disintegrate a measure.
-/

namespace MeasureTheory.Measure
variable (ρ : Measure (α × Ω)) [IsFiniteMeasure ρ] (ρCond : Kernel α Ω)

/-- A kernel `ρCond` is a conditional kernel for a measure `ρ` if it disintegrates it in the sense
that `ρ.fst ⊗ₘ ρCond = ρ`. -/
class IsCondKernel : Prop where
  disintegrate' : ρ.fst ⊗ₘ ρCond = ρ

variable [ρ.IsCondKernel ρCond]

lemma disintegrate : ρ.fst ⊗ₘ ρCond = ρ := IsCondKernel.disintegrate'

/-- Auxiliary lemma for `IsCondKernel.apply_of_ne_zero`. -/
private lemma IsCondKernel.apply_of_ne_zero_of_measurableSet [MeasurableSingletonClass α]
    [IsSFiniteKernel ρCond] {x : α} (hx : ρ.fst {x} ≠ 0) {s : Set Ω} (hs : MeasurableSet s) :
    ρCond x s = (ρ.fst {x})⁻¹ * ρ ({x} ×ˢ s) := by
  nth_rewrite 2 [← ρ.disintegrate ρCond]
  rw [Measure.compProd_apply (measurableSet_prod.mpr (Or.inl ⟨measurableSet_singleton x, hs⟩))]
  classical
  have (a) : ρCond a (Prod.mk a ⁻¹' {x} ×ˢ s) = ({x} : Set α).indicator (ρCond · s) a := by
    obtain rfl | hax := eq_or_ne a x
    · simp only [singleton_prod, mem_singleton_iff, indicator_of_mem]
      congr with y
      simp
    · simp only [singleton_prod, mem_singleton_iff, hax, not_false_eq_true, indicator_of_not_mem]
      have : Prod.mk a ⁻¹' (Prod.mk x '' s) = ∅ := by ext y; simp [Ne.symm hax]
      simp only [this, measure_empty]
  simp_rw [this]
  rw [MeasureTheory.lintegral_indicator _ (measurableSet_singleton x)]
  simp only [Measure.restrict_singleton, lintegral_smul_measure, lintegral_dirac]
  rw [← mul_assoc, ENNReal.inv_mul_cancel hx (measure_ne_top _ _), one_mul]

/-- If the singleton `{x}` has non-zero mass for `ρ.fst`, then for all `s : Set Ω`,
`ρCond x s = (ρ.fst {x})⁻¹ * ρ ({x} ×ˢ s)` . -/
lemma IsCondKernel.apply_of_ne_zero [MeasurableSingletonClass α] [IsSFiniteKernel ρCond] {x : α}
    (hx : ρ.fst {x} ≠ 0) (s : Set Ω) : ρCond x s = (ρ.fst {x})⁻¹ * ρ ({x} ×ˢ s) := by
  have : ρCond x s = ((ρ.fst {x})⁻¹ • ρ).comap (fun (y : Ω) ↦ (x, y)) s := by
    congr 2 with s hs
    simp [IsCondKernel.apply_of_ne_zero_of_measurableSet _ _ hx hs,
      (measurableEmbedding_prod_mk_left x).comap_apply]
  simp [this, (measurableEmbedding_prod_mk_left x).comap_apply, hx]

-- TODO: Can we generalise away from `MeasurableSingletonClass`, using eg `measurableAtom a` instead
-- of `{a}`?
lemma IsCondKernel.isMarkovKernel_iff_isSFiniteKernel [MeasurableSingletonClass α]
    (hρ : ∀ a, ρ.fst {a} ≠ 0) : IsMarkovKernel ρCond ↔ IsSFiniteKernel ρCond := by
  refine ⟨fun _ ↦ inferInstance, fun _ ↦ ⟨fun a ↦ ⟨?_⟩⟩⟩
  rw [IsCondKernel.apply_of_ne_zero _ _ (hρ _), prod_univ, ← Measure.fst_apply
    (measurableSet_singleton _), ENNReal.inv_mul_cancel (hρ _) (measure_ne_top _ _)]

end MeasureTheory.Measure

/-!
### Disintegration of kernels

This section provides a predicate for a kernel to disintegrate a kernel, and proves that such a
disintegrating kernel exists for a countable space if we have disintegrating.
-/

namespace ProbabilityTheory.Kernel
variable (κ : Kernel α (β × Ω)) [IsFiniteKernel κ] (κCond : Kernel (α × β) Ω)

/-! #### Predicate for a kernel to disintegrate a kernel -/

/-- A kernel `κCond` is a conditional kernel for a kernel `κ` if it disintegrates it in the sense
that `κ.fst ⊗ₖ κCond = κ`. -/
class IsCondKernel : Prop where
  disintegrate' : κ.fst ⊗ₖ κCond = κ

variable [κ.IsCondKernel κCond]

lemma disintegrate : κ.fst ⊗ₖ κCond = κ := IsCondKernel.disintegrate'

/-! #### Existence of a disintegrating kernel in a countable space -/

section Countable
variable [Countable α] (κCond : α → Kernel β Ω)
  (h_atom : ∀ x y, x ∈ measurableAtom y → κCond x = κCond y)

/-- Auxiliary definition for `ProbabilityTheory.Kernel.condKernel`.

A conditional kernel for `κ : Kernel α (β × Ω)` where `α` is countable and `Ω` is a measurable
space. -/
noncomputable def condKernelCountable : Kernel (α × β) Ω where
  toFun p := κCond p.1 p.2
  measurable' := by
    change Measurable ((fun q : β × α ↦ (κCond q.2) q.1) ∘ Prod.swap)
    refine (measurable_from_prod_countable' (fun a ↦ (κCond a).measurable) ?_).comp measurable_swap
    · intro x y hx hy
      simpa using DFunLike.congr (h_atom _ _ hy) rfl

lemma condKernelCountable_apply (p : α × β) : condKernelCountable κCond h_atom p = κCond p.1 p.2 :=
  rfl

instance condKernelCountable.instIsMarkovKernel [∀ a, IsMarkovKernel (κCond a)] :
    IsMarkovKernel (condKernelCountable κCond h_atom) where
  isProbabilityMeasure p := (‹∀ a, IsMarkovKernel (κCond a)› p.1).isProbabilityMeasure p.2

instance condKernelCountable.instIsCondKernel [∀ a, IsMarkovKernel (κCond a)]
    (κ : Kernel α (β × Ω)) [IsSFiniteKernel κ] [∀ a, (κ a).IsCondKernel (κCond a)] :
    κ.IsCondKernel (condKernelCountable κCond h_atom) := by
  constructor
  ext a s hs
  conv_rhs => rw [← (κ a).disintegrate (κCond a)]
  simp_rw [compProd_apply _ _ _ hs, condKernelCountable_apply, Measure.compProd_apply hs]
  congr

end Countable
end ProbabilityTheory.Kernel
