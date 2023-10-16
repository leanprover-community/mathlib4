/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
import Mathlib.MeasureTheory.Integral.Lebesgue

/-!
A supplement to the file `DMeasureTheory.Integral.Lebesgue`, doing some missing setup for the tactic
`gcongr`.
-/

open scoped ENNReal
open MeasureTheory Measure
set_option autoImplicit true

-- move these
alias ⟨_, ENNReal.coe_monotone⟩ := ENNReal.coe_le_coe
attribute [gcongr] ENNReal.coe_monotone

namespace MeasureTheory

-- workaround for the known eta-reduction issue with `@[gcongr]`
@[gcongr] theorem lintegral_mono_fn ⦃f g : α → ℝ≥0∞⦄ (hfg : ∀ x, f x ≤ g x) :
    lintegral μ f ≤ lintegral μ g :=
lintegral_mono hfg

-- workaround for the known eta-reduction issue with `@[gcongr]`
@[gcongr] theorem lintegral_mono_fn_measure ⦃f g : α → ℝ≥0∞⦄ (hfg : ∀ x, f x ≤ g x) (h2 : μ ≤ ν) :
    lintegral μ f ≤ lintegral ν g :=
lintegral_mono' h2 hfg

theorem lintegral_of_isEmpty {α} [MeasurableSpace α] [IsEmpty α] (μ : Measure α) (f : α → ℝ≥0∞) :
    ∫⁻ x, f x ∂μ = 0 := by convert lintegral_zero_measure f

protected theorem MeasurePreserving.lintegral_map_equiv {α β}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    (f : β → ℝ≥0∞) (g : α ≃ᵐ β) (hg : MeasurePreserving g μ ν) :
    ∫⁻ a, f a ∂ν = ∫⁻ a, f (g a) ∂μ := by rw [← MeasureTheory.lintegral_map_equiv f g, hg.map_eq]
