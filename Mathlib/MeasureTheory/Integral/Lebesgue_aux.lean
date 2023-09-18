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
set_option autoImplicit true

-- move these
alias ⟨_, ENNReal.monotone2⟩ := ENNReal.coe_le_coe
attribute [gcongr] ENNReal.monotone2

namespace MeasureTheory

-- workaround for the known eta-reduction issue with `@[gcongr]`
@[gcongr] theorem lintegral_mono2 ⦃f g : α → ℝ≥0∞⦄ (hfg : ∀ x, f x ≤ g x) :
    lintegral μ f ≤ lintegral μ g :=
lintegral_mono hfg

@[gcongr] theorem lintegral_mono3 ⦃f g : α → ℝ≥0∞⦄ (hfg : ∀ x, f x ≤ g x) (h2 : μ ≤ ν) :
    lintegral μ f ≤ lintegral ν g :=
lintegral_mono' h2 hfg

-- @[gcongr] theorem lintegral_congr2 ⦃f g : α → ℝ≥0∞⦄ (hfg : ∀ x, f x = g x) :
--     lintegral μ f = lintegral μ g :=
-- lintegral_congr hfg

theorem lintegral_of_isEmpty {α} [MeasurableSpace α] [IsEmpty α] (μ : Measure α) (f : α → ℝ≥0∞) :
    ∫⁻ x, f x ∂μ = 0 := by convert lintegral_zero_measure f
