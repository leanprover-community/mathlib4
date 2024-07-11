/-
Copyright (c) 2023 Igor Khavkine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Khavkine
-/
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L1Space
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# Uniform tightness

This file contains the definitions for uniform tightness for a family of Lp functions.
It is used as a hypothesis to the version of Vitali's convergence theorem for Lp spaces
that works also for spaces of infinite measure. This version of Vitali's theorem
is also proved later in the file.

## Main definitions

* `MeasureTheory.UnifTight`:
  A sequence of functions `f` is uniformly tight in `L^p` if for all `ε > 0`, there
  exists some measurable set `s` with finite measure such that the Lp-norm of
  `f i` restricted to `sᶜ` is smaller than `ε` for all `i`.

# Main results

* `MeasureTheory.unifTight_finite`: a finite sequence of Lp functions is uniformly
  tight.
* `MeasureTheory.tendsto_Lp_notFinite_of_tendsto_ae`: a sequence of Lp functions which is uniformly
  integrable and uniformly tight converges in Lp if it converge almost everywhere.
* `MeasureTheory.tendstoInMeasure_notFinite_iff_tendsto_Lp`: Vitali convergence theorem:
  a sequence of Lp functions converges in Lp if and only if it is uniformly integrable,
  uniformly tight and converges in measure.

## Tags

uniform integrable, uniformly tight, Vitali convergence theorem
-/


namespace MeasureTheory

open Classical Set Filter Topology MeasureTheory NNReal ENNReal

variable {α β ι : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup β]



section UnifTight

/- This follows closely the `UnifIntegrable` section
from `MeasureTheory.Functions.UniformIntegrable`.-/

variable {f g : ι → α → β} {p : ℝ≥0∞}


/-- Definition of being Uniformly Tight.

A sequence of functions `f` is uniformly tight in `L^p` if for all `ε > 0`, there
exists some measurable set `s` with finite measure such that the Lp-norm of
`f i` restricted to `sᶜ` is smaller than `ε` for all `i`. -/
def UnifTight {_ : MeasurableSpace α} (f : ι → α → β) (p : ℝ≥0∞) (μ : Measure α) : Prop :=
  ∀ ⦃ε : ℝ≥0∞⦄, 0 < ε → ∃ s : Set α, μ s ≠ ∞ ∧ ∀ i, snorm (sᶜ.indicator (f i)) p μ ≤ ε

end UnifTight

-- main results and proofs to be filled in

section VitaliConvergence

variable {μ : Measure α} {p : ℝ≥0∞}

variable {f : ℕ → α → β} {g : α → β}

/-- **Vitali's convergence theorem** (general version).
A sequence of functions `f` converges to `g` in Lp
if and only if it is uniformly integrable, uniformly tight and to `g` in measure. -/
theorem tendstoInMeasure_iff_tendsto_Lp (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hf : ∀ n, Memℒp (f n) p μ) (hg : Memℒp g p μ) :
    TendstoInMeasure μ f atTop g ∧ UnifIntegrable f p μ ∧ UnifTight f p μ
      ↔ Tendsto (fun n => snorm (f n - g) p μ) atTop (𝓝 0) :=
  sorry

end VitaliConvergence
end MeasureTheory
