/-
Copyright (c) 2025 Bryan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Wang
-/
import Mathlib.Probability.Kernel.Composition.Comp

/-!
# Irreducibility of kernels

## Main definitions

* `ProbabilityTheory.Kernel.IsIrreducible`:
  irreducibility of a given kernel with respect to a measure `φ`.

## References

* [C Robert, G Casella, *Monte Carlo Statistical Methods*][robertcasella2004]

-/

open MeasureTheory

open scoped MeasureTheory ENNReal ProbabilityTheory

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

namespace Kernel

/-- `φ`-irreducibility of a kernel `κ` (w.r.t. a measure `φ`). -/
def IsIrreducible (φ : Measure α) (κ : Kernel α α) : Prop :=
  ∀ ⦃A⦄, MeasurableSet A → φ A > 0 →
    ∃ (n : ℕ+), ∀ a, κ.pow n a A > 0

/-- Strongly `φ`-irreducibility of a kernel `κ` (w.r.t. a measure `φ`). -/
def IsStronglyIrreducible (φ : Measure α) (κ : Kernel α α) : Prop :=
  ∀ ⦃A⦄, MeasurableSet A → φ A > 0 →
    ∀ a, κ a A > 0

end Kernel

end ProbabilityTheory
