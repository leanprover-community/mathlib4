/-
Copyright (c) 2025 Bryan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Wang
-/
import Mathlib.Probability.Kernel.Composition.Comp

/-!
# Irreducibility of kernels

A kernel is irreducible if there is a positive probability of reaching any
(positive measure) set of states from any other state within a finite number of steps.

## Main definitions

* `ProbabilityTheory.Kernel.IsIrreducible`:
  irreducibility of a given kernel with respect to a measure `φ`.
* `ProbabilityTheory.Kernel.IsStronglyIrreducible`:
  strong irreducibility of a given kernel with respect to a measure `φ`.

## References

* [C Robert, G Casella, *Monte Carlo Statistical Methods*][robertcasella2004]

-/

open MeasureTheory

open scoped MeasureTheory ENNReal ProbabilityTheory

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

namespace Kernel

/-- `φ`-irreducibility of a kernel `κ` (w.r.t. a measure `φ`). -/
@[mk_iff]
class IsIrreducible (φ : Measure α) (κ : Kernel α α) : Prop where
  irreducible : ∀ ⦃A⦄, MeasurableSet A → φ A > 0 → ∃ (n : ℕ+), ∀ a, κ.pow n a A > 0

/-- Strongly `φ`-irreducibility of a kernel `κ` (w.r.t. a measure `φ`). -/
@[mk_iff]
class IsStronglyIrreducible (φ : Measure α) (κ : Kernel α α) : Prop where
  strongly_irreducible : ∀ ⦃A⦄, MeasurableSet A → φ A > 0 → ∀ a, κ a A > 0

instance {φ : Measure α} {κ : Kernel α α} [IsStronglyIrreducible φ κ] :
    IsIrreducible φ κ :=
  { irreducible := fun _ hs hsp ↦ by
      use 1; simpa using IsStronglyIrreducible.strongly_irreducible hs hsp }

lemma isIrreducible_of_le_measure {φ₁ φ₂ : Measure α} (hφ : φ₁ ≤ φ₂)
    {κ : Kernel α α} [hκ : IsIrreducible φ₂ κ] :
    IsIrreducible φ₁ κ :=
  { irreducible := fun s hs hsp ↦ by
      simpa using hκ.irreducible hs <| Std.lt_of_lt_of_le hsp (hφ s) }

lemma isStronglyIrreducible_of_le_measure {φ₁ φ₂ : Measure α} (hφ : φ₁ ≤ φ₂)
    {κ : Kernel α α} [hκ : IsStronglyIrreducible φ₂ κ] :
    IsStronglyIrreducible φ₁ κ :=
  { strongly_irreducible := fun s hs hsp ↦ by
      simpa using hκ.strongly_irreducible hs <| Std.lt_of_lt_of_le hsp (hφ s) }

end Kernel

end ProbabilityTheory
