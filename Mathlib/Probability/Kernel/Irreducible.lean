/-
Copyright (c) 2025 Bryan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Wang
-/
module

public import Mathlib.Probability.Kernel.Composition.Comp

/-!
# Irreducibility of kernels

A kernel `κ : Kernel α α` is `φ`-irreducible, for a given measure `φ` on `α`,
if for every measurable set `A` with positive measure under `φ`, and for every `a : α`,
there exists a positive integer `n` such that we have `(κ ^ n) a A > 0`.

When the kernel `κ` is the transition kernel of a Markov chain,
this precisely means that the Markov chain is `φ`-irreducible,
that is, there is a positive probability of reaching any
(`φ`-positive measure) set of states from any other state within a finite number of steps.

## Main definitions

* `ProbabilityTheory.Kernel.IsIrreducible`:
  irreducibility of a given kernel with respect to a measure `φ`.

## Main statements

* `isIrreducible_of_le_measure`: If a kernel `κ` is irreducible with respect to a measure `φ₂`,
  then it is also irreducible with respect to any measure `φ₁` with `φ₁ ≤ φ₂`.

## References

* [Meyn, S.P. and Tweedie, R.L., *Markov Chains and Stochastic Stability*][meyntweedie1993]
* [C Robert, G Casella, *Monte Carlo Statistical Methods*][robertcasella2004]

-/

@[expose] public section

open MeasureTheory

open scoped MeasureTheory ENNReal ProbabilityTheory

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

namespace Kernel

/-- A kernel `κ : Kernel α α` is `φ`-irreducible (w.r.t. a given measure `φ` on `α`),
if for every measurable set `A` with positive measure under `φ`,
and for every `a : α`, there exists an integer `n` such that `(κ ^ n) a A > 0`.
Ref. *Meyn-Tweedie* Proposition 4.2.1(ii), page 89 -/
@[mk_iff]
class IsIrreducible (φ : Measure α) (κ : Kernel α α) : Prop where
  irreducible ⦃A⦄ (hA : MeasurableSet A) (hφA : φ A > 0) a :
    ∃ (n : ℕ), (κ ^ n) a A > 0

instance {φ : Measure α} [Subsingleton α] :
    IsIrreducible φ Kernel.id where
  irreducible s hs hsp a := by
    use 1;
    have ha : a ∈ s :=
      Subsingleton.mem_iff_nonempty.mpr
        <| MeasureTheory.nonempty_of_measure_ne_zero (μ := φ) (ne_of_lt hsp).symm
    simp [id_apply, ha]

instance {c : ℝ≥0∞} {φ : Measure α} {κ : Kernel α α} [hκ : IsIrreducible φ κ] :
    IsIrreducible (c • φ) κ where
  irreducible s hs hsp := by
    simpa using hκ.irreducible hs <| by simp_all

lemma isIrreducible_of_le_measure {φ₁ φ₂ : Measure α} (hφ : φ₁ ≤ φ₂)
    {κ : Kernel α α} [hκ : IsIrreducible φ₂ κ] :
    IsIrreducible φ₁ κ where
  irreducible s hs hsp := by
    simpa using hκ.irreducible hs <| Std.lt_of_lt_of_le hsp (hφ s)

end Kernel

end ProbabilityTheory
