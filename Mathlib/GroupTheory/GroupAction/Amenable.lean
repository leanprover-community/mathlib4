/-
Copyright (c) 2023 Matthias Uschold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Uschold
-/
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Data.Real.ENNReal


/-!
# Amenable Monoid Actions

In this file, we define amenability of a monoid action.
A monoid action is amenable if it admits a invariant mean.
A mean is like a probability measure, demanding
only finite additivity instead of σ-additivity.

## Main Definitions

- `Mean`: defines means as finitely additive probability measures
- `InvariantMean`: defines when a mean is invariant under a monoid action
- `amenable`: A monoid action is amenable if there exists an invariant mean

## Implementation Notes

`Mean` was not implemented using MeasureTheory.ProbabilityMeasure
because meausures are σ-additive (i.e. countably additive). In this
setting, this would be a too strong assumption, we only want to demand
finite additivity. Typically, the resulting measures will not be
σ-additive.

## References

See [bartholdi2017amenability] for definitions
and more information on amenable actions.

-/

universe u v
variable (M : Type u) (α : Type v) [Monoid M] [MulAction M α]


/--A mean is a function from the power set of α to ENNReal that
- assigns the value 1 to the full set α, and
- is finitely additive under disjoint unions -/
structure Mean where
  μ : Set α  → ENNReal
  norm : μ Set.univ = 1
  fin_add : ∀ (X Y : Set α), Disjoint X Y
            → μ (X ∪ Y) = μ X + μ Y

@[coe]
instance : CoeFun (Mean α) (λ _ => Set α → ENNReal) where
  coe := Mean.μ


/--An invariant mean is a mean that is invariant
under translation with the monoid action-/
structure InvariantMean extends Mean α where
  invariance: ∀ (A: Set α), ∀ (g: M),
      μ ((λ (x:α) => g•x) '' A) = μ A


/-- A monoid action is amenable if there exists an invariant mean for it-/
def amenable : Prop :=
  Nonempty (InvariantMean M α)


/-- For amenable actions, we can pick an invariant mean -/
noncomputable def invmean_of_amenable (h: amenable M α) :
    InvariantMean M α :=
  Classical.choice h
