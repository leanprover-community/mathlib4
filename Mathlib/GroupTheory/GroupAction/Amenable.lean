/-
Copyright (c) 2023 Matthias Uschold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Uschold
-/
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Data.Real.ENNReal
import Mathlib.MeasureTheory.MeasurableSpace.Defs


/-!
# Amenable Monoid Actions

In this file, we define amenability of a monoid action.
A monoid action is amenable if it admits an invariant mean.
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
variable (α : Type v) [MeasurableSpace α]

/--A mean is a function from the power set of α to ENNReal that
- assigns the value 1 to the full set α, and
- is finitely additive under disjoint unions -/
structure Mean where
  /-- function giving the measure of a measurable subset-/
  measureOf : {S // MeasurableSet (α := α) S} → NNReal
  /-- μ should be normalised  -/
  measureOf_univ : μ Set.univ = 1
  /-- μ has to be finitely additive -/
  fin_add : ∀ (X Y : Set α),
      (hX : MeasurableSet X) → (hY: MeasurableSet Y) → Disjoint X Y
      → μ (⟨X ∪ Y, MeasurableSet.union hX hY⟩) = μ ⟨X, hX⟩ + μ ⟨Y, hY⟩

@[coe]
instance : CoeFun (Mean α) (λ _ => {S // MeasurableSet (α := α) S} → NNReal) where
  coe := Mean.μ


variable (G : Type u) [Monoid G] [MulAction G α]
  [MulActionMeasurable : Fact (∀ (g : G), Measurable (λ (x : α) => g • x))]

instance MeanSMul : SMul G (Mean α) where
  smul g μ := {
    μ := λ S => μ ⟨(λ (x : α) => g • x)⁻¹' S, (MulActionMeasurable.out g S.property)⟩
    norm := by simp only [Set.preimage_univ, μ.norm]
    fin_add := by
      intro X Y hX hY disjXY
      simp only [Set.preimage_union]
      apply μ.fin_add ((λ (x:α) => g•x)⁻¹' X) ((λ (x:α) => g•x)⁻¹' Y) _ _ _
      apply Disjoint.preimage
      exact disjXY
  }

/--An invariant mean is a mean that is invariant
under translation with the monoid action-/
structure InvariantMean extends Mean α where
  /-- invariance of the mean -/
  invariance: ∀ (g: G), g • toMean = toMean


/-- A monoid action is amenable if there exists an invariant mean for it-/
def amenable : Prop :=
  Nonempty (InvariantMean α G)


/-- For amenable actions, we can pick an invariant mean -/
noncomputable def invmean_of_amenable (h: amenable α G) :
    InvariantMean α G :=
  Classical.choice h
