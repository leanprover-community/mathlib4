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
  μ : {S // MeasurableSet (α:=α) S} → NNReal
  /-- μ should be normalised  -/
  norm : μ ⟨Set.univ, MeasurableSet.univ⟩ = 1
  /-- μ has to be finitely additive -/
  fin_add : ∀ (X Y : Set α),
      (hX: MeasurableSet X) → (hY: MeasurableSet Y) → Disjoint X Y
      → μ (⟨X ∪ Y, MeasurableSet.union hX hY⟩) = μ ⟨X, hX⟩ + μ ⟨Y, hY⟩

@[coe]
instance : CoeFun (Mean α) (λ _ => {S // MeasurableSet (α:=α) S} → NNReal) where
  coe := Mean.μ


variable (G : Type u) [Group G] [MulAction G α] (MulActionMeasurable: ∀ (g: G), Measurable (λ (x:α) => g•x))


instance : SMul G (Mean α) := SMul.mk (λ g μ =>
    Mean.mk (λ S => μ ⟨(λ (x:α) => g•x)⁻¹' S, MulActionMeasurable g S⟩)
    (by simp only [Set.preimage_univ, μ.norm])
    (by
      intro X Y hX hY disjXY
      simp only [Set.preimage_union]
      apply μ.fin_add ((λ (x:α) => g•x)⁻¹' X) ((λ (x:α) => g•x)⁻¹' Y) _ _ _
      apply Disjoint.preimage
      exact disjXY
    )
    )

--instance : MulAction G (Mean α) :=
 --   MulAction.mk


/--An invariant mean is a mean that is invariant
under translation with the monoid action-/
structure InvariantMean extends Mean α where
  /-- invariance of the mean -/
  invariance: ∀ (A: Set α), (hA: MeasurableSet A) →
      ∀ (g: G), μ ((λ (x:α) => g•x) '' A) = μ ⟨A, hA⟩


/-- A monoid action is amenable if there exists an invariant mean for it-/
def amenable : Prop :=
  Nonempty (InvariantMean G α)


/-- For amenable actions, we can pick an invariant mean -/
noncomputable def invmean_of_amenable (h: amenable G α) :
    InvariantMean G α :=
  Classical.choice h
