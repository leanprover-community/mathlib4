import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Monomorphisms of simplicial sets

In this file, we show that the class of monomorphisms in `SSet` is stable
under coproducts, pushouts, filtered colimits and transfinite compositions.

-/

@[expose] public section

universe v' u' u

open CategoryTheory Limits MorphismProperty

namespace SSet

instance [HasCoproducts.{v'} (Type u)] :
    IsStableUnderCoproducts.{v'} (monomorphisms SSet.{u}) :=
  inferInstanceAs (IsStableUnderCoproducts.{v'} (monomorphisms (_ ⥤ _)))

instance : (monomorphisms SSet).IsStableUnderCobaseChange := by
  change (monomorphisms (_ ⥤ _)).IsStableUnderCobaseChange
  rw [← functorCategory_monomorphisms]
  infer_instance

instance : MorphismProperty.IsStableUnderFilteredColimits.{u, u} (monomorphisms SSet.{u}) where
  isStableUnderColimitsOfShape J _ _ := by
    change (monomorphisms (_ ⥤ _)).IsStableUnderColimitsOfShape J
    rw [← functorCategory_monomorphisms]
    infer_instance

example (K : Type u) [LinearOrder K] [SuccOrder K] [OrderBot K] [WellFoundedLT K] :
    (monomorphisms SSet.{u}).IsStableUnderTransfiniteCompositionOfShape K := by
  infer_instance

end SSet
