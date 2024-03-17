import Mathlib.AlgebraicTopology.AnodyneExtensions
import Mathlib.AlgebraicTopology.SimplicialSet

universe u

open CategoryTheory

namespace SSet

/-open MorphismProperty in
instance : (monomorphisms SSet.{u}).IsGabrielZismanSaturated where
  subset_mono := by rfl
  iso_subset _ _ f (f : IsIso f) := monomorphisms.infer_property _
  stableUnderCobaseChange := sorry
  isStableUnderRetract := IsStableUnderRetract.monomorphisms _
  isStableUnderCoproducts := sorry
  isStableUnderInfiniteComposition := sorry

inductive B₁ : MorphismProperty SSet.{u}
  | hornInclusion (n : ℕ) (i : Fin (n + 1)) : B₁ (hornInclusion n i)-/

end SSet
