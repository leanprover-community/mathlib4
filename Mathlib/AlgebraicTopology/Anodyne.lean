import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.CategoryTheory.MorphismProperty.WeakSaturation

open CategoryTheory MorphismProperty Limits

namespace SSet

/-- Inductive definition of all horn inclusions Λ[n, i] ⟶ Δ[n], 0 ≤ i ≤ n -/
inductive HornInclusion : {X Y : SSet} → (X ⟶ Y) → Prop
  | mk (n : ℕ) (i : Fin (n + 1)) : HornInclusion (hornInclusion n i)

lemma hornInclusion_hornInclusion (n : ℕ) (i : Fin (n + 1)) : HornInclusion (hornInclusion n i) :=
  HornInclusion.mk n i

/-- The class of horn inclusions as a MorphismProperty -/
def HornInclusions : MorphismProperty SSet := fun _ _ p ↦ HornInclusion p

def Anodyne : MorphismProperty SSet := WeakSaturation HornInclusions

end SSet
