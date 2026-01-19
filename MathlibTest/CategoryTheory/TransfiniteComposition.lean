import Mathlib.CategoryTheory.Types.Monomorphisms
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition

universe v u

namespace CategoryTheory.Types

open MorphismProperty

example : MorphismProperty.IsStableUnderTransfiniteComposition.{v}
    (monomorphisms (Type u)) := inferInstance

end CategoryTheory.Types
