module

public import Mathlib.CategoryTheory.Types.Monomorphisms
public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition

@[expose] public section

universe v u

namespace CategoryTheory.Types

open MorphismProperty

example : MorphismProperty.IsStableUnderTransfiniteComposition.{v}
    (monomorphisms (Type u)) := inferInstance

end CategoryTheory.Types
