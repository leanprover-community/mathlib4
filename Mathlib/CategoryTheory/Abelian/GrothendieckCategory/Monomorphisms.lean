
/-!
# Monomorphisms in Grothendieck abelian categories

In this file, we show that in a Grothendieck abelian category,
monomorphisms are stable under transfinite composition.

-/

@[expose] public section

universe w v u

namespace CategoryTheory

namespace IsGrothendieckAbelian

open MorphismProperty

instance {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C] :
    IsStableUnderTransfiniteComposition.{w} (monomorphisms C) := by
  infer_instance

end IsGrothendieckAbelian

end CategoryTheory
