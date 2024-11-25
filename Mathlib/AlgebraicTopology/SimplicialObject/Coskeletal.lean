/-
Copyright (c) 2024 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl, Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Basic

/-!
# Coskeletal simplicial objects
The identity natural transformation exhibits a simplicial object `X` as a right extension of its
restriction along `(Truncated.inclusion (n := n)).op` recorded by `rightExtensionInclusion X n`.

The simplicial object `X` is *n-coskeletal* if `(rightExtensionInclusion X n)` is a right Kan
extension.
-/

open Opposite

open CategoryTheory

open CategoryTheory.Limits CategoryTheory.Functor SimplexCategory

universe v u v' u'

namespace CategoryTheory

namespace SimplicialObject
variable {C : Type u} [Category.{v} C]
variable (X : SimplicialObject C) (n : ℕ)

class IsCoskeletal : Prop where
  nonempty_isRightKanExtension :
    Nonempty (IsRightKanExtension X (𝟙 (Truncated.inclusion (n := n).op ⋙ X)))


namespace Truncated

/-- The identity natural transformation exhibits a simplicial set as a right extension of its
restriction along `(Truncated.inclusion (n := n)).op`.-/
@[simps!]
def rightExtensionInclusion :
    RightExtension (Truncated.inclusion (n := n)).op
      (Functor.op Truncated.inclusion ⋙ X) := RightExtension.mk _ (𝟙 _)

end Truncated


end SimplicialObject

end CategoryTheory
