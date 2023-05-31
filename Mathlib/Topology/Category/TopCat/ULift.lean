import Mathlib.CategoryTheory.Types
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Constructions

universe u v

namespace TopCat

open CategoryTheory

def uliftFunctor : TopCat.{u} ⥤ TopCatMax.{u, v} where
  obj (X) := ⟨CategoryTheory.uliftFunctor.{v}.obj X.α, ULift.topologicalSpace⟩
  map {X Y} (f) :=
    @ContinuousMap.mk
      (ULift X.α) (ULift Y.α)
      ULift.topologicalSpace
      ULift.topologicalSpace
      (CategoryTheory.uliftFunctor.{v}.map f.toFun)
      (by { dsimp [CategoryTheory.uliftFunctor]; continuity })

end TopCat
