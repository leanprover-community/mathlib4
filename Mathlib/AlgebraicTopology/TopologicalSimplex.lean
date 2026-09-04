/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Adam Topaz, Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.Geometry.Convex.ConvexSpace.PathConnectedSpaceStdSimplex
public import Mathlib.Topology.Category.TopCat.ULift

/-!
# Topological simplices

We define the natural functor from `SimplexCategory` to `TopCat` sending `⦋n⦌` to the
topological `n`-simplex.
This is used to define `TopCat.toSSet` in `AlgebraicTopology.SingularSet`.
-/

@[expose] public section

universe u

open CategoryTheory Convexity

open scoped Simplicial

namespace SimplexCategory

/-- The functor `SimplexCategory ⥤ TopCat.{0}`
associating the topological `n`-simplex to `⦋n⦌ : SimplexCategory`. -/
@[simps obj map, implicit_reducible]
noncomputable def toTop₀ : CosimplicialObject TopCat.{0} where
  obj n := ↧(StdSimplex ℝ (Fin (n.len + 1)))
  map f := TopCat.ofHom ⟨_, StdSimplex.continuous_map ℝ f⟩
  map_comp f g := by
    ext : 1
    simp [← StdSimplex.map_comp]
    rfl

/-- The functor `SimplexCategory ⥤ TopCat.{u}`
associating the topological `n`-simplex to `⦋n⦌ : SimplexCategory`. -/
@[simps! obj map, pp_with_univ]
noncomputable def toTop : SimplexCategory ⥤ TopCat.{u} :=
  toTop₀ ⋙ TopCat.uliftFunctor

set_option backward.defeqAttrib.useBackward true in
instance (n : SimplexCategory) : Nonempty (toTop₀.obj n) := by dsimp; infer_instance

instance (n : SimplexCategory) : Nonempty (toTop.{u}.obj n) := inferInstanceAs (Nonempty (ULift _))

noncomputable instance : Unique (toTop₀.obj ⦋0⦌) := inferInstanceAs (Unique (StdSimplex ℝ (Fin 1)))

noncomputable instance : Unique (toTop.{u}.obj ⦋0⦌) := inferInstanceAs (Unique (ULift _))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance (n : SimplexCategory) : PathConnectedSpace (toTop₀.obj n) := by dsimp; infer_instance

instance (n : SimplexCategory) : PathConnectedSpace (toTop.{u}.obj n) :=
  ULift.up_surjective.pathConnectedSpace continuous_uliftUp

end SimplexCategory
