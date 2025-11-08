/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Adam Topaz, Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Category.TopCat.ULift

/-!
# Topological simplices

We define the natural functor from `SimplexCategory` to `TopCat` sending `⦋n⦌` to the
topological `n`-simplex.
This is used to define `TopCat.toSSet` in `AlgebraicTopology.SingularSet`.
-/

universe u

open CategoryTheory Simplicial

namespace SimplexCategory

attribute [local simp] stdSimplex.map_comp_apply in
/-- The functor `SimplexCategory ⥤ TopCat.{0}`
associating the topological `n`-simplex to `⦋n⦌ : SimplexCategory`. -/
@[simps obj map]
noncomputable def toTop₀ : CosimplicialObject TopCat.{0} where
  obj n := TopCat.of (stdSimplex ℝ (Fin (n.len + 1)))
  map f := TopCat.ofHom ⟨_, stdSimplex.continuous_map f⟩

/-- The functor `SimplexCategory ⥤ TopCat.{u}`
associating the topological `n`-simplex to `⦋n⦌ : SimplexCategory`. -/
@[simps! obj map, pp_with_univ]
noncomputable def toTop : SimplexCategory ⥤ TopCat.{u} :=
  toTop₀ ⋙ TopCat.uliftFunctor

instance (n : SimplexCategory) : Nonempty (toTop₀.obj n) := by dsimp; infer_instance
instance (n : SimplexCategory) : Nonempty (toTop.{u}.obj n) := inferInstanceAs (Nonempty (ULift _))
instance : Unique (toTop₀.obj ⦋0⦌) := inferInstanceAs (Unique (stdSimplex ℝ (Fin 1)))
instance : Unique (toTop.{u}.obj ⦋0⦌) := inferInstanceAs (Unique (ULift _))
instance (n : SimplexCategory) : PathConnectedSpace (toTop₀.obj n) := by dsimp; infer_instance
instance (n : SimplexCategory) : PathConnectedSpace (toTop.{u}.obj n) :=
  ULift.up_surjective.pathConnectedSpace continuous_uliftUp

@[deprecated (since := "2025-08-25")] alias toTopObj := toTop₀
@[deprecated (since := "2025-08-25")] alias toTopObj.ext := stdSimplex.ext
@[deprecated (since := "2025-08-25")] alias toTopObj_zero_apply_zero := stdSimplex.eq_one_of_unique
@[deprecated (since := "2025-08-25")] alias toTopObj_one_add_eq_one := stdSimplex.add_eq_one
@[deprecated (since := "2025-08-25")] alias toTopObj_one_coe_add_coe_eq_one := stdSimplex.add_eq_one
@[deprecated (since := "2025-08-25")] alias toTopObjOneHomeo := stdSimplexHomeomorphUnitInterval
@[deprecated (since := "2025-08-25")] alias toTopMap := toTop₀
@[deprecated (since := "2025-08-25")] alias coe_toTopMap := FunOnFinite.linearMap_apply_apply
@[deprecated (since := "2025-08-25")] alias continuous_toTopMap := stdSimplex.continuous_map

end SimplexCategory
