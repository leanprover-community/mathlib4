/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Adam Topaz, Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Topology.Category.TopCat.ULift
public import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# Topological simplices

We define the natural functor from `SimplexCategory` to `TopCat` sending `⦋n⦌` to the
topological `n`-simplex.
This is used to define `TopCat.toSSet` in `AlgebraicTopology.SingularSet`.
-/

@[expose] public section

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

set_option backward.isDefEq.respectTransparency false in
instance (n : SimplexCategory) : PathConnectedSpace (toTop₀.obj n) := by dsimp; infer_instance

instance (n : SimplexCategory) : PathConnectedSpace (toTop.{u}.obj n) :=
  ULift.up_surjective.pathConnectedSpace continuous_uliftUp

end SimplexCategory
