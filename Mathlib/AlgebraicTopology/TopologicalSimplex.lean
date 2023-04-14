/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Adam Topaz

! This file was ported from Lean 3 source module algebraic_topology.topological_simplex
! leanprover-community/mathlib commit 6ca1a09bc9aa75824bf97388c9e3b441fc4ccf3f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicTopology.SimplexCategory
import Mathbin.Topology.Category.Top.Basic
import Mathbin.Topology.Instances.Nnreal

/-!
# Topological simplices

We define the natural functor from `simplex_category` to `Top` sending `[n]` to the
topological `n`-simplex.
This is used to define `Top.to_sSet` in `algebraic_topology.simpliciaL_set`.
-/


noncomputable section

namespace SimplexCategory

open Simplicial NNReal BigOperators Classical

attribute [local instance]
  CategoryTheory.ConcreteCategory.hasCoeToSort CategoryTheory.ConcreteCategory.hasCoeToFun

/-- The topological simplex associated to `x : simplex_category`.
  This is the object part of the functor `simplex_category.to_Top`. -/
def toTopObj (x : SimplexCategory) :=
  { f : x → ℝ≥0 | (∑ i, f i) = 1 }
#align simplex_category.to_Top_obj SimplexCategory.toTopObj

instance (x : SimplexCategory) : CoeFun x.toTopObj fun _ => x → ℝ≥0 :=
  ⟨fun f => (f : x → ℝ≥0)⟩

@[ext]
theorem toTopObj.ext {x : SimplexCategory} (f g : x.toTopObj) : (f : x → ℝ≥0) = g → f = g :=
  Subtype.ext
#align simplex_category.to_Top_obj.ext SimplexCategory.toTopObj.ext

/-- A morphism in `simplex_category` induces a map on the associated topological spaces. -/
def toTopMap {x y : SimplexCategory} (f : x ⟶ y) : x.toTopObj → y.toTopObj := fun g =>
  ⟨fun i => ∑ j in Finset.univ.filterₓ fun k => f k = i, g j,
    by
    simp only [[anonymous], Finset.sum_congr, to_Top_obj, Set.mem_setOf]
    rw [← Finset.sum_bunionᵢ]
    convert g.2
    · rw [Finset.eq_univ_iff_forall]
      intro i
      rw [Finset.mem_bunionᵢ]
      exact ⟨f i, by simp, by simp⟩
    · intro i hi j hj h
      rw [Function.onFun, disjoint_iff_inf_le]
      intro e he
      apply h
      simp only [true_and_iff, Finset.inf_eq_inter, Finset.mem_univ, Finset.mem_filter,
        Finset.mem_inter] at he
      rw [← he.1, ← he.2]⟩
#align simplex_category.to_Top_map SimplexCategory.toTopMap

@[simp]
theorem coe_toTopMap {x y : SimplexCategory} (f : x ⟶ y) (g : x.toTopObj) (i : y) :
    toTopMap f g i = ∑ j in Finset.univ.filterₓ fun k => f k = i, g j :=
  rfl
#align simplex_category.coe_to_Top_map SimplexCategory.coe_toTopMap

@[continuity]
theorem continuous_toTopMap {x y : SimplexCategory} (f : x ⟶ y) : Continuous (toTopMap f) :=
  Continuous.subtype_mk
    (continuous_pi fun i =>
      continuous_finset_sum _ fun j hj => (continuous_apply _).comp continuous_subtype_val)
    _
#align simplex_category.continuous_to_Top_map SimplexCategory.continuous_toTopMap

/-- The functor associating the topological `n`-simplex to `[n] : simplex_category`. -/
@[simps]
def toTop : SimplexCategory ⥤ TopCat
    where
  obj x := TopCat.of x.toTopObj
  map x y f := ⟨toTopMap f⟩
  map_id' := by
    intro x
    ext (f i) : 3
    change (finset.univ.filter fun k => k = i).Sum _ = _
    simp [Finset.sum_filter]
  map_comp' := by
    intro x y z f g
    ext (h i) : 3
    dsimp
    erw [← Finset.sum_bunionᵢ]
    apply Finset.sum_congr
    · exact Finset.ext fun j => ⟨fun hj => by simpa using hj, fun hj => by simpa using hj⟩
    · tauto
    · intro j hj k hk h
      rw [Function.onFun, disjoint_iff_inf_le]
      intro e he
      apply h
      simp only [true_and_iff, Finset.inf_eq_inter, Finset.mem_univ, Finset.mem_filter,
        Finset.mem_inter] at he
      rw [← he.1, ← he.2]
#align simplex_category.to_Top SimplexCategory.toTop

end SimplexCategory

