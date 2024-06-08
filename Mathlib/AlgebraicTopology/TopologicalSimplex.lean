/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Adam Topaz
-/
import Mathlib.AlgebraicTopology.SimplexCategory
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Instances.NNReal

#align_import algebraic_topology.topological_simplex from "leanprover-community/mathlib"@"6ca1a09bc9aa75824bf97388c9e3b441fc4ccf3f"

/-!
# Topological simplices

We define the natural functor from `SimplexCategory` to `TopCat` sending `[n]` to the
topological `n`-simplex.
This is used to define `TopCat.toSSet` in `AlgebraicTopology.SingularSet`.
-/

set_option linter.uppercaseLean3 false

noncomputable section

namespace SimplexCategory

open Simplicial NNReal Classical CategoryTheory

attribute [local instance] ConcreteCategory.hasCoeToSort ConcreteCategory.instFunLike

-- Porting note: added, should be moved
instance (x : SimplexCategory) : Fintype (ConcreteCategory.forget.obj x) :=
  inferInstanceAs (Fintype (Fin _))

/-- The topological simplex associated to `x : SimplexCategory`.
  This is the object part of the functor `SimplexCategory.toTop`. -/
def toTopObj (x : SimplexCategory) := { f : x → ℝ≥0 | ∑ i, f i = 1 }
#align simplex_category.to_Top_obj SimplexCategory.toTopObj

instance (x : SimplexCategory) : CoeFun x.toTopObj fun _ => x → ℝ≥0 :=
  ⟨fun f => (f : x → ℝ≥0)⟩

@[ext]
theorem toTopObj.ext {x : SimplexCategory} (f g : x.toTopObj) : (f : x → ℝ≥0) = g → f = g :=
  Subtype.ext
#align simplex_category.to_Top_obj.ext SimplexCategory.toTopObj.ext

/-- A morphism in `SimplexCategory` induces a map on the associated topological spaces. -/
def toTopMap {x y : SimplexCategory} (f : x ⟶ y) (g : x.toTopObj) : y.toTopObj :=
  ⟨fun i => ∑ j ∈ Finset.univ.filter (f · = i), g j, by
    simp only [toTopObj, Set.mem_setOf]
    rw [← Finset.sum_biUnion]
    · have hg : ∑ i : (forget SimplexCategory).obj x, g i = 1 := g.2
      convert hg
      simp [Finset.eq_univ_iff_forall]
    · apply Set.pairwiseDisjoint_filter⟩
#align simplex_category.to_Top_map SimplexCategory.toTopMap

@[simp]
theorem coe_toTopMap {x y : SimplexCategory} (f : x ⟶ y) (g : x.toTopObj) (i : y) :
    toTopMap f g i = ∑ j ∈ Finset.univ.filter (f · = i), g j :=
  rfl
#align simplex_category.coe_to_Top_map SimplexCategory.coe_toTopMap

@[continuity]
theorem continuous_toTopMap {x y : SimplexCategory} (f : x ⟶ y) : Continuous (toTopMap f) := by
  refine Continuous.subtype_mk (continuous_pi fun i => ?_) _
  dsimp only [coe_toTopMap]
  exact continuous_finset_sum _ (fun j _ => (continuous_apply _).comp continuous_subtype_val)
#align simplex_category.continuous_to_Top_map SimplexCategory.continuous_toTopMap

/-- The functor associating the topological `n`-simplex to `[n] : SimplexCategory`. -/
@[simps obj map]
def toTop : SimplexCategory ⥤ TopCat where
  obj x := TopCat.of x.toTopObj
  map f := ⟨toTopMap f, by continuity⟩
  map_id := by
    intro Δ
    ext f
    apply toTopObj.ext
    funext i
    change (Finset.univ.filter (· = i)).sum _ = _
    simp [Finset.sum_filter, CategoryTheory.id_apply]
  map_comp := fun f g => by
    ext h
    apply toTopObj.ext
    funext i
    dsimp
    simp only [comp_apply, TopCat.coe_of_of, ContinuousMap.coe_mk, coe_toTopMap]
    rw [← Finset.sum_biUnion]
    · apply Finset.sum_congr
      · exact Finset.ext (fun j => ⟨fun hj => by simpa using hj, fun hj => by simpa using hj⟩)
      · tauto
    · apply Set.pairwiseDisjoint_filter
#align simplex_category.to_Top SimplexCategory.toTop

end SimplexCategory
