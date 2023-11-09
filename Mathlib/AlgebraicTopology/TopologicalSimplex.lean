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
This is used to define `TopCat.toSSet` in `AlgebraicTopology.SimplicialSet`.
-/


noncomputable section

namespace SimplexCategory

open Simplicial NNReal BigOperators Classical CategoryTheory

attribute [local instance]
  CategoryTheory.ConcreteCategory.hasCoeToSort CategoryTheory.ConcreteCategory.funLike

-- porting note: added, should be moved
instance (x : SimplexCategory) : Fintype (CategoryTheory.ConcreteCategory.forget.obj x) := by
  change (Fintype (Fin _))
  infer_instance

/-- The topological simplex associated to `x : SimplexCategory`.
  This is the object part of the functor `SimplexCategory.toTop`. -/
def toTopObj (x : SimplexCategory) :=
  { f : x → ℝ≥0 | ∑ i, f i = 1 }
set_option linter.uppercaseLean3 false in
#align simplex_category.to_Top_obj SimplexCategory.toTopObj

instance (x : SimplexCategory) : CoeFun x.toTopObj fun _ => x → ℝ≥0 :=
  ⟨fun f => (f : x → ℝ≥0)⟩

@[ext]
theorem toTopObj.ext {x : SimplexCategory} (f g : x.toTopObj) : (f : x → ℝ≥0) = g → f = g :=
  Subtype.ext
set_option linter.uppercaseLean3 false in
#align simplex_category.to_Top_obj.ext SimplexCategory.toTopObj.ext

/-- A morphism in `SimplexCategory` induces a map on the associated topological spaces. -/
def toTopMap {x y : SimplexCategory} (f : x ⟶ y) : x.toTopObj → y.toTopObj := fun g =>
  ⟨fun i => ∑ j in Finset.univ.filter fun k => f k = i, g j, by
    simp only [Finset.sum_congr, toTopObj, Set.mem_setOf]
    rw [← Finset.sum_biUnion]
    have hg := g.2
    dsimp [toTopObj] at hg
    convert hg
    · simp [Finset.eq_univ_iff_forall]
    · intro i _ j _ h
      rw [Function.onFun, disjoint_iff_inf_le]
      intro e he
      simp only [Finset.bot_eq_empty, Finset.not_mem_empty]
      apply h
      simp only [Finset.mem_univ, forall_true_left,
        ge_iff_le, Finset.le_eq_subset, Finset.inf_eq_inter, Finset.mem_inter,
        Finset.mem_filter, true_and] at he
      rw [← he.1, he.2]⟩
set_option linter.uppercaseLean3 false in
#align simplex_category.to_Top_map SimplexCategory.toTopMap

@[simp]
theorem coe_toTopMap {x y : SimplexCategory} (f : x ⟶ y) (g : x.toTopObj) (i : y) :
    toTopMap f g i = ∑ j in Finset.univ.filter fun k => f k = i, g j :=
  rfl
set_option linter.uppercaseLean3 false in
#align simplex_category.coe_to_Top_map SimplexCategory.coe_toTopMap

@[continuity]
theorem continuous_toTopMap {x y : SimplexCategory} (f : x ⟶ y) : Continuous (toTopMap f) := by
  refine' Continuous.subtype_mk (continuous_pi fun i => _) _
  dsimp only [coe_toTopMap]
  exact continuous_finset_sum _ (fun j _ => (continuous_apply _).comp continuous_subtype_val)
set_option linter.uppercaseLean3 false in
#align simplex_category.continuous_to_Top_map SimplexCategory.continuous_toTopMap

/-- The functor associating the topological `n`-simplex to `[n] : SimplexCategory`. -/
@[simps]
def toTop : SimplexCategory ⥤ TopCat where
  obj x := TopCat.of x.toTopObj
  map f := ⟨toTopMap f, by continuity⟩
  map_id := by
    intro Δ
    ext f
    apply toTopObj.ext
    funext i
    change (Finset.univ.filter fun k => k = i).sum _ = _
    simp [Finset.sum_filter, CategoryTheory.id_apply]
  map_comp := fun f g => by
    ext h
    apply toTopObj.ext
    funext i
    dsimp
    -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
    rw [CategoryTheory.comp_apply]; erw [ContinuousMap.coe_mk,
      ContinuousMap.coe_mk, ContinuousMap.coe_mk]
    simp only [coe_toTopMap]
    erw [← Finset.sum_biUnion]
    · apply Finset.sum_congr
      · exact Finset.ext (fun j => ⟨fun hj => by simpa using hj, fun hj => by simpa using hj⟩)
      · tauto
    · intro j _ k _ h
      rw [Function.onFun, disjoint_iff_inf_le]
      intro e he
      simp only [Finset.bot_eq_empty, Finset.not_mem_empty]
      apply h
      simp only [Finset.mem_univ, forall_true_left,
        ge_iff_le, Finset.le_eq_subset, Finset.inf_eq_inter, Finset.mem_inter,
        Finset.mem_filter, true_and] at he
      rw [← he.1, he.2]
set_option linter.uppercaseLean3 false in
#align simplex_category.to_Top SimplexCategory.toTop

-- These lemmas have always been bad (#7657), but leanprover/lean4#2644 made `simp` start noticing
attribute [nolint simpNF] SimplexCategory.toTop_map_apply

end SimplexCategory
