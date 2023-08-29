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
  -- ⊢ Fintype (Fin (len x + 1))
  infer_instance
  -- 🎉 no goals

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
    -- ⊢ ∑ i : (forget SimplexCategory).obj y, ∑ x_1 in Finset.filter (fun k => ↑f k  …
    rw [← Finset.sum_biUnion]
    -- ⊢ ∑ x_1 in Finset.biUnion Finset.univ fun i => Finset.filter (fun k => ↑f k =  …
    have hg := g.2
    -- ⊢ ∑ x_1 in Finset.biUnion Finset.univ fun i => Finset.filter (fun k => ↑f k =  …
    dsimp [toTopObj] at hg
    -- ⊢ ∑ x_1 in Finset.biUnion Finset.univ fun i => Finset.filter (fun k => ↑f k =  …
    convert hg
    -- ⊢ (Finset.biUnion Finset.univ fun i => Finset.filter (fun k => ↑f k = i) Finse …
    · simp [Finset.eq_univ_iff_forall]
      -- 🎉 no goals
    · intro i _ j _ h
      -- ⊢ (Disjoint on fun i => Finset.filter (fun k => ↑f k = i) Finset.univ) i j
      rw [Function.onFun, disjoint_iff_inf_le]
      -- ⊢ Finset.filter (fun k => ↑f k = i) Finset.univ ⊓ Finset.filter (fun k => ↑f k …
      intro e he
      -- ⊢ e ∈ ⊥
      simp only [Finset.bot_eq_empty, Finset.not_mem_empty]
      -- ⊢ False
      apply h
      -- ⊢ i = j
      simp only [Finset.mem_univ, forall_true_left,
        ge_iff_le, Finset.le_eq_subset, Finset.inf_eq_inter, Finset.mem_inter,
        Finset.mem_filter, true_and] at he
      rw [← he.1, he.2]⟩
      -- 🎉 no goals
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
  -- ⊢ Continuous fun a => ∑ j in Finset.filter (fun k => ↑f k = i) Finset.univ, ↑a j
  dsimp only [coe_toTopMap]
  -- ⊢ Continuous fun a => ∑ j in Finset.filter (fun k => ↑f k = i) Finset.univ, ↑a j
  exact continuous_finset_sum _ (fun j _ => (continuous_apply _).comp continuous_subtype_val)
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align simplex_category.continuous_to_Top_map SimplexCategory.continuous_toTopMap

/-- The functor associating the topological `n`-simplex to `[n] : SimplexCategory`. -/
@[simps]
def toTop : SimplexCategory ⥤ TopCat where
  obj x := TopCat.of x.toTopObj
  map f := ⟨toTopMap f, by continuity⟩
                           -- 🎉 no goals
  map_id := by
    intro Δ
    -- ⊢ { obj := fun x => TopCat.of ↑(toTopObj x), map := fun {X Y} f => ContinuousM …
    ext f
    -- ⊢ ↑({ obj := fun x => TopCat.of ↑(toTopObj x), map := fun {X Y} f => Continuou …
    apply toTopObj.ext
    -- ⊢ ↑(↑({ obj := fun x => TopCat.of ↑(toTopObj x), map := fun {X Y} f => Continu …
    funext i
    -- ⊢ ↑(↑({ obj := fun x => TopCat.of ↑(toTopObj x), map := fun {X Y} f => Continu …
    change (Finset.univ.filter fun k => k = i).sum _ = _
    -- ⊢ ∑ j in Finset.filter (fun k => k = i) Finset.univ, ↑f j = ↑(↑(𝟙 ({ obj := fu …
    simp [Finset.sum_filter, CategoryTheory.id_apply]
    -- 🎉 no goals
  map_comp := fun f g => by
    ext h
    -- ⊢ ↑({ obj := fun x => TopCat.of ↑(toTopObj x), map := fun {X Y} f => Continuou …
    apply toTopObj.ext
    -- ⊢ ↑(↑({ obj := fun x => TopCat.of ↑(toTopObj x), map := fun {X Y} f => Continu …
    funext i
    -- ⊢ ↑(↑({ obj := fun x => TopCat.of ↑(toTopObj x), map := fun {X Y} f => Continu …
    dsimp
    -- ⊢ ↑(↑(ContinuousMap.mk (toTopMap (Hom.mk (OrderHom.comp (Hom.toOrderHom g) (Ho …
    rw [CategoryTheory.comp_apply, ContinuousMap.coe_mk, ContinuousMap.coe_mk, ContinuousMap.coe_mk]
    -- ⊢ ↑(toTopMap (Hom.mk (OrderHom.comp (Hom.toOrderHom g) (Hom.toOrderHom f))) h) …
    simp only [coe_toTopMap]
    -- ⊢ ∑ j in Finset.filter (fun k => ↑(Hom.mk (OrderHom.comp (Hom.toOrderHom g) (H …
    erw [← Finset.sum_biUnion]
    -- ⊢ ∑ j in Finset.filter (fun k => ↑(Hom.mk (OrderHom.comp (Hom.toOrderHom g) (H …
    · apply Finset.sum_congr
      -- ⊢ Finset.filter (fun k => ↑(Hom.mk (OrderHom.comp (Hom.toOrderHom g) (Hom.toOr …
      · exact Finset.ext (fun j => ⟨fun hj => by simpa using hj, fun hj => by simpa using hj⟩)
        -- 🎉 no goals
      · tauto
        -- 🎉 no goals
    · intro j _ k _ h
      -- ⊢ (Disjoint on fun x => Finset.filter (fun k => ↑f k = x) Finset.univ) j k
      rw [Function.onFun, disjoint_iff_inf_le]
      -- ⊢ Finset.filter (fun k => ↑f k = j) Finset.univ ⊓ Finset.filter (fun k_1 => ↑f …
      intro e he
      -- ⊢ e ∈ ⊥
      simp only [Finset.bot_eq_empty, Finset.not_mem_empty]
      -- ⊢ False
      apply h
      -- ⊢ j = k
      simp only [Finset.mem_univ, forall_true_left,
        ge_iff_le, Finset.le_eq_subset, Finset.inf_eq_inter, Finset.mem_inter,
        Finset.mem_filter, true_and] at he
      rw [← he.1, he.2]
      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align simplex_category.to_Top SimplexCategory.toTop

end SimplexCategory
