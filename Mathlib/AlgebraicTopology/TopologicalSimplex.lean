/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Adam Topaz
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Connected.PathConnected

/-!
# Topological simplices

We define the natural functor from `SimplexCategory` to `TopCat` sending `⦋n⦌` to the
topological `n`-simplex.
This is used to define `TopCat.toSSet` in `AlgebraicTopology.SingularSet`.
-/


noncomputable section

namespace SimplexCategory

open Simplicial NNReal CategoryTheory

/-- The topological simplex associated to `x : SimplexCategory`.
  This is the object part of the functor `SimplexCategory.toTop`. -/
def toTopObj (x : SimplexCategory) := { f : ToType x → ℝ≥0 | ∑ i, f i = 1 }

instance (x : SimplexCategory) : CoeFun x.toTopObj fun _ => ToType x → ℝ≥0 :=
  ⟨fun f => (f : ToType x → ℝ≥0)⟩

@[ext]
theorem toTopObj.ext {x : SimplexCategory} (f g : x.toTopObj) : (f : ToType x → ℝ≥0) = g → f = g :=
  Subtype.ext

@[simp]
lemma toTopObj_zero_apply_zero (f : ⦋0⦌.toTopObj) : f 0 = 1 := by
  simpa [toType_apply] using show ∑ _, _ = _ from f.2

lemma toTopObj_one_add_eq_one (f : ⦋1⦌.toTopObj) : f 0 + f 1 = 1 := by
  simpa [toType_apply, Finset.sum] using show ∑ _, _ = _ from f.2

lemma toTopObj_one_coe_add_coe_eq_one (f : ⦋1⦌.toTopObj) : (f 0 : ℝ) + f 1 = 1 := by
  norm_cast
  rw [toTopObj_one_add_eq_one]

instance (x : SimplexCategory) : Nonempty x.toTopObj :=
  ⟨⟨Pi.single 0 1, (show ∑ _, _ = _ by simp)⟩⟩

instance : Unique ⦋0⦌.toTopObj :=
  ⟨⟨1, show ∑ _, _ = _ by simp [toType_apply]⟩, fun f ↦ by ext i; fin_cases i; simp⟩

open unitInterval in
/-- The one-dimensional topological simplex is homeomorphic to the unit interval. -/
def toTopObjOneHomeo : ⦋1⦌.toTopObj ≃ₜ I where
  toFun f := ⟨f 0, (f 0).2, toTopObj_one_coe_add_coe_eq_one f ▸ le_add_of_nonneg_right (f 1).2⟩
  invFun x := ⟨![toNNReal x, toNNReal (σ x)],
    show ∑ _, _ = _ by ext; simp [toType_apply, Finset.sum]⟩
  left_inv f := by ext i; fin_cases i <;> simp [← toTopObj_one_coe_add_coe_eq_one f]
  right_inv x := by simp
  continuous_toFun := .subtype_mk (continuous_subtype_val.comp
    ((continuous_apply _).comp continuous_subtype_val)) _
  continuous_invFun := .subtype_mk (continuous_pi fun i ↦ by fin_cases i <;> dsimp <;> fun_prop) _

open unitInterval in
instance (x : SimplexCategory) : PathConnectedSpace x.toTopObj := by
  refine ⟨inferInstance, ?_⟩
  intros f g
  dsimp [toTopObj, toType_apply] at f g ⊢
  refine ⟨⟨fun j ↦ ⟨toNNReal (symm j) • f.1 + toNNReal j • g.1, ?_⟩, ?_⟩, ?_, ?_⟩
  · ext; simp [Finset.sum_add_distrib, ← Finset.mul_sum, f.2, g.2]
  · fun_prop
  · ext; simp
  · ext; simp

open Classical in
/-- A morphism in `SimplexCategory` induces a map on the associated topological spaces. -/
def toTopMap {x y : SimplexCategory} (f : x ⟶ y) (g : x.toTopObj) : y.toTopObj :=
  ⟨fun i => ∑ j ∈ Finset.univ.filter (f · = i), g j, by
    simp only [toTopObj, Set.mem_setOf]
    rw [← Finset.sum_biUnion]
    · have hg : ∑ i : ToType x, g i = 1 := g.2
      convert hg
      simp [Finset.eq_univ_iff_forall]
    · convert Set.pairwiseDisjoint_filter _ _ _⟩

open Classical in
@[simp]
theorem coe_toTopMap {x y : SimplexCategory} (f : x ⟶ y) (g : x.toTopObj) (i : ToType y) :
    toTopMap f g i = ∑ j ∈ Finset.univ.filter (f · = i), g j :=
  rfl

@[continuity, fun_prop]
theorem continuous_toTopMap {x y : SimplexCategory} (f : x ⟶ y) : Continuous (toTopMap f) := by
  refine Continuous.subtype_mk (continuous_pi fun i => ?_) _
  dsimp only [coe_toTopMap]
  exact continuous_finset_sum _ (fun j _ => (continuous_apply _).comp continuous_subtype_val)

/-- The functor associating the topological `n`-simplex to `⦋n⦌ : SimplexCategory`. -/
@[simps obj map]
def toTop : SimplexCategory ⥤ TopCat where
  obj x := TopCat.of x.toTopObj
  map f := TopCat.ofHom ⟨toTopMap f, by fun_prop⟩
  map_id := by
    classical
    intro Δ
    ext f
    simp [Finset.sum_filter]
  map_comp := fun f g => by
    classical
    ext h : 3
    dsimp
    rw [← Finset.sum_biUnion]
    · apply Finset.sum_congr
      · exact Finset.ext (fun j => ⟨fun hj => by simpa using hj, fun hj => by simpa using hj⟩)
      · tauto
    · apply Set.pairwiseDisjoint_filter

end SimplexCategory
