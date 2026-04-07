/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Adam Topaz, Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Topology.Category.TopCat.ULift

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
@[simps! -isSimp obj map, pp_with_univ]
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

lemma _root_.stdSimplex.map_δ_apply {n : ℕ} (i : Fin (n + 2)) (j : Fin (⦋n + 1⦌.len + 1))
    (σ : stdSimplex ℝ (Fin (⦋n⦌.len + 1))) :
    stdSimplex.map (SimplexCategory.δ i) σ j =
      (if i < j then σ ⟨j - 1, by simp_all; lia⟩ else 0) +
      (if h : i > j then σ ⟨j, by simp_all; lia⟩ else 0) := by
  simp only [_root_.SimplexCategory.len_mk, stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply,
    SimplexCategory.δ_apply, Fin.succAbove_eq_iff]
  obtain hij | rfl | hij := lt_trichotomy i j
  · rw [Finset.sum_eq_single ⟨j - 1, by lia⟩]
    all_goals simp; grind
  · rw [Finset.sum_eq_zero]
    all_goals simp <;> grind
  · rw [Finset.sum_eq_single ⟨j, by lia⟩]
    all_goals simp; grind

lemma toTop_map_δ_apply {n : ℕ} (i : Fin (n + 2)) (j : Fin (⦋n + 1⦌.len + 1))
    (σ : toTop.{u} ^⦋n⦌) :
    (toTop.map (SimplexCategory.δ i) σ).down.1 j =
      (if i < j then σ.down.1 ⟨j - 1, by simpa using j.2⟩ else 0) +
      (if h : i > j then σ.down.1 ⟨j, by simp_all; lia⟩ else 0) :=
  stdSimplex.map_δ_apply ..

end SimplexCategory
