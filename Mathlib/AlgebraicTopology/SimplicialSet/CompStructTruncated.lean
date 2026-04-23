/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Truncated
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
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
# Edges and "triangles" in truncated simplicial sets

Given a `2`-truncated simplicial set `X`, we introduce two types:
* Given `0`-simplices `x₀` and `x₁`, we define `Edge x₀ x₁`
  which is the type of `1`-simplices with faces `x₁` and `x₀` respectively;
* Given `0`-simplices `x₀`, `x₁`, `x₂`, edges `e₀₁ : Edge x₀ x₁`, `e₁₂ : Edge x₁ x₂`,
  `e₀₂ : Edge x₀ x₂`, a structure `CompStruct e₀₁ e₁₂ e₀₂` which records the
  data of a `2`-simplex with faces `e₁₂`, `e₀₂` and `e₀₁` respectively. This data
  will allow to obtain relations in the homotopy category of `X`.

-/

@[expose] public section

universe v u

open CategoryTheory Simplicial SimplicialObject.Truncated
  SimplexCategory.Truncated

namespace SSet.Truncated

variable {X Y : Truncated.{u} 2}

/-- In a `2`-truncated simplicial set, an edge from a vertex `x₀` to `x₁` is
a `1`-simplex with prescribed `0`-dimensional faces. -/
@[ext]
structure Edge (x₀ x₁ : X _⦋0⦌₂) where
  /-- A `1`-simplex -/
  edge : X _⦋1⦌₂
  /-- The source of the edge is `x₀`. -/
  src_eq : X.map (δ₂ 1).op edge = x₀ := by cat_disch
  /-- The target of the edge is `x₁`. -/
  tgt_eq : X.map (δ₂ 0).op edge = x₁ := by cat_disch

namespace Edge

attribute [simp] src_eq tgt_eq

/-- The edge given by a `1`-simplex. -/
@[simps]
def mk' (s : X _⦋1⦌₂) : Edge (X.map (δ₂ 1).op s) (X.map (δ₂ 0).op s) where
  edge := s

lemma exists_of_simplex (s : X _⦋1⦌₂) :
    ∃ (x₀ x₁ : X _⦋0⦌₂) (e : Edge x₀ x₁), e.edge = s :=
  ⟨_, _, mk' s, rfl⟩

/-- The constant edge on a `0`-simplex. -/
@[simps]
def id (x : X _⦋0⦌₂) : Edge x x where
  edge := X.map (σ₂ 0).op x
  src_eq := by simp [← Functor.map_comp_apply, ← op_comp]
  tgt_eq := by simp [← Functor.map_comp_apply, ← op_comp]

/-- The image of an edge by a morphism of truncated simplicial sets. -/
@[simps]
def map {x₀ x₁ : X _⦋0⦌₂} (e : Edge x₀ x₁) (f : X ⟶ Y) :
    Edge (f.app _ x₀) (f.app _ x₁) where
  edge := f.app _ e.edge
  src_eq := by simp [← NatTrans.naturality_apply]
  tgt_eq := by simp [← NatTrans.naturality_apply]

@[simp]
lemma map_id (x : X _⦋0⦌₂) (f : X ⟶ Y) :
    (Edge.id x).map f = Edge.id (f.app _ x) := by
  ext
  simp [NatTrans.naturality_apply]

instance [Subsingleton (X _⦋1⦌₂)] {x y : X _⦋0⦌₂} :
    Subsingleton (X.Edge x y) where
  allEq f g := by ext; subsingleton

/-- Let `x₀`, `x₁`, `x₂` be `0`-simplices of a `2`-truncated simplicial set `X`,
`e₀₁` an edge from `x₀` to `x₁`, `e₁₂` an edge from `x₁` to `x₂`,
`e₀₂` an edge from `x₀` to `x₂`. This is the data of a `2`-simplex whose
faces are respectively `e₀₂`, `e₁₂` and `e₀₁`. Such structures shall provide
relations in the homotopy category of arbitrary (truncated) simplicial sets
(and specialized constructions for quasicategories and Kan complexes.). -/
@[ext]
structure CompStruct {x₀ x₁ x₂ : X _⦋0⦌₂}
    (e₀₁ : Edge x₀ x₁) (e₁₂ : Edge x₁ x₂) (e₀₂ : Edge x₀ x₂) where
  /-- A `2`-simplex with prescribed `1`-dimensional faces -/
  simplex : X _⦋2⦌₂
  d₂ : X.map (δ₂ 2).op simplex = e₀₁.edge := by cat_disch
  d₀ : X.map (δ₂ 0).op simplex = e₁₂.edge := by cat_disch
  d₁ : X.map (δ₂ 1).op simplex = e₀₂.edge := by cat_disch

namespace CompStruct

attribute [simp] d₀ d₁ d₂

lemma exists_of_simplex (s : X _⦋2⦌₂) :
    ∃ (x₀ x₁ x₂ : X _⦋0⦌₂) (e₀₁ : Edge x₀ x₁) (e₁₂ : Edge x₁ x₂)
      (e₀₂ : Edge x₀ x₂) (h : CompStruct e₀₁ e₁₂ e₀₂), h.simplex = s := by
  refine ⟨X.map (Hom.tr (SimplexCategory.const _ _ 0)).op s,
    X.map (Hom.tr (SimplexCategory.const _ _ 1)).op s,
    X.map (Hom.tr (SimplexCategory.const _ _ 2)).op s,
    .mk _ ?_ ?_, .mk _ ?_ ?_, .mk _ ?_ ?_, .mk s rfl rfl rfl, rfl⟩
  all_goals
  · rw [← Functor.map_comp_apply, ← op_comp]
    apply congr_fun; congr
    decide

/-- `e : Edge x y` is a composition of `Edge.id x` with `e`. -/
def idComp {x y : X _⦋0⦌₂} (e : Edge x y) :
    CompStruct (.id x) e e where
  simplex := X.map (σ₂ 0).op e.edge
  d₂ := by
    rw [← Functor.map_comp_apply, ← op_comp, δ₂_two_comp_σ₂_zero]
    simp
  d₀ := by
    rw [← Functor.map_comp_apply, ← op_comp, δ₂_zero_comp_σ₂_zero]
    simp
  d₁ := by
    rw [← Functor.map_comp_apply, ← op_comp, δ₂_one_comp_σ₂_zero]
    simp

/-- `e : Edge x y` is a composition of `e` with `Edge.id y`. -/
def compId {x y : X _⦋0⦌₂} (e : Edge x y) :
    CompStruct e (.id y) e where
  simplex := X.map (σ₂ 1).op e.edge
  d₂ := by
    rw [← Functor.map_comp_apply, ← op_comp, δ₂_two_comp_σ₂_one]
    simp
  d₀ := by
    rw [← Functor.map_comp_apply, ← op_comp, δ₂_zero_comp_σ₂_one]
    simp
  d₁ := by
    rw [← Functor.map_comp_apply, ← op_comp, δ₂_one_comp_σ₂_one]
    simp

/-- `Edge.id x` is a composition of `Edge.id x` with `Edge.id x`. -/
@[simps!]
def idCompId (x : X _⦋0⦌₂) :
    CompStruct (.id x) (.id x) (.id x) :=
  idComp _

attribute [local simp ←] FunctorToTypes.naturality in
/-- The image of a `Edge.CompStruct` by a morphism of `2`-truncated
simplicial sets. -/
@[simps]
def map {x₀ x₁ x₂ : X _⦋0⦌₂}
    {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂}
    (h : CompStruct e₀₁ e₁₂ e₀₂) (f : X ⟶ Y) :
    CompStruct (e₀₁.map f) (e₁₂.map f) (e₀₂.map f) where
  simplex := f.app _ h.simplex

end CompStruct

end Edge

end SSet.Truncated
