/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.AlgebraicTopology.SimplexCategory.Truncated

/-!
# Edges and "triangles" in (truncated) simplicial sets

-/

universe v u

open CategoryTheory Simplicial SimplicialObject.Truncated
  SimplexCategory.Truncated

namespace SSet

namespace Truncated

variable {X Y : Truncated.{u} 2}

/-- In a `2`-truncated simplicial set, an edge from a `0`-simplex `x₀` -/
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

/-- The constant edge on a `0`-simplex. -/
@[simps]
def id (x : X _⦋0⦌₂) : Edge x x where
  edge := X.map (σ₂ 0).op x
  src_eq := by simp [← FunctorToTypes.map_comp_apply, ← op_comp]
  tgt_eq := by simp [← FunctorToTypes.map_comp_apply, ← op_comp]

/-- The image of an edge by a morphism of truncated simplicial sets. -/
@[simps]
def map {x₀ x₁ : X _⦋0⦌₂} (e : Edge x₀ x₁) (f : X ⟶ Y) :
    Edge (f.app _ x₀) (f.app _ x₁) where
  edge := f.app _ e.edge
  src_eq := by simp [← FunctorToTypes.naturality]
  tgt_eq := by simp [← FunctorToTypes.naturality]

/-- Let `x₀`, `x₁`, `x₂` be `0`-simplices of a `2`-truncated simplicial set `X`,
`e₀₁` an edge from `x₀` to `x₁`, `e₁₂` an edge from `x₁` to `x₂`,
`e₀₂` an edge from `x₀` to `x₂`. This is the data of a `2`-simplex whose
faces are respectively `e₀₂`, `e₁₂` and `e₀₁`. Such structures shall provide
relations in the homotopy category of arbitrary (truncated) simplicial sets `X`
(and specialized constructions for quasicategories and Kan complexes.). -/
structure CompStruct {x₀ x₁ x₂ : X _⦋0⦌₂}
    (e₀₁ : Edge x₀ x₁) (e₁₂ : Edge x₁ x₂) (e₀₂ : Edge x₀ x₂) where
  /-- A `2`-simplex with prescribed `1`-dimensional faces -/
  simplex : X _⦋2⦌₂
  d₂ : X.map (δ₂ 2).op simplex = e₀₁.edge
  d₀ : X.map (δ₂ 0).op simplex = e₁₂.edge
  d₁ : X.map (δ₂ 1).op simplex = e₀₂.edge

namespace CompStruct

attribute [simp] d₀ d₁ d₂

/-- The composition of `Edge.id x` with `e : Edge x y` is `e`. -/
def idComp {x y : X _⦋0⦌₂} (e : Edge x y) :
    CompStruct (.id x) e e where
  simplex := X.map (σ₂ 0).op e.edge
  d₂ := by
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, δ₂_two_comp_σ₂_zero]
    simp
  d₀ := by
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, δ₂_zero_comp_σ₂_zero]
    simp
  d₁ := by
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, δ₂_one_comp_σ₂_zero]
    simp

/-- The composition of `e : Edge x y` with `Edge.id y` is `e`. -/
def compId {x y : X _⦋0⦌₂} (e : Edge x y) :
    CompStruct e (.id y) e where
  simplex := X.map (σ₂ 1).op e.edge
  d₂ := by
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, δ₂_two_comp_σ₂_one]
    simp
  d₀ := by
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, δ₂_zero_comp_σ₂_one]
    simp
  d₁ := by
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, δ₂_one_comp_σ₂_one]
    simp

/-- The image of a `Edge.CompStruct` by a morphism of `2`-truncated
simplicial sets. -/
@[simps]
def map {x₀ x₁ x₂ : X _⦋0⦌₂}
    {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂}
    (h : CompStruct e₀₁ e₁₂ e₀₂) (f : X ⟶ Y) :
    CompStruct (e₀₁.map f) (e₁₂.map f) (e₀₂.map f) where
  simplex := f.app _ h.simplex
  d₂ := by simp [← FunctorToTypes.naturality]
  d₀ := by simp [← FunctorToTypes.naturality]
  d₁ := by simp [← FunctorToTypes.naturality]

end CompStruct

end Edge

end Truncated

variable {X : SSet.{u}}

def Edge (x y : X _⦋0⦌) := Truncated.Edge (X := (truncation 2).obj X) x y

end SSet

namespace CategoryTheory

open SSet

variable {C : Type u} [Category.{v} C]

def nerveHomEquiv {x y : (nerve C) _⦋0⦌} :
    Edge x y ≃ (nerveEquiv x ⟶ nerveEquiv y) where
  toFun e := eqToHom (by simp only [nerveEquiv, ← e.src_eq]; rfl) ≫ e.edge.hom ≫
    eqToHom (by simp only [nerveEquiv, ← e.tgt_eq]; rfl)
  invFun f :=
    { edge := ComposableArrows.mk₁ f
      src_eq := ComposableArrows.ext₀ rfl
      tgt_eq := ComposableArrows.ext₀ rfl }
  left_inv := sorry
  right_inv := sorry

end CategoryTheory
