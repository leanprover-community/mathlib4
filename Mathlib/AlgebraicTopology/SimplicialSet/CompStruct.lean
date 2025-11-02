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

@[simp]
lemma map_id (x : X _⦋0⦌₂) (f : X ⟶ Y) :
    (Edge.id x).map f = Edge.id (f.app _ x) := by
  ext
  simp [FunctorToTypes.naturality]

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

/-- In a simplicial set, an edge from a vertex `x₀` to `x₁` is
a `1`-simplex with prescribed `0`-dimensional faces. -/
def Edge (x y : X _⦋0⦌) := Truncated.Edge (X := (truncation 2).obj X) x y

namespace Edge

variable {x y : X _⦋0⦌}

def edge (e : Edge x y) : X _⦋1⦌ := Truncated.Edge.edge e

@[simp]
lemma src_eq (e : Edge x y) : X.δ 1 e.edge = x := Truncated.Edge.src_eq e

@[simp]
lemma tgt_eq (e : Edge x y) : X.δ 0 e.edge = y := Truncated.Edge.tgt_eq e

@[ext]
lemma ext {x y : X _⦋0⦌} {e e' : Edge x y} (h : e.edge = e'.edge) :
    e = e' := Truncated.Edge.ext h

section

variable {x y : X _⦋0⦌} (s : X _⦋1⦌) (src_eq : X.δ 1 s = x) (tgt_eq : X.δ 0 s = y)

def mk : Edge x y where
  edge := s

@[simp]
lemma mk_edge : (mk s src_eq tgt_eq).edge = s := rfl

end

/-- The constant edge on a `0`-simplex. -/
def id (x : X _⦋0⦌) : Edge x x :=
  Truncated.Edge.id _

@[simp]
lemma id_edge (x : X _⦋0⦌) :
    (id x).edge = X.σ 0 x := rfl

def CompStruct {x₀ x₁ x₂ : X _⦋0⦌}
    (e₀₁ : Edge x₀ x₁) (e₁₂ : Edge x₁ x₂) (e₀₂ : Edge x₀ x₂) :=
  Truncated.Edge.CompStruct e₀₁ e₁₂ e₀₂

end Edge

end SSet

namespace CategoryTheory

open SSet

variable {C : Type u} [Category.{v} C]

@[simp]
lemma nerve.left {x y : (nerve C) _⦋0⦌} (e : Edge x y) :
    ComposableArrows.left e.edge = nerveEquiv x := by
  simp only [← e.src_eq]
  rfl

@[simp]
lemma nerve.right {x y : (nerve C) _⦋0⦌} (e : Edge x y) :
    ComposableArrows.right (n := 1) e.edge = nerveEquiv y := by
  simp only [← e.tgt_eq]
  rfl

def nerveHomEquiv {x y : (nerve C) _⦋0⦌} :
    Edge x y ≃ (nerveEquiv x ⟶ nerveEquiv y) where
  toFun e := eqToHom (by simp only [nerveEquiv, ← e.src_eq]; rfl) ≫ e.edge.hom ≫
    eqToHom (by simp only [nerveEquiv, ← e.tgt_eq]; rfl)
  invFun f := .mk (ComposableArrows.mk₁ f) (ComposableArrows.ext₀ rfl) (ComposableArrows.ext₀ rfl)
  left_inv e := by
    ext
    exact ComposableArrows.ext₁ (by simp) (by simp) rfl
  right_inv f := by simp

def Edge.ofHom {x y : C} (f : x ⟶ y) :
    Edge (nerveEquiv.symm x) (nerveEquiv.symm y) :=
  .mk (ComposableArrows.mk₁ f) sorry sorry

lemma Edge.ofHom_surjective {x y : C} :
    Function.Surjective (Edge.ofHom : (x ⟶ y) → _) := sorry

lemma nerve.nonempty_compStruct_iff {x₀ x₁ x₂ : C}
    (f₀₁ : x₀ ⟶ x₁) (f₁₂ : x₁ ⟶ x₂) (f₀₂ : x₀ ⟶ x₂) :
    Nonempty (Edge.CompStruct (Edge.ofHom f₀₁) (Edge.ofHom f₁₂) (Edge.ofHom f₀₂)) ↔
      f₀₁ ≫ f₁₂ = f₀₂ := sorry

@[simp]
lemma nerveHomEquiv_ofHom {x y : C} (f : x ⟶ y) :
    nerveHomEquiv (Edge.ofHom f) = f :=
  nerveHomEquiv.symm.injective (by
    ext
    simp only [Equiv.symm_apply_apply]
    exact ComposableArrows.ext₁ rfl rfl (by aesop))

@[simp]
lemma nerveHomEquiv_id (x : (nerve C) _⦋0⦌) :
    nerveHomEquiv (Edge.id x) = 𝟙 _ := by
  obtain ⟨x, rfl⟩ := nerveEquiv.symm.surjective x
  dsimp [nerveHomEquiv]
  cat_disch

lemma nerveHomEquiv_comp {x₀ x₁ x₂ : (nerve C) _⦋0⦌} {e₀₁ : Edge x₀ x₁}
    {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂} (h : Edge.CompStruct e₀₁ e₁₂ e₀₂) :
    nerveHomEquiv e₀₁ ≫ nerveHomEquiv e₁₂ = nerveHomEquiv e₀₂ := by
  obtain ⟨x₀, rfl⟩ := nerveEquiv.symm.surjective x₀
  obtain ⟨x₁, rfl⟩ := nerveEquiv.symm.surjective x₁
  obtain ⟨x₂, rfl⟩ := nerveEquiv.symm.surjective x₂
  obtain ⟨f₀₁, rfl⟩ := Edge.ofHom_surjective e₀₁
  obtain ⟨f₁₂, rfl⟩ := Edge.ofHom_surjective e₁₂
  obtain ⟨f₀₂, rfl⟩ := Edge.ofHom_surjective e₀₂
  convert (nerve.nonempty_compStruct_iff _ _ _).1 ⟨h⟩ <;> apply nerveHomEquiv_ofHom

lemma σ_zero_nerveEquiv_symm (x : C) :
    (nerve C).σ 0 (nerveEquiv.symm x) = ComposableArrows.mk₁ (𝟙 x) :=
  ComposableArrows.ext₁ rfl rfl (by aesop)

end CategoryTheory
