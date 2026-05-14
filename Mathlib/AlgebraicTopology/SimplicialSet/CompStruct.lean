/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.CompStructTruncated

/-!
# Edges and "triangles" in simplicial sets

Given a simplicial set `X`, we introduce two types:

* Given `0`-simplices `x₀` and `x₁`, we define `Edge x₀ x₁`
  which is the type of `1`-simplices with faces `x₁` and `x₀` respectively;
* Given `0`-simplices `x₀`, `x₁`, `x₂`, edges `e₀₁ : Edge x₀ x₁`, `e₁₂ : Edge x₁ x₂`,
  `e₀₂ : Edge x₀ x₂`, a structure `CompStruct e₀₁ e₁₂ e₀₂` which records the
  data of a `2`-simplex with faces `e₁₂`, `e₀₂` and `e₀₁` respectively. This data
  will allow to obtain relations in the homotopy category of `X`.

(This API parallels similar definitions for `2`-truncated simplicial sets.
The definitions in this file are definitionally equal to their `2`-truncated
counterparts.)

-/

@[expose] public section

universe v u

open CategoryTheory Simplicial

namespace SSet

variable {X Y : SSet.{u}} {x₀ x₁ x₂ : X _⦋0⦌}

variable (x₀ x₁) in
/-- In a simplicial set, an edge from a vertex `x₀` to `x₁` is
a `1`-simplex with prescribed `0`-dimensional faces. -/
def Edge := ((truncation 2).obj X).Edge x₀ x₁

namespace Edge

/-- Constructor for `SSet.Edge` which takes as an input a term in the definitionally
equal type `SSet.Truncated.Edge` for the `2`-truncation of the simplicial set.
(This definition is made to contain abuse of defeq in other definitions.) -/
def ofTruncated (e : ((truncation 2).obj X).Edge x₀ x₁) :
    Edge x₀ x₁ := e

/-- The edge of the `2`-truncation of a simplicial set `X` that is induced
by an edge of `X`. -/
def toTruncated (e : Edge x₀ x₁) :
    ((truncation 2).obj X).Edge x₀ x₁ :=
  e

/-- In a simplicial set, an edge from a vertex `x₀` to `x₁` is
a `1`-simplex with prescribed `0`-dimensional faces. -/
def edge (e : Edge x₀ x₁) : X _⦋1⦌ := e.toTruncated.edge

@[simp]
lemma ofTruncated_edge (e : ((truncation 2).obj X).Edge x₀ x₁) :
    (ofTruncated e).edge = e.edge := rfl

@[simp]
lemma toTruncated_edge (e : Edge x₀ x₁) :
    (toTruncated e).edge = e.edge := rfl

@[simp]
lemma src_eq (e : Edge x₀ x₁) : X.δ 1 e.edge = x₀ := Truncated.Edge.src_eq e

@[simp]
lemma tgt_eq (e : Edge x₀ x₁) : X.δ 0 e.edge = x₁ := Truncated.Edge.tgt_eq e

@[ext]
lemma ext {e e' : Edge x₀ x₁} (h : e.edge = e'.edge) :
    e = e' := Truncated.Edge.ext h

section

variable (edge : X _⦋1⦌) (src_eq : X.δ 1 edge = x₀ := by cat_disch)
  (tgt_eq : X.δ 0 edge = x₁ := by cat_disch)

set_option backward.privateInPublic true in
/-- Constructor for edges in a simplicial set. -/
def mk : Edge x₀ x₁ := ofTruncated { edge := edge }

set_option backward.privateInPublic true in
@[simp]
lemma mk_edge : (mk edge src_eq tgt_eq).edge = edge := rfl

end

variable (x₀) in
/-- The constant edge on a `0`-simplex. -/
def id : Edge x₀ x₀ := ofTruncated (.id _)

variable (x₀) in
@[simp]
lemma toTruncated_id :
    toTruncated (id x₀) = Truncated.Edge.id (X := (truncation 2).obj X) x₀ := rfl

variable (x₀) in
@[simp]
lemma id_edge : (id x₀).edge = X.σ 0 x₀ := rfl

/-- The image of an edge by a morphism of simplicial sets. -/
def map (e : Edge x₀ x₁) (f : X ⟶ Y) : Edge (f.app _ x₀) (f.app _ x₁) :=
  ofTruncated (e.toTruncated.map ((truncation 2).map f))

@[simp]
lemma map_edge (e : Edge x₀ x₁) (f : X ⟶ Y) :
    (e.map f).edge = f.app _ e.edge := rfl

variable (x₀) in
@[simp]
lemma map_id (f : X ⟶ Y) :
    (Edge.id x₀).map f = Edge.id (f.app _ x₀) :=
  Truncated.Edge.map_id _ _

/-- The edge given by a `1`-simplex. -/
def mk' (s : X _⦋1⦌) : Edge (X.δ 1 s) (X.δ 0 s) := mk s

@[simp]
lemma mk'_edge (s : X _⦋1⦌) : (mk' s).edge = s := rfl

lemma exists_of_simplex (s : X _⦋1⦌) :
    ∃ (x₀ x₁ : X _⦋0⦌) (e : Edge x₀ x₁), e.edge = s :=
  ⟨_, _, mk' s, rfl⟩

/-- Let `x₀`, `x₁`, `x₂` be `0`-simplices of a simplicial set `X`,
`e₀₁` an edge from `x₀` to `x₁`, `e₁₂` an edge from `x₁` to `x₂`,
`e₀₂` an edge from `x₀` to `x₂`. This is the data of a `2`-simplex whose
faces are respectively `e₀₂`, `e₁₂` and `e₀₁`. Such structures shall provide
relations in the homotopy category of arbitrary simplicial sets
(and specialized constructions for quasicategories and Kan complexes.). -/
def CompStruct (e₀₁ : Edge x₀ x₁) (e₁₂ : Edge x₁ x₂) (e₀₂ : Edge x₀ x₂) :=
  Truncated.Edge.CompStruct e₀₁.toTruncated e₁₂.toTruncated e₀₂.toTruncated

namespace CompStruct

variable {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂}

/-- Constructor for `SSet.Edge.CompStruct` which takes as an input a term in the
definitionally equal type `SSet.Truncated.Edge.CompStruct` for the `2`-truncation of
the simplicial set. (This definition is made to contain abuse of defeq in
other definitions.) -/
def ofTruncated (h : Truncated.Edge.CompStruct e₀₁.toTruncated e₁₂.toTruncated e₀₂.toTruncated) :
    CompStruct e₀₁ e₁₂ e₀₂ := h

/-- Conversion from `SSet.Edge.CompStruct` to `SSet.Truncated.Edge.CompStruct`. -/
def toTruncated (h : CompStruct e₀₁ e₁₂ e₀₂) :
    Truncated.Edge.CompStruct e₀₁.toTruncated e₁₂.toTruncated e₀₂.toTruncated :=
  h

section

variable (h : CompStruct e₀₁ e₁₂ e₀₂)

/-- The underlying `2`-simplex in a structure `SSet.Edge.CompStruct`. -/
def simplex : X _⦋2⦌ := h.toTruncated.simplex

@[simp]
lemma d₂ : X.δ 2 h.simplex = e₀₁.edge := Truncated.Edge.CompStruct.d₂ h

@[simp]
lemma d₀ : X.δ 0 h.simplex = e₁₂.edge := Truncated.Edge.CompStruct.d₀ h

@[simp]
lemma d₁ : X.δ 1 h.simplex = e₀₂.edge := Truncated.Edge.CompStruct.d₁ h

end

section

variable (simplex : X _⦋2⦌)
  (d₂ : X.δ 2 simplex = e₀₁.edge := by cat_disch)
  (d₀ : X.δ 0 simplex = e₁₂.edge := by cat_disch)
  (d₁ : X.δ 1 simplex = e₀₂.edge := by cat_disch)

set_option backward.privateInPublic true in
/-- Constructor for `SSet.Edge.CompStruct`. -/
def mk : CompStruct e₀₁ e₁₂ e₀₂ where
  simplex := simplex

set_option backward.privateInPublic true in
@[simp]
lemma mk_simplex : (mk simplex).simplex = simplex := rfl

end

@[ext]
lemma ext {h h' : CompStruct e₀₁ e₁₂ e₀₂} (eq : h.simplex = h'.simplex) :
    h = h' :=
  Truncated.Edge.CompStruct.ext eq

lemma exists_of_simplex (s : X _⦋2⦌) :
    ∃ (x₀ x₁ x₂ : X _⦋0⦌) (e₀₁ : Edge x₀ x₁) (e₁₂ : Edge x₁ x₂)
      (e₀₂ : Edge x₀ x₂) (h : CompStruct e₀₁ e₁₂ e₀₂), h.simplex = s :=
  Truncated.Edge.CompStruct.exists_of_simplex (X := (truncation 2).obj X) s

/-- `e : Edge x₀ x₁` is a composition of `Edge.id x₀` with `e`. -/
def idComp (e : Edge x₀ x₁) : CompStruct (.id x₀) e e :=
  ofTruncated (.idComp _)

@[simp]
lemma idComp_simplex (e : Edge x₀ x₁) : (idComp e).simplex = X.σ 0 e.edge := rfl

/-- `e : Edge x₀ x₁` is a composition of `e` with `Edge.id x₁` -/
def compId (e : Edge x₀ x₁) : CompStruct e (.id x₁) e :=
  ofTruncated (.compId _)

@[simp]
lemma compId_simplex (e : Edge x₀ x₁) : (compId e).simplex = X.σ 1 e.edge := rfl

/-- The image of a `Edge.CompStruct` by a morphism of simplicial sets. -/
def map (h : CompStruct e₀₁ e₁₂ e₀₂) (f : X ⟶ Y) :
    CompStruct (e₀₁.map f) (e₁₂.map f) (e₀₂.map f) :=
  .ofTruncated (h.toTruncated.map ((truncation 2).map f))

@[simp]
lemma map_simplex (h : CompStruct e₀₁ e₁₂ e₀₂) (f : X ⟶ Y) :
    (h.map f).simplex = f.app _ h.simplex := rfl

end CompStruct

end Edge

end SSet
