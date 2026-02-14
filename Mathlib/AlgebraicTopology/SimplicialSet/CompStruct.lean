/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Arnoud van der Leer
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.CompStructTruncated

/-!
# Edges, "triangles" and isos in simplicial sets

Given a simplicial set `X`, we introduce three types:
* Given `0`-simplices `x₀` and `x₁`, we define `Edge x₀ x₁`
  which is the type of `1`-simplices with faces `x₁` and `x₀` respectively;
* Given `0`-simplices `x₀`, `x₁`, `x₂`, edges `e₀₁ : Edge x₀ x₁`, `e₁₂ : Edge x₁ x₂`,
  `e₀₂ : Edge x₀ x₂`, a structure `CompStruct e₀₁ e₁₂ e₀₂` which records the
  data of a `2`-simplex with faces `e₁₂`, `e₀₂` and `e₀₁` respectively. This data
  will allow to obtain relations in the homotopy category of `X`.

(This API parallels similar definitions for `2`-truncated simplicial sets.
The definitions in this file are definitionally equal to their `2`-truncated
counterparts.)

Given `0`-simplices `x₀` and `x₁`, and an edge `hom : Edge x₀ x₁`, `IsIso hom` records the data of
an edge `inv : Edge x₁ x₀` and simplices `homInvId : CompStruct hom inv (id x₀)` and
`invHomId : CompStruct inv hom (id x₁)`, witnessing that `inv` is an inverse to `hom`.

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

/-- Transports an edge between `x₀` and `x₁` along equalities `xᵢ = yᵢ`.
  I.e. constructs an edge between the `yᵢ` from an edge between the `xᵢ`. -/
def ofEq {y₀ y₁ : X _⦋0⦌}
    (e : Edge x₀ x₁)
    (h₀ : x₀ = y₀)
    (h₁ : x₁ = y₁) :
    Edge y₀ y₁ where
  edge    := e.edge
  src_eq  := e.src_eq.trans h₀
  tgt_eq  := e.tgt_eq.trans h₁

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

/-- Transports a CompStruct between edges `e₀₁`, `e₁₂` and `e₀₂` along equalities on
  1-simplices `eᵢⱼ.edge = fᵢⱼ.edge`.
  I.e. constructs a `CompStruct` between the `fᵢⱼ` from a `CompStruct` between the `eᵢⱼ`. -/
def ofEq {y₀ y₁ y₂ : X _⦋0⦌}
    {e₀₁ : Edge x₀ x₁} {f₀₁ : Edge y₀ y₁}
    {e₁₂ : Edge x₁ x₂} {f₁₂ : Edge y₁ y₂}
    {e₀₂ : Edge x₀ x₂} {f₀₂ : Edge y₀ y₂}
    (c : CompStruct e₀₁ e₁₂ e₀₂)
    (h₀₁ : e₀₁.edge = f₀₁.edge)
    (h₁₂ : e₁₂.edge = f₁₂.edge)
    (h₀₂ : e₀₂.edge = f₀₂.edge) :
    CompStruct f₀₁ f₁₂ f₀₂ where
  simplex := c.simplex
  d₂ := c.d₂.trans h₀₁
  d₀ := c.d₀.trans h₁₂
  d₁ := c.d₁.trans h₀₂

end CompStruct

/-- For `hom` an edge, `IsIso hom` encodes that there is a backward edge `inv`, and
  there are 2-simplices witnessing that `hom` and `inv` compose to the identity on their endpoints.
  This means that `hom` becomes an isomorphism in the homotopy category. -/
structure IsIso (hom : Edge x₀ x₁) where
  /-- The backwards edge -/
  inv : Edge x₁ x₀
  /-- The simplex witnessing that `hom` and `inv` compose to the identity -/
  homInvId  : CompStruct hom inv (id x₀)
  /-- The simplex witnessing that `inv` and `hom` compose to the identity -/
  invHomId  : CompStruct inv hom (id x₁)

namespace IsIso

lemma id_comp_id_aux {l m n : ℕ}
    {f : ⦋n⦌ ⟶ ⦋m⦌}
    {g : ⦋m⦌ ⟶ ⦋l⦌}
    {h : ⦋n⦌ ⟶ ⦋l⦌}
    (x : X _⦋l⦌)
    (e : f ≫ g = h) :
    X.map f.op (X.map g.op x) = X.map h.op x := by
  rw [← e, op_comp, X.map_comp]
  rfl

/-- The identity edge on a point, composed with itself, gives the identity. -/
def idCompId (x : X _⦋0⦌) : CompStruct (id x) (id x) (id x) :=
  .mk
    (X.map (Opposite.op (SimplexCategory.Hom.mk ⟨fun _ ↦ 0, monotone_const⟩)) x)
    (by apply id_comp_id_aux; decide)
    (by apply id_comp_id_aux; decide)
    (by apply id_comp_id_aux; decide)

/-- The identity edge is an isomorphism. -/
def isIsoId (x : X _⦋0⦌) : IsIso (id x) where
  inv := id x
  homInvId := idCompId x
  invHomId := idCompId x

/-- The inverse of an isomorphism is an isomorphism. -/
def isIsoInv {hom : Edge x₀ x₁} (I : IsIso hom) : IsIso I.inv where
  inv := hom
  homInvId := I.invHomId
  invHomId := I.homInvId

/-- The image of an isomorphism under an SSet morphism is an isomorphism. -/
def map {hom : Edge x₀ x₁} (I : IsIso hom) (f : X ⟶ Y) : IsIso (hom.map f) where
  inv := I.inv.map f
  homInvId := (I.homInvId.map f).ofEq rfl rfl (Edge.ext_iff.mp (map_id _ _))
  invHomId := (I.invHomId.map f).ofEq rfl rfl (Edge.ext_iff.mp (map_id _ _))

/-- Transports a proof of isomorphism for `hom` along an equality of 1-simplices `hom = hom'`.
  I.e. shows that `hom'` is an isomorphism from an isomorphism proof of `hom`. -/
def ofEq {y₀ y₁ : X _⦋0⦌} {hom : Edge x₀ x₁} {hom' : Edge y₀ y₁}
    (I : IsIso hom)
    (hhom : hom.edge = hom'.edge) :
    IsIso hom' where
  inv := I.inv.ofEq
    (by rw [← hom.tgt_eq, hhom, hom'.tgt_eq])
    (by rw [← hom.src_eq, hhom, hom'.src_eq])
  homInvId := I.homInvId.ofEq hhom rfl (by rw [← hom.src_eq, hhom, hom'.src_eq])
  invHomId := I.invHomId.ofEq rfl hhom (by rw [← hom.tgt_eq, hhom, hom'.tgt_eq])

end IsIso

end Edge

end SSet
