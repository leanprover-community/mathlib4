/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

/-!
# Homotopic maps induce isomorphic functors on the fundamental groupoid

The main definition in this file is `SSet.congrMapFundamentalGroupoid`.
Given two morphisms of simplicial sets `f : X ⟶ Y` and `g : X ⟶ Y`
and a homotopy `h : Homotopy f g`, this is an isomorphism between
the functors `mapFundamentalGroupoid f` and `mapFundamentalGroupoid g`.

## Implementation notes

We first define the variant `SSet.congrMapFundamentalGroupoid'`
which takes as an input a combinatorial simplicial homotopy
(as `h : SimplicialObject.Homotopy f g`), and we deduce the result
for terms in `SSet.Homotopy f g` which involve a morphism `X ⊗ Δ[1] ⟶ Y`.

-/

@[expose] public section

universe u

open CategoryTheory Simplicial

namespace SSet

variable {X Y : SSet.{u}} {f g : X ⟶ Y}

namespace Edge

open ConcreteCategory

/-!

Given ``h : SimplicialObject.Homotopy f g` where `f` and `g` are morphisms
of simplicial sets `X ⟶ Y`, we define an edge `ofSimplicialObjectHomotopy h x`
connecting `f.app _ x` and `g.app _ x` for any `x : X _⦋0⦌`.
If `e` is an edge from `x` to `y`, we obtain a diagram involving edges which
gives a commutative diagram in the fundamental groupoid (see the lemma
 `FundamentalGroupoid.comm_of_ofSimplicialObjectHomotopy`):
```
f.app _ x ---> g.app _ x
    |     \        |
    |      \       |
    |       \      |
    |        \     |
    v         v    v
f.app _ y ---> g.app _ y
```
The horizontal edges are obtained by `Edge.ofSimplicialObjectHomotopy`,
the vertical edges are the images of `e` by `f` and `g`, and
the diagonal edge is defined as `Edge.diagOfSimplicialObjectHomotopy h e`.
The commutativity of the lower left triangle is justified by
`Edge.CompStruct.ofSimplicialObjectHomotopy`, and the commutativity
of the upper right triangle is justified by
`Edge.CompStruct.ofSimplicialObjectHomotopy'`.

-/


variable (h : SimplicialObject.Homotopy f g)

/-- The edge connecting `f.app _ x` and `g.app _ x`
when `h : SimplicialObject.Homotopy f g` and `x` is a `0`-simplex. -/
def ofSimplicialObjectHomotopy (x : X _⦋0⦌) :
    Edge (f.app _ x) (g.app _ x) :=
  Edge.mk (h.h 0 x) (by rw [← (h.h_last_comp_δ_last 0)]; dsimp)
    (by rw [← SimplicialObject.Homotopy.h_zero_comp_δ_zero]; dsimp)

@[simp]
lemma ofSimplicialObjectHomotopy_edge (x : X _⦋0⦌) :
  (Edge.ofSimplicialObjectHomotopy h x).edge = h.h 0 x := rfl

variable {x y : X _⦋0⦌} (e : Edge x y)

/-- Given `h : SimplicialObject.Homotopy f g` and an edge `e : Edge x y`,
this is the edge that is the diagonal of the "commutative square" involving
`f.app _ x`, `g.app _ x`, `g.app _ y` and `f.app _ y`. -/
@[no_expose]
def diagOfSimplicialObjectHomotopy :
    Edge (f.app _ x) (g.app _ y) :=
  Edge.mk (Y.δ 1 (h.h 1 e.edge)) (by
    rw [dsimp% congr_hom (h.h_succ_comp_δ_castSucc_succ (n := 0) 0) e.edge,
      ← dsimp% Y.δ_comp_δ_apply (i := 1) (j := 1) (by simp),
      dsimp% congr_hom (h.h_castSucc_comp_δ_succ_of_lt (n := 0) 1 0 (by simp)) e.edge,
      e.src_eq, ← h.h_last_comp_δ_last 0]
    dsimp) (by
    rw [dsimp% Y.δ_comp_δ_apply (i := 0) (j := 0) (by simp),
      dsimp% congr_hom (h.h_succ_comp_δ_castSucc_of_lt 0 0 (by simp)) e.edge,
      tgt_eq, dsimp% congr_hom (h.h_zero_comp_δ_zero 0) y])

lemma diagOfSimplicialObjectHomotopy_edge :
    (diagOfSimplicialObjectHomotopy h e).edge = Y.δ 1 (h.h 1 e.edge) := by rfl

lemma diagOfSimplicialObjectHomotopy_edge' :
    (diagOfSimplicialObjectHomotopy h e).edge = Y.δ 1 (h.h 0 e.edge) :=
  congr_hom (h.h_succ_comp_δ_castSucc_succ (n := 0) 0) e.edge

/-- The lower left triangle of the "commutative square" that
`diagOfSimplicialObjectHomotopy h e` is part of,
when `h : SimplicialObject.Homotopy f g` and `e` is an edge. -/
def CompStruct.ofSimplicialObjectHomotopy :
    Edge.CompStruct (e.map f) (.ofSimplicialObjectHomotopy h y)
      (diagOfSimplicialObjectHomotopy h e) :=
  CompStruct.mk (h.h 1 e.edge) (by simp [← h.h_last_comp_δ_last 1])
    (by simpa using congr_hom (h.h_succ_comp_δ_castSucc_of_lt 0 0
      (by simp)) e.edge) (by simp [diagOfSimplicialObjectHomotopy_edge])

/-- The upper right triangle of the "commutative square" that
`diagOfSimplicialObjectHomotopy h e` is part of,
when `h : SimplicialObject.Homotopy f g` and `e` is an edge. -/
def CompStruct.ofSimplicialObjectHomotopy' :
    Edge.CompStruct (.ofSimplicialObjectHomotopy h x) (e.map g)
      (diagOfSimplicialObjectHomotopy h e) :=
  CompStruct.mk (h.h 0 e.edge)
    (by simpa using congr_hom (h.h_castSucc_comp_δ_succ_of_lt 1 0 (by simp)) e.edge)
    (congr_hom (h.h_zero_comp_δ_zero 1) e.edge)
    (by simp [diagOfSimplicialObjectHomotopy_edge'])

end Edge

@[reassoc]
lemma FundamentalGroupoid.comm_of_ofSimplicialObjectHomotopy
    (h : SimplicialObject.Homotopy f g) {x y : X _⦋0⦌} (e : Edge x y) :
    homMk (e.map f) ≫ homMk (Edge.ofSimplicialObjectHomotopy h y) =
      homMk (Edge.ofSimplicialObjectHomotopy h x) ≫ homMk (e.map g) := by
  simp [(Edge.CompStruct.ofSimplicialObjectHomotopy h e).homMk_comp,
    (Edge.CompStruct.ofSimplicialObjectHomotopy' h e).homMk_comp]

open FundamentalGroupoid

attribute [local simp] comm_of_ofSimplicialObjectHomotopy in
/-- Two homotopic maps of simplicial sets (where the homotopy is given
by a term in `SimplicialObject.Homotopy`) induce isomorphic functors
between the fundamental groupoids. -/
noncomputable def congrMapFundamentalGroupoid' (h : SimplicialObject.Homotopy f g) :
    mapFundamentalGroupoid f ≅ mapFundamentalGroupoid g :=
  natIsoMk (fun x ↦ asIso (homMk (Edge.ofSimplicialObjectHomotopy h x)))

lemma congrMapFundamentalGroupoid'_hom_app_mk
    (h : SimplicialObject.Homotopy f g) (x : X _⦋0⦌) :
    (congrMapFundamentalGroupoid' h).hom.app (.mk x) =
      homMk (Edge.ofSimplicialObjectHomotopy h x) := by rfl

/-- Two homotopic maps of simplicial sets (where the homotopy is given
by a term in `SSet.Homotopy`) induce isomorphic functors
between the fundamental groupoids. -/
noncomputable def congrMapFundamentalGroupoid (h : Homotopy f g) :
    mapFundamentalGroupoid f ≅ mapFundamentalGroupoid g :=
  congrMapFundamentalGroupoid' h.toSimplicialObjectHomotopy

lemma congrMapFundamentalGroupoid_hom_app_mk
    (h : Homotopy f g) (x : X _⦋0⦌) :
    (congrMapFundamentalGroupoid h).hom.app (.mk x) =
      homMk (Edge.ofSimplicialObjectHomotopy h.toSimplicialObjectHomotopy x) := by rfl

end SSet
