/-
Copyright (c) 2022 George Peter Banyard, Yaël Dillies, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Peter Banyard, Yaël Dillies, Kyle Miller
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity

#align_import combinatorics.simple_graph.prod from "leanprover-community/mathlib"@"2985fa3c31a27274aed06c433510bc14b73d6488"

/-!
# Graph products

This file defines the box product of graphs and other product constructions. The box product of `G`
and `H` is the graph on the product of the vertices such that `x` and `y` are related iff they agree
on one component and the other one is related via either `G` or `H`. For example, the box product of
two edges is a square.

## Main declarations

* `SimpleGraph.boxProd`: The box product.

## Notation

* `G □ H`: The box product of `G` and `H`.

## TODO

Define all other graph products!
-/

set_option autoImplicit true


variable {α β γ : Type*}

namespace SimpleGraph

-- Porting note: pruned variables to keep things out of local contexts, which
-- can impact how generalization works, or what aesop does.
variable {G : SimpleGraph α} {H : SimpleGraph β}

/-- Box product of simple graphs. It relates `(a₁, b)` and `(a₂, b)` if `G` relates `a₁` and `a₂`,
and `(a, b₁)` and `(a, b₂)` if `H` relates `b₁` and `b₂`. -/
def boxProd (G : SimpleGraph α) (H : SimpleGraph β) : SimpleGraph (α × β) where
  Adj x y := G.Adj x.1 y.1 ∧ x.2 = y.2 ∨ H.Adj x.2 y.2 ∧ x.1 = y.1
  symm x y := by simp [and_comm, or_comm, eq_comm, adj_comm]
                 -- 🎉 no goals
  loopless x := by simp
                   -- 🎉 no goals
#align simple_graph.box_prod SimpleGraph.boxProd

-- mathport name: «expr □ »
/-- Box product of simple graphs. It relates `(a₁, b)` and `(a₂, b)` if `G` relates `a₁` and `a₂`,
and `(a, b₁)` and `(a, b₂)` if `H` relates `b₁` and `b₂`. -/
infixl:70 " □ " => boxProd

@[simp]
theorem boxProd_adj : (G □ H).Adj x y ↔ G.Adj x.1 y.1 ∧ x.2 = y.2 ∨ H.Adj x.2 y.2 ∧ x.1 = y.1 :=
  Iff.rfl
#align simple_graph.box_prod_adj SimpleGraph.boxProd_adj

--@[simp] porting note: `simp` can prove
theorem boxProd_adj_left : (G □ H).Adj (a₁, b) (a₂, b) ↔ G.Adj a₁ a₂ := by
  simp only [boxProd_adj, and_true, SimpleGraph.irrefl, false_and, or_false]
  -- 🎉 no goals
#align simple_graph.box_prod_adj_left SimpleGraph.boxProd_adj_left

--@[simp] porting note: `simp` can prove
theorem boxProd_adj_right : (G □ H).Adj (a, b₁) (a, b₂) ↔ H.Adj b₁ b₂ := by
  simp only [boxProd_adj, SimpleGraph.irrefl, false_and, and_true, false_or]
  -- 🎉 no goals
#align simple_graph.box_prod_adj_right SimpleGraph.boxProd_adj_right

theorem boxProd_neighborSet (x : α × β) :
    (G □ H).neighborSet x = G.neighborSet x.1 ×ˢ {x.2} ∪ {x.1} ×ˢ H.neighborSet x.2 := by
  ext ⟨a', b'⟩
  -- ⊢ (a', b') ∈ neighborSet (G □ H) x ↔ (a', b') ∈ neighborSet G x.fst ×ˢ {x.snd} …
  simp only [mem_neighborSet, Set.mem_union, boxProd_adj, Set.mem_prod, Set.mem_singleton_iff]
  -- ⊢ Adj G x.fst a' ∧ x.snd = b' ∨ Adj H x.snd b' ∧ x.fst = a' ↔ Adj G x.fst a' ∧ …
  simp only [eq_comm, and_comm]
  -- 🎉 no goals
#align simple_graph.box_prod_neighbor_set SimpleGraph.boxProd_neighborSet

variable (G H)

/-- The box product is commutative up to isomorphism. `Equiv.prodComm` as a graph isomorphism. -/
@[simps!]
def boxProdComm : G □ H ≃g H □ G := ⟨Equiv.prodComm _ _, or_comm⟩
#align simple_graph.box_prod_comm SimpleGraph.boxProdComm

/-- The box product is associative up to isomorphism. `Equiv.prodAssoc` as a graph isomorphism. -/
@[simps!]
def boxProdAssoc (I : SimpleGraph γ) : G □ H □ I ≃g G □ (H □ I) :=
  ⟨Equiv.prodAssoc _ _ _, fun {x y} => by
    simp only [boxProd_adj, Equiv.prodAssoc_apply, or_and_right, or_assoc, Prod.ext_iff,
      and_assoc, @and_comm (x.fst.fst = _)]⟩
#align simple_graph.box_prod_assoc SimpleGraph.boxProdAssoc

/-- The embedding of `G` into `G □ H` given by `b`. -/
@[simps]
def boxProdLeft (b : β) : G ↪g G □ H where
  toFun a := (a, b)
  inj' _ _ := congr_arg Prod.fst
  map_rel_iff' {_ _} := boxProd_adj_left
#align simple_graph.box_prod_left SimpleGraph.boxProdLeft

/-- The embedding of `H` into `G □ H` given by `a`. -/
@[simps]
def boxProdRight (a : α) : H ↪g G □ H where
  toFun := Prod.mk a
  inj' _ _ := congr_arg Prod.snd
  map_rel_iff' {_ _} := boxProd_adj_right
#align simple_graph.box_prod_right SimpleGraph.boxProdRight

namespace Walk

variable {G}

/-- Turn a walk on `G` into a walk on `G □ H`. -/
protected def boxProdLeft (b : β) : G.Walk a₁ a₂ → (G □ H).Walk (a₁, b) (a₂, b) :=
  Walk.map (G.boxProdLeft H b).toHom
#align simple_graph.walk.box_prod_left SimpleGraph.Walk.boxProdLeft

variable (G) {H}

/-- Turn a walk on `H` into a walk on `G □ H`. -/
protected def boxProdRight (a : α) : H.Walk b₁ b₂ → (G □ H).Walk (a, b₁) (a, b₂) :=
  Walk.map (G.boxProdRight H a).toHom
#align simple_graph.walk.box_prod_right SimpleGraph.Walk.boxProdRight

variable {G}

/-- Project a walk on `G □ H` to a walk on `G` by discarding the moves in the direction of `H`. -/
def ofBoxProdLeft [DecidableEq β] [DecidableRel G.Adj] {x y : α × β} :
    (G □ H).Walk x y → G.Walk x.1 y.1
  | nil => nil
  | cons h w =>
    Or.by_cases h
      (fun hG => w.ofBoxProdLeft.cons hG.1)
      (fun hH => hH.2 ▸ w.ofBoxProdLeft)
#align simple_graph.walk.of_box_prod_left SimpleGraph.Walk.ofBoxProdLeft

/-- Project a walk on `G □ H` to a walk on `H` by discarding the moves in the direction of `G`. -/
def ofBoxProdRight [DecidableEq α] [DecidableRel H.Adj] {x y : α × β} :
    (G □ H).Walk x y → H.Walk x.2 y.2
  | nil => nil
  | cons h w =>
    (Or.symm h).by_cases
      (fun hH => w.ofBoxProdRight.cons hH.1)
      (fun hG => hG.2 ▸ w.ofBoxProdRight)
#align simple_graph.walk.of_box_prod_right SimpleGraph.Walk.ofBoxProdRight

@[simp]
theorem ofBoxProdLeft_boxProdLeft [DecidableEq β] [DecidableRel G.Adj] {a₁ a₂ : α} :
    ∀ (w : G.Walk a₁ a₂), (w.boxProdLeft H b).ofBoxProdLeft = w
  | nil => rfl
  | cons' x y z h w => by
    rw [Walk.boxProdLeft, map_cons, ofBoxProdLeft, Or.by_cases, dif_pos, ← Walk.boxProdLeft]
    simp [ofBoxProdLeft_boxProdLeft]
    -- ⊢ Adj G (x, b).fst (↑(Embedding.toHom (boxProdLeft G H b)) y).fst ∧ (x, b).snd …
    exact ⟨h, rfl⟩
    -- 🎉 no goals
#align simple_graph.walk.of_box_prod_left_box_prod_left SimpleGraph.Walk.ofBoxProdLeft_boxProdLeft

@[simp]
theorem ofBoxProdLeft_boxProdRight [DecidableEq α] [DecidableRel G.Adj] {b₁ b₂ : α} :
    ∀ (w : G.Walk b₁ b₂), (w.boxProdRight G a).ofBoxProdRight = w
  | nil => rfl
  | cons' x y z h w => by
    rw [Walk.boxProdRight, map_cons, ofBoxProdRight, Or.by_cases, dif_pos, ←
      Walk.boxProdRight]
    simp [ofBoxProdLeft_boxProdRight]
    -- ⊢ Adj G (a, x).snd (↑(Embedding.toHom (boxProdRight G G a)) y).snd ∧ (a, x).fs …
    exact⟨h, rfl⟩
    -- 🎉 no goals
#align simple_graph.walk.of_box_prod_left_box_prod_right SimpleGraph.Walk.ofBoxProdLeft_boxProdRight

end Walk

variable {G H}

protected theorem Preconnected.boxProd (hG : G.Preconnected) (hH : H.Preconnected) :
    (G □ H).Preconnected := by
  rintro x y
  -- ⊢ Reachable (G □ H) x y
  obtain ⟨w₁⟩ := hG x.1 y.1
  -- ⊢ Reachable (G □ H) x y
  obtain ⟨w₂⟩ := hH x.2 y.2
  -- ⊢ Reachable (G □ H) x y
  rw [← @Prod.mk.eta _ _ x, ← @Prod.mk.eta _ _ y]
  -- ⊢ Reachable (G □ H) (x.fst, x.snd) (y.fst, y.snd)
  exact ⟨(w₁.boxProdLeft _ _).append (w₂.boxProdRight _ _)⟩
  -- 🎉 no goals
#align simple_graph.preconnected.box_prod SimpleGraph.Preconnected.boxProd

protected theorem Preconnected.ofBoxProdLeft [Nonempty β] (h : (G □ H).Preconnected) :
    G.Preconnected := by
  classical
  rintro a₁ a₂
  obtain ⟨w⟩ := h (a₁, Classical.arbitrary _) (a₂, Classical.arbitrary _)
  exact ⟨w.ofBoxProdLeft⟩
#align simple_graph.preconnected.of_box_prod_left SimpleGraph.Preconnected.ofBoxProdLeft

protected theorem Preconnected.ofBoxProdRight [Nonempty α] (h : (G □ H).Preconnected) :
    H.Preconnected := by
  classical
  rintro b₁ b₂
  obtain ⟨w⟩ := h (Classical.arbitrary _, b₁) (Classical.arbitrary _, b₂)
  exact ⟨w.ofBoxProdRight⟩
#align simple_graph.preconnected.of_box_prod_right SimpleGraph.Preconnected.ofBoxProdRight

protected theorem Connected.boxProd (hG : G.Connected) (hH : H.Connected) : (G □ H).Connected := by
  haveI := hG.nonempty
  -- ⊢ Connected (G □ H)
  haveI := hH.nonempty
  -- ⊢ Connected (G □ H)
  exact ⟨hG.preconnected.boxProd hH.preconnected⟩
  -- 🎉 no goals
#align simple_graph.connected.box_prod SimpleGraph.Connected.boxProd

protected theorem Connected.ofBoxProdLeft (h : (G □ H).Connected) : G.Connected := by
  haveI := (nonempty_prod.1 h.nonempty).1
  -- ⊢ Connected G
  haveI := (nonempty_prod.1 h.nonempty).2
  -- ⊢ Connected G
  exact ⟨h.preconnected.ofBoxProdLeft⟩
  -- 🎉 no goals
#align simple_graph.connected.of_box_prod_left SimpleGraph.Connected.ofBoxProdLeft

protected theorem Connected.ofBoxProdRight (h : (G □ H).Connected) : H.Connected := by
  haveI := (nonempty_prod.1 h.nonempty).1
  -- ⊢ Connected H
  haveI := (nonempty_prod.1 h.nonempty).2
  -- ⊢ Connected H
  exact ⟨h.preconnected.ofBoxProdRight⟩
  -- 🎉 no goals
#align simple_graph.connected.of_box_prod_right SimpleGraph.Connected.ofBoxProdRight

@[simp]
theorem boxProd_connected : (G □ H).Connected ↔ G.Connected ∧ H.Connected :=
  ⟨fun h => ⟨h.ofBoxProdLeft, h.ofBoxProdRight⟩, fun h => h.1.boxProd h.2⟩
#align simple_graph.box_prod_connected SimpleGraph.boxProd_connected

instance boxProdFintypeNeighborSet (x : α × β)
    [Fintype (G.neighborSet x.1)] [Fintype (H.neighborSet x.2)] :
    Fintype ((G □ H).neighborSet x) :=
  Fintype.ofEquiv
    ((G.neighborFinset x.1 ×ˢ {x.2}).disjUnion ({x.1} ×ˢ H.neighborFinset x.2) <|
        Finset.disjoint_product.mpr <| Or.inl <| neighborFinset_disjoint_singleton _ _)
    ((Equiv.refl _).subtypeEquiv fun y => by
      simp_rw [Finset.mem_disjUnion, Finset.mem_product, Finset.mem_singleton, mem_neighborFinset,
        mem_neighborSet, Equiv.refl_apply, boxProd_adj]
      simp only [eq_comm, and_comm])
      -- 🎉 no goals
#align simple_graph.box_prod_fintype_neighbor_set SimpleGraph.boxProdFintypeNeighborSet

theorem boxProd_neighborFinset (x : α × β)
    [Fintype (G.neighborSet x.1)] [Fintype (H.neighborSet x.2)] [Fintype ((G □ H).neighborSet x)] :
    (G □ H).neighborFinset x =
      (G.neighborFinset x.1 ×ˢ {x.2}).disjUnion ({x.1} ×ˢ H.neighborFinset x.2)
        (Finset.disjoint_product.mpr <| Or.inl <| neighborFinset_disjoint_singleton _ _) := by
  -- swap out the fintype instance for the canonical one
  letI : Fintype ((G □ H).neighborSet x) := SimpleGraph.boxProdFintypeNeighborSet _
  -- ⊢ neighborFinset (G □ H) x = Finset.disjUnion (neighborFinset G x.fst ×ˢ {x.sn …
  convert_to (G □ H).neighborFinset x = _ using 2
  -- ⊢ neighborFinset (G □ H) x = Finset.disjUnion (neighborFinset G x.fst ×ˢ {x.sn …
  exact Eq.trans (Finset.map_map _ _ _) Finset.attach_map_val
  -- 🎉 no goals
#align simple_graph.box_prod_neighbor_finset SimpleGraph.boxProd_neighborFinset

theorem boxProd_degree (x : α × β)
    [Fintype (G.neighborSet x.1)] [Fintype (H.neighborSet x.2)] [Fintype ((G □ H).neighborSet x)] :
    (G □ H).degree x = G.degree x.1 + H.degree x.2 := by
  rw [degree, degree, degree, boxProd_neighborFinset, Finset.card_disjUnion]
  -- ⊢ Finset.card (neighborFinset G x.fst ×ˢ {x.snd}) + Finset.card ({x.fst} ×ˢ ne …
  simp_rw [Finset.card_product, Finset.card_singleton, mul_one, one_mul]
  -- 🎉 no goals
#align simple_graph.box_prod_degree SimpleGraph.boxProd_degree

end SimpleGraph
