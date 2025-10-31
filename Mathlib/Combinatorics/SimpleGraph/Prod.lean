/-
Copyright (c) 2022 George Peter Banyard, Yaël Dillies, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Peter Banyard, Yaël Dillies, Kyle Miller
-/
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Metric

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

variable {α β γ : Type*}

namespace SimpleGraph

variable {G : SimpleGraph α} {H : SimpleGraph β}

/-- Box product of simple graphs. It relates `(a₁, b)` and `(a₂, b)` if `G` relates `a₁` and `a₂`,
and `(a, b₁)` and `(a, b₂)` if `H` relates `b₁` and `b₂`. -/
def boxProd (G : SimpleGraph α) (H : SimpleGraph β) : SimpleGraph (α × β) where
  Adj x y := G.Adj x.1 y.1 ∧ x.2 = y.2 ∨ H.Adj x.2 y.2 ∧ x.1 = y.1
  symm x y := by simp [and_comm, eq_comm, adj_comm]
  loopless x := by simp

/-- Box product of simple graphs. It relates `(a₁, b)` and `(a₂, b)` if `G` relates `a₁` and `a₂`,
and `(a, b₁)` and `(a, b₂)` if `H` relates `b₁` and `b₂`. -/
infixl:70 " □ " => boxProd

@[simp]
theorem boxProd_adj {x y : α × β} :
    (G □ H).Adj x y ↔ G.Adj x.1 y.1 ∧ x.2 = y.2 ∨ H.Adj x.2 y.2 ∧ x.1 = y.1 :=
  Iff.rfl

theorem boxProd_adj_left {a₁ : α} {b : β} {a₂ : α} :
    (G □ H).Adj (a₁, b) (a₂, b) ↔ G.Adj a₁ a₂ := by
  simp only [boxProd_adj, and_true, SimpleGraph.irrefl, false_and, or_false]

theorem boxProd_adj_right {a : α} {b₁ b₂ : β} : (G □ H).Adj (a, b₁) (a, b₂) ↔ H.Adj b₁ b₂ := by
  simp only [boxProd_adj, SimpleGraph.irrefl, false_and, and_true, false_or]

theorem neighborSet_boxProd (x : α × β) :
    (G □ H).neighborSet x = G.neighborSet x.1 ×ˢ {x.2} ∪ {x.1} ×ˢ H.neighborSet x.2 := by
  ext ⟨a', b'⟩
  simp only [mem_neighborSet, Set.mem_union, boxProd_adj, Set.mem_prod, Set.mem_singleton_iff]
  simp only [eq_comm, and_comm]

@[deprecated (since := "2025-05-08")] alias boxProd_neighborSet := neighborSet_boxProd

variable (G H)

/-- The box product is commutative up to isomorphism. `Equiv.prodComm` as a graph isomorphism. -/
@[simps!]
def boxProdComm : G □ H ≃g H □ G := ⟨Equiv.prodComm _ _, or_comm⟩

/-- The box product is associative up to isomorphism. `Equiv.prodAssoc` as a graph isomorphism. -/
@[simps!]
def boxProdAssoc (I : SimpleGraph γ) : G □ H □ I ≃g G □ (H □ I) :=
  ⟨Equiv.prodAssoc _ _ _, fun {x y} => by
    simp only [boxProd_adj, Equiv.prodAssoc_apply, or_and_right, or_assoc, Prod.ext_iff,
      and_assoc, @and_comm (x.fst.fst = _)]⟩

/-- The embedding of `G` into `G □ H` given by `b`. -/
@[simps]
def boxProdLeft (b : β) : G ↪g G □ H where
  toFun a := (a, b)
  inj' _ _ := congr_arg Prod.fst
  map_rel_iff' {_ _} := boxProd_adj_left

/-- The embedding of `H` into `G □ H` given by `a`. -/
@[simps]
def boxProdRight (a : α) : H ↪g G □ H where
  toFun := Prod.mk a
  inj' _ _ := congr_arg Prod.snd
  map_rel_iff' {_ _} := boxProd_adj_right

namespace Walk

variable {G}

/-- Turn a walk on `G` into a walk on `G □ H`. -/
protected def boxProdLeft {a₁ a₂ : α} (b : β) : G.Walk a₁ a₂ → (G □ H).Walk (a₁, b) (a₂, b) :=
  Walk.map (G.boxProdLeft H b).toHom

variable (G) {H}

/-- Turn a walk on `H` into a walk on `G □ H`. -/
protected def boxProdRight {b₁ b₂ : β} (a : α) : H.Walk b₁ b₂ → (G □ H).Walk (a, b₁) (a, b₂) :=
  Walk.map (G.boxProdRight H a).toHom

variable {G}

/-- Project a walk on `G □ H` to a walk on `G` by discarding the moves in the direction of `H`. -/
def ofBoxProdLeft [DecidableEq β] [DecidableRel G.Adj] {x y : α × β} :
    (G □ H).Walk x y → G.Walk x.1 y.1
  | nil => nil
  | cons h w =>
    Or.by_cases h
      (fun hG => w.ofBoxProdLeft.cons hG.1)
      (fun hH => hH.2 ▸ w.ofBoxProdLeft)

/-- Project a walk on `G □ H` to a walk on `H` by discarding the moves in the direction of `G`. -/
def ofBoxProdRight [DecidableEq α] [DecidableRel H.Adj] {x y : α × β} :
    (G □ H).Walk x y → H.Walk x.2 y.2
  | nil => nil
  | cons h w =>
    (Or.symm h).by_cases
      (fun hH => w.ofBoxProdRight.cons hH.1)
      (fun hG => hG.2 ▸ w.ofBoxProdRight)

@[simp]
theorem ofBoxProdLeft_boxProdLeft [DecidableEq β] [DecidableRel G.Adj] {a₁ a₂ : α} {b : β} :
    ∀ (w : G.Walk a₁ a₂), (w.boxProdLeft H b).ofBoxProdLeft = w
  | nil => rfl
  | cons' x y z h w => by
    rw [Walk.boxProdLeft, map_cons, ofBoxProdLeft, Or.by_cases, dif_pos, ← Walk.boxProdLeft]
    · simp [ofBoxProdLeft_boxProdLeft]
    · exact ⟨h, rfl⟩

@[simp]
theorem ofBoxProdRight_boxProdRight [DecidableEq α] [DecidableRel G.Adj] {a b₁ b₂ : α} :
    ∀ (w : G.Walk b₁ b₂), (w.boxProdRight G a).ofBoxProdRight = w
  | nil => rfl
  | cons' x y z h w => by
    rw [Walk.boxProdRight, map_cons, ofBoxProdRight, Or.by_cases, dif_pos, ←
      Walk.boxProdRight]
    · simp [ofBoxProdRight_boxProdRight]
    · exact ⟨h, rfl⟩

lemma length_boxProd {a₁ a₂ : α} {b₁ b₂ : β} [DecidableEq α] [DecidableEq β]
    [DecidableRel G.Adj] [DecidableRel H.Adj] (w : (G □ H).Walk (a₁, b₁) (a₂, b₂)) :
    w.length = w.ofBoxProdLeft.length + w.ofBoxProdRight.length := by
  match w with
  | .nil => simp [ofBoxProdLeft, ofBoxProdRight]
  | .cons x w' => next c =>
    unfold ofBoxProdLeft ofBoxProdRight
    rw [length_cons, length_boxProd w']
    have disj : (G.Adj a₁ c.1 ∧ b₁ = c.2) ∨ (H.Adj b₁ c.2 ∧ a₁ = c.1) := by simp_all
    rcases disj with h₁ | h₂
    · simp only [h₁, and_self, ↓reduceDIte, length_cons, Or.by_cases]
      rw [add_comm, add_comm w'.ofBoxProdLeft.length 1, add_assoc]
      congr <;> simp [h₁.2.symm]
    · simp only [h₂, add_assoc, Or.by_cases]
      congr <;> simp [h₂.2.symm]

end Walk

variable {G H}

protected theorem Preconnected.boxProd (hG : G.Preconnected) (hH : H.Preconnected) :
    (G □ H).Preconnected := by
  rintro x y
  obtain ⟨w₁⟩ := hG x.1 y.1
  obtain ⟨w₂⟩ := hH x.2 y.2
  exact ⟨(w₁.boxProdLeft _ _).append (w₂.boxProdRight _ _)⟩

protected theorem Preconnected.ofBoxProdLeft [Nonempty β] (h : (G □ H).Preconnected) :
    G.Preconnected := by
  classical
  rintro a₁ a₂
  obtain ⟨w⟩ := h (a₁, Classical.arbitrary _) (a₂, Classical.arbitrary _)
  exact ⟨w.ofBoxProdLeft⟩

protected theorem Preconnected.ofBoxProdRight [Nonempty α] (h : (G □ H).Preconnected) :
    H.Preconnected := by
  classical
  rintro b₁ b₂
  obtain ⟨w⟩ := h (Classical.arbitrary _, b₁) (Classical.arbitrary _, b₂)
  exact ⟨w.ofBoxProdRight⟩

protected theorem Connected.boxProd (hG : G.Connected) (hH : H.Connected) : (G □ H).Connected := by
  haveI := hG.nonempty
  haveI := hH.nonempty
  exact ⟨hG.preconnected.boxProd hH.preconnected⟩

protected theorem Connected.ofBoxProdLeft (h : (G □ H).Connected) : G.Connected := by
  haveI := (nonempty_prod.1 h.nonempty).1
  haveI := (nonempty_prod.1 h.nonempty).2
  exact ⟨h.preconnected.ofBoxProdLeft⟩

protected theorem Connected.ofBoxProdRight (h : (G □ H).Connected) : H.Connected := by
  haveI := (nonempty_prod.1 h.nonempty).1
  haveI := (nonempty_prod.1 h.nonempty).2
  exact ⟨h.preconnected.ofBoxProdRight⟩

@[simp]
theorem connected_boxProd : (G □ H).Connected ↔ G.Connected ∧ H.Connected :=
  ⟨fun h => ⟨h.ofBoxProdLeft, h.ofBoxProdRight⟩, fun h => h.1.boxProd h.2⟩

@[deprecated (since := "2025-05-08")] alias boxProd_connected := connected_boxProd

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

theorem neighborFinset_boxProd (x : α × β)
    [Fintype (G.neighborSet x.1)] [Fintype (H.neighborSet x.2)] [Fintype ((G □ H).neighborSet x)] :
    (G □ H).neighborFinset x =
      (G.neighborFinset x.1 ×ˢ {x.2}).disjUnion ({x.1} ×ˢ H.neighborFinset x.2)
        (Finset.disjoint_product.mpr <| Or.inl <| neighborFinset_disjoint_singleton _ _) := by
  -- swap out the fintype instance for the canonical one
  letI : Fintype ((G □ H).neighborSet x) := SimpleGraph.boxProdFintypeNeighborSet _
  convert_to (G □ H).neighborFinset x = _ using 2
  exact Eq.trans (Finset.map_map _ _ _) Finset.attach_map_val

@[deprecated (since := "2025-05-08")] alias boxProd_neighborFinset := neighborFinset_boxProd

theorem degree_boxProd (x : α × β)
    [Fintype (G.neighborSet x.1)] [Fintype (H.neighborSet x.2)] [Fintype ((G □ H).neighborSet x)] :
    (G □ H).degree x = G.degree x.1 + H.degree x.2 := by
  rw [degree, degree, degree, neighborFinset_boxProd, Finset.card_disjUnion]
  simp_rw [Finset.card_product, Finset.card_singleton, mul_one, one_mul]

@[deprecated (since := "2025-05-08")] alias boxProd_degree := degree_boxProd

lemma reachable_boxProd {x y : α × β} :
    (G □ H).Reachable x y ↔ G.Reachable x.1 y.1 ∧ H.Reachable x.2 y.2 := by
  classical
  constructor
  · intro ⟨w⟩
    exact ⟨⟨w.ofBoxProdLeft⟩, ⟨w.ofBoxProdRight⟩⟩
  · intro ⟨⟨w₁⟩, ⟨w₂⟩⟩
    exact ⟨(w₁.boxProdLeft _ _).append (w₂.boxProdRight _ _)⟩

@[deprecated (since := "2025-05-08")] alias boxProd_reachable := reachable_boxProd

@[simp]
lemma edist_boxProd (x y : α × β) :
    (G □ H).edist x y = G.edist x.1 y.1 + H.edist x.2 y.2 := by
  classical
  -- The case `(G □ H).edist x y = ⊤` is used twice, so better to factor it out.
  have top_case : (G □ H).edist x y = ⊤ ↔ G.edist x.1 y.1 = ⊤ ∨ H.edist x.2 y.2 = ⊤ := by
    simp_rw [← not_ne_iff, edist_ne_top_iff_reachable, reachable_boxProd, not_and_or]
  by_cases h : (G □ H).edist x y = ⊤
  · rw [top_case] at h
    aesop
  · have rGH : G.edist x.1 y.1 ≠ ⊤ ∧ H.edist x.2 y.2 ≠ ⊤ := by rw [top_case] at h; aesop
    have ⟨wG, hwG⟩ := exists_walk_of_edist_ne_top rGH.1
    have ⟨wH, hwH⟩ := exists_walk_of_edist_ne_top rGH.2
    let w_app := (wG.boxProdLeft _ _).append (wH.boxProdRight _ _)
    have w_len : w_app.length = wG.length + wH.length := by
      unfold w_app Walk.boxProdLeft Walk.boxProdRight; simp
    refine le_antisymm ?_ ?_
    ·  calc (G □ H).edist x y ≤ w_app.length := by exact edist_le _
          _ = wG.length + wH.length := by exact_mod_cast w_len
          _ = G.edist x.1 y.1 + H.edist x.2 y.2 := by simp only [hwG, hwH]
    · have ⟨w, hw⟩ := exists_walk_of_edist_ne_top h
      rw [← hw, Walk.length_boxProd]
      exact add_le_add (edist_le w.ofBoxProdLeft) (edist_le w.ofBoxProdRight)

@[deprecated (since := "2025-05-08")] alias boxProd_edist := edist_boxProd

end SimpleGraph
